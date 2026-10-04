// lion_net::{TcpStream, TcpListener} over the in-process mock OS backend
// (lion_reactor::os::mock): fake fds whose readiness edges the test injects,
// so every edge, WouldBlock and wakeup below is deterministic. These are the
// mock-backend cases of lion-utility/tests/async_fd.rs, ported to the stream
// and listener (whose readiness is AsyncFd's), plus accept, use on the wrong
// thread and drop. The runtime is driven with `tick_with_timeout` from the
// test itself or, for tasks, until a flag is set; every loop is bounded, so a
// lost wakeup fails a test instead of hanging it.

use lion_executor::os::mock::{MockBackend, MockOs};
use lion_executor::{Runtime, RuntimeBuilder};
use lion_net::{SocketOps, TcpListener, TcpStream};
use lion_reactor::{readiness, OsEvent, RawFd, ResourceId};
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet, VecDeque};
use std::future::poll_fn;
use std::io::{self, ErrorKind};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};
use std::time::{Duration, Instant};

fn mock_runtime() -> (Runtime, MockOs) {
  let (backend, os) = MockBackend::new();
  let rt = RuntimeBuilder::new().os_backend(Box::new(backend)).build().expect("runtime over the mock backend");
  (rt, os)
}

// One park of the runtime (no task is runnable in the tests that call it), so
// the backend's pending events reach the readiness flags and wakers.
fn park(rt: &Runtime) {
  rt.tick_with_timeout(Duration::from_millis(5));
}

// Ticks until `done` holds; false if it still does not after 20 s.
fn tick_until(rt: &Runtime, done: &dyn Fn() -> bool) -> bool {
  let deadline = Instant::now() + Duration::from_secs(20);
  while !done() {
    if Instant::now() >= deadline {
      return false;
    }
    rt.tick_with_timeout(Duration::from_millis(1));
  }
  true
}

struct Counter(AtomicUsize);
impl Wake for Counter {
  fn wake(self: Arc<Self>) {
    self.0.fetch_add(1, Ordering::SeqCst);
  }
  fn wake_by_ref(self: &Arc<Self>) {
    self.0.fetch_add(1, Ordering::SeqCst);
  }
}

fn counting_waker() -> (Arc<Counter>, Waker) {
  let c = Arc::new(Counter(AtomicUsize::new(0)));
  (c.clone(), Waker::from(c))
}

fn count(c: &Arc<Counter>) -> usize {
  c.0.load(Ordering::SeqCst)
}

fn would_block<R>() -> io::Result<R> {
  Err(io::Error::from(ErrorKind::WouldBlock))
}

fn rid(s: &TcpStream) -> ResourceId {
  s.resource_id().expect("a live stream is registered")
}

// ---------------------------------------------------------------------------
// Per direction: a WouldBlock clears that direction's flag only, the caller's
// waker for that direction is the one registered, a poll that finds the flag
// clear runs nothing, and only an edge for the direction sets it and wakes its
// waker.

#[test]
fn each_direction_clears_waits_and_wakes_on_its_own() {
  let (rt, os) = mock_runtime();
  let fd = 100;
  let mut s = TcpStream::from_raw_fd(fd).unwrap();
  let r = rid(&s);
  assert!(os.is_registered(fd));
  assert!(readiness::is_readable(r) && readiness::is_writable(r), "both flags start set");

  let (reads, read_waker) = counting_waker();
  let (writes, write_waker) = counting_waker();
  let mut rcx = Context::from_waker(&read_waker);
  let mut wcx = Context::from_waker(&write_waker);
  let ran = Cell::new(0u32);

  // The write would block: Pending, the write flag cleared, the read flag not.
  let polled: Poll<io::Result<()>> = s.poll_write_with(&mut wcx, |_| { ran.set(ran.get() + 1); would_block() });
  assert!(polled.is_pending());
  assert_eq!(ran.get(), 1);
  assert!(!readiness::is_writable(r), "a write WouldBlock left the write flag set");
  assert!(readiness::is_readable(r), "a write WouldBlock cleared the read flag");
  assert_eq!((count(&reads), count(&writes)), (0, 0), "a Pending poll woke a waker");

  // A read still completes, and a success leaves the read flag set.
  match s.poll_read_with(&mut rcx, |_| { ran.set(ran.get() + 1); Ok(5usize) }) {
    Poll::Ready(Ok(5)) => {}
    other => panic!("expected a 5-byte read, got {other:?}"),
  }
  assert!(readiness::is_readable(r), "a successful read cleared the read flag");

  // With the write flag clear, a write poll runs nothing and stays parked.
  let polled: Poll<io::Result<()>> = s.poll_write_with(&mut wcx, |_| { ran.set(ran.get() + 1); Ok(()) });
  assert!(polled.is_pending());
  assert_eq!(ran.get(), 2, "a poll ran the operation without readiness");

  // The read side now waits too.
  let polled: Poll<io::Result<()>> = s.poll_read_with(&mut rcx, |_| would_block());
  assert!(polled.is_pending());
  assert!(!readiness::is_readable(r));

  // A read edge sets the read flag and wakes the reader only.
  assert!(os.ready(fd, true, false));
  park(&rt);
  assert!(readiness::is_readable(r) && !readiness::is_writable(r));
  assert_eq!((count(&reads), count(&writes)), (1, 0), "a read edge woke the wrong waker");

  // A write edge sets the write flag and wakes the writer only.
  assert!(os.ready(fd, false, true));
  park(&rt);
  assert!(readiness::is_writable(r));
  assert_eq!((count(&reads), count(&writes)), (1, 1), "a write edge woke the wrong waker");
  match s.poll_write_with(&mut wcx, |_| Ok(3usize)) {
    Poll::Ready(Ok(3)) => {}
    other => panic!("expected a 3-byte write, got {other:?}"),
  }

  // poll_*_ready waits the same way and, ready, runs nothing.
  let polled: Poll<io::Result<()>> = s.poll_read_with(&mut rcx, |_| would_block());
  assert!(polled.is_pending());
  assert!(s.poll_read_ready(&mut rcx).is_pending());
  assert!(matches!(s.poll_write_ready(&mut wcx), Poll::Ready(Ok(()))));
  assert!(os.ready(fd, true, false));
  park(&rt);
  assert_eq!(count(&reads), 2);
  assert!(matches!(s.poll_read_ready(&mut rcx), Poll::Ready(Ok(()))));

  // try_*_io: the same clearing, no waker and no kernel step.
  let r2: io::Result<()> = s.try_write_io(|_| would_block());
  assert_eq!(r2.unwrap_err().kind(), ErrorKind::WouldBlock);
  assert!(!readiness::is_writable(r) && readiness::is_readable(r));
  let r3: io::Result<()> = s.try_write_io(|_| { ran.set(ran.get() + 100); Ok(()) });
  assert_eq!(r3.unwrap_err().kind(), ErrorKind::WouldBlock, "try_write_io ran without readiness");
  assert!(ran.get() < 100);
  drop(s);
  drop(rt);
}

// ---------------------------------------------------------------------------
// HANG_FIXING_STORY.md story 1 on the stream: a non-blocking connect is a
// write operation that would block until the connection completes, which
// delivers exactly one writable edge; an idle connected socket sends no other.
// The connect's success must leave that edge's readiness for the first write.

#[test]
fn story1_the_connect_edge_is_kept_for_the_first_write() {
  let (rt, os) = mock_runtime();
  let fd = 110;
  let mut s = TcpStream::from_raw_fd(fd).unwrap();
  let (wakes, waker) = counting_waker();
  let mut cx = Context::from_waker(&waker);
  let connected = Cell::new(false);
  let connect = |_: RawFd| -> io::Result<()> { if connected.get() { Ok(()) } else { would_block() } };

  // Poll #1: the optimistic flag, "not connected yet", armed.
  assert!(s.poll_write_with(&mut cx, connect).is_pending());
  // The connection completes: the one writable edge.
  connected.set(true);
  assert!(os.ready(fd, false, true));
  park(&rt);
  assert_eq!(count(&wakes), 1);
  // Poll #2 connects.
  assert!(matches!(s.poll_write_with(&mut cx, connect), Poll::Ready(Ok(()))));
  // The first write must not wait for an edge that never comes.
  match s.poll_write_with(&mut cx, |_| Ok(5usize)) {
    Poll::Ready(Ok(5)) => {}
    other => panic!("the first write waited after the connect consumed its edge: {other:?}"),
  }
  drop(s);
  drop(rt);
}

// ---------------------------------------------------------------------------
// In-memory sockets: a byte queue per fd with a small capacity, delivering the
// edges a kernel would (a write makes the peer readable, a read makes the peer
// writable, a close makes the peer readable with read_closed). Implements
// SocketOps, so the stream's generic `poll_read`/`poll_write` are exercised
// with a non-zero-sized implementation.

struct FakeNet {
  os: MockOs,
  cap: usize,
  inbound: RefCell<HashMap<RawFd, VecDeque<u8>>>,
  peer: HashMap<RawFd, RawFd>,
  write_closed: RefCell<HashSet<RawFd>>,
  would_blocks: Cell<u64>,
}

impl FakeNet {
  fn pair(os: MockOs, a: RawFd, b: RawFd, cap: usize) -> Rc<FakeNet> {
    let inbound = HashMap::from([(a, VecDeque::new()), (b, VecDeque::new())]);
    Rc::new(FakeNet {
      os,
      cap,
      inbound: RefCell::new(inbound),
      peer: HashMap::from([(a, b), (b, a)]),
      write_closed: RefCell::new(HashSet::new()),
      would_blocks: Cell::new(0),
    })
  }

  fn blocked(&self) -> io::Error {
    self.would_blocks.set(self.would_blocks.get() + 1);
    io::Error::from(ErrorKind::WouldBlock)
  }

  fn close_write(&self, fd: RawFd) {
    self.write_closed.borrow_mut().insert(fd);
    let peer = self.peer[&fd];
    self.os.event(peer, OsEvent { readable: true, read_closed: true, ..Default::default() });
  }
}

impl SocketOps for FakeNet {
  fn recv(&self, fd: RawFd, buf: &mut [u8]) -> io::Result<usize> {
    let peer = self.peer[&fd];
    let mut inbound = self.inbound.borrow_mut();
    let q = inbound.get_mut(&fd).unwrap();
    if q.is_empty() {
      return if self.write_closed.borrow().contains(&peer) { Ok(0) } else { Err(self.blocked()) };
    }
    let n = buf.len().min(q.len());
    for (dst, src) in buf.iter_mut().zip(q.drain(..n)) {
      *dst = src;
    }
    self.os.ready(peer, false, true);
    Ok(n)
  }

  fn send(&self, fd: RawFd, data: &[u8]) -> io::Result<usize> {
    let peer = self.peer[&fd];
    let mut inbound = self.inbound.borrow_mut();
    let q = inbound.get_mut(&peer).unwrap();
    let room = self.cap - q.len();
    if room == 0 {
      return Err(self.blocked());
    }
    let n = room.min(data.len());
    q.extend(&data[..n]);
    self.os.ready(peer, true, false);
    Ok(n)
  }

  fn accept(&self, _listener: RawFd) -> io::Result<RawFd> {
    Err(io::Error::from(ErrorKind::Unsupported))
  }
}

fn pattern(i: usize) -> u8 {
  (i.wrapping_mul(31) ^ (i >> 7)) as u8
}

// A reader task and a writer task share one stream (through an Rc<RefCell>,
// borrowed only within a poll) while an echo task serves the peer fd. With
// 64-byte queues every message blocks both directions many times, so each
// direction's waits and wakes must stay apart.
#[test]
fn reader_and_writer_tasks_share_one_stream() {
  let (rt, os) = mock_runtime();
  let (client_fd, server_fd) = (1000, 1001);
  let net = FakeNet::pair(os.clone(), client_fd, server_fd, 64);
  let total: usize = (0..200usize).map(|r| 1 + (r * 131) % 700).sum();
  let echoed = Rc::new(Cell::new(None::<usize>));
  let got = Rc::new(Cell::new(None::<usize>));
  let wrote = Rc::new(Cell::new(false));

  {
    let (net, echoed) = (net.clone(), echoed.clone());
    let _ = rt.handle().spawn_local(async move {
      let mut s = TcpStream::from_raw_fd(server_fd).unwrap();
      let mut buf = [0u8; 100];
      let mut n_echoed = 0usize;
      loop {
        let n = poll_fn(|cx| s.poll_read(cx, &*net, &mut buf)).await.unwrap();
        if n == 0 {
          net.close_write(server_fd);
          break;
        }
        let mut off = 0;
        while off < n {
          off += poll_fn(|cx| s.poll_write(cx, &*net, &buf[off..n])).await.unwrap();
        }
        n_echoed += n;
      }
      drop(s);
      echoed.set(Some(n_echoed));
    });
  }
  let client = Rc::new(RefCell::new(Some(TcpStream::from_raw_fd(client_fd).unwrap())));
  {
    let (net, client, wrote) = (net.clone(), client.clone(), wrote.clone());
    let _ = rt.handle().spawn_local(async move {
      let mut i = 0usize;
      for r in 0..200usize {
        let len = 1 + (r * 131) % 700;
        let msg: Vec<u8> = (i..i + len).map(pattern).collect();
        let mut off = 0;
        while off < len {
          off += poll_fn(|cx| client.borrow_mut().as_mut().unwrap().poll_write(cx, &*net, &msg[off..])).await.unwrap();
        }
        i += len;
      }
      net.close_write(client_fd);
      wrote.set(true);
    });
  }
  {
    let (net, client, got) = (net.clone(), client.clone(), got.clone());
    let _ = rt.handle().spawn_local(async move {
      let mut have = 0usize;
      let mut buf = [0u8; 50];
      loop {
        let n = poll_fn(|cx| client.borrow_mut().as_mut().unwrap().poll_read(cx, &*net, &mut buf)).await.unwrap();
        if n == 0 {
          break;
        }
        for (k, b) in buf[..n].iter().enumerate() {
          assert_eq!(*b, pattern(have + k), "byte {}", have + k);
        }
        have += n;
      }
      got.set(Some(have));
    });
  }
  let done = || wrote.get() && got.get().is_some() && echoed.get().is_some();
  assert!(tick_until(&rt, &done), "the echo hung: wrote={} got={:?} echoed={:?}", wrote.get(), got.get(), echoed.get());
  assert_eq!(got.get(), Some(total));
  assert_eq!(echoed.get(), Some(total));
  assert!(net.would_blocks.get() > 100, "the queues never filled: {}", net.would_blocks.get());
  drop(client.borrow_mut().take());
  assert_eq!(os.registered(), 0, "every stream deregistered on drop");
  drop(rt);
}

// ---------------------------------------------------------------------------
// Accept: a listener's accept waits for the listener's read edge. A
// WouldBlock clears the read flag and arms; with the flag clear nothing runs;
// the edge for a new connection wakes the waiter; a completed accept leaves
// the flag set, so the next accept runs and finds out.

#[test]
fn accept_waits_for_the_listeners_read_edge() {
  struct Backlog(RefCell<VecDeque<RawFd>>, Cell<u32>);
  impl SocketOps for Backlog {
    fn recv(&self, _: RawFd, _: &mut [u8]) -> io::Result<usize> {
      Err(io::Error::from(ErrorKind::Unsupported))
    }
    fn send(&self, _: RawFd, _: &[u8]) -> io::Result<usize> {
      Err(io::Error::from(ErrorKind::Unsupported))
    }
    fn accept(&self, _listener: RawFd) -> io::Result<RawFd> {
      self.1.set(self.1.get() + 1);
      self.0.borrow_mut().pop_front().ok_or_else(|| io::Error::from(ErrorKind::WouldBlock))
    }
  }

  let (rt, os) = mock_runtime();
  let lfd = 200;
  let mut l = TcpListener::from_raw_fd(lfd).unwrap();
  let lrid = l.resource_id().unwrap();
  let backlog = Backlog(RefCell::new(VecDeque::new()), Cell::new(0));
  let (wakes, waker) = counting_waker();
  let mut cx = Context::from_waker(&waker);

  // Nothing queued: the optimistic accept would block, which arms.
  assert!(l.poll_accept(&mut cx, &backlog).is_pending());
  assert_eq!(backlog.1.get(), 1);
  assert!(!readiness::is_readable(lrid));
  assert!(readiness::is_writable(lrid), "an accept WouldBlock cleared the write flag");
  // Not readable: a poll runs no accept.
  assert!(l.poll_accept(&mut cx, &backlog).is_pending());
  assert_eq!(backlog.1.get(), 1, "an accept ran without readiness");
  assert_eq!(count(&wakes), 0);

  // Two connections arrive with one edge.
  backlog.0.borrow_mut().extend([201, 202]);
  assert!(os.ready(lfd, true, false));
  park(&rt);
  assert_eq!(count(&wakes), 1, "the listener's edge did not wake the accept");
  assert!(matches!(l.poll_accept(&mut cx, &backlog), Poll::Ready(Ok(201))));
  assert!(readiness::is_readable(lrid), "a completed accept cleared the read flag");
  // The closure form, on the readiness the first accept left.
  assert!(matches!(l.poll_accept_with(&mut cx, |fd| backlog.accept(fd)), Poll::Ready(Ok(202))));
  assert!(l.poll_accept(&mut cx, &backlog).is_pending());
  assert_eq!(backlog.1.get(), 4);
  assert!(!readiness::is_readable(lrid));

  // An accepted connection becomes a stream of its own.
  let s = TcpStream::from_raw_fd(201).unwrap();
  assert!(os.is_registered(201));
  drop(s);
  drop(l);
  assert_eq!(os.registered(), 0);
  drop(rt);
}

// ---------------------------------------------------------------------------
// The stream and listener are Send and Sync with no `unsafe impl` (their only
// per-thread state is AsyncFd's, which checks the reactor on every use).
// Moved to another thread whose reactor numbers its rids from 1 again, a
// stream fails closed: its poll errs without running the operation and
// without arming, and its drop leaves that reactor's resource of the same rid
// alone. The registration stays with its own reactor.

#[test]
fn a_stream_moved_to_another_thread_fails_closed() {
  fn assert_send_sync<T: Send + Sync>() {}
  assert_send_sync::<TcpStream>();
  assert_send_sync::<TcpListener>();

  let (rt1, os1) = mock_runtime();
  let moved = TcpStream::from_raw_fd(300).unwrap();
  let moved_listener = TcpListener::from_raw_fd(301).unwrap();
  let moved_rid = rid(&moved);
  let other = std::thread::spawn(move || {
    let (rt2, os2) = mock_runtime();
    let (mut moved, mut moved_listener) = (moved, moved_listener);
    let own = TcpStream::from_raw_fd(310).unwrap();
    assert_eq!(rid(&own), moved_rid, "the scenario needs the two reactors' rids to collide");
    let (wakes, waker) = counting_waker();
    let mut cx = Context::from_waker(&waker);
    let ran = Cell::new(false);
    match moved.poll_read_with(&mut cx, |_| { ran.set(true); Ok(1usize) }) {
      Poll::Ready(Err(e)) => assert_eq!(e.kind(), ErrorKind::Other),
      other => panic!("a moved stream was usable under another thread's reactor: {other:?}"),
    }
    assert!(!ran.get(), "a moved stream ran its operation");
    assert!(matches!(moved.poll_write_ready(&mut cx), Poll::Ready(Err(_))));
    let r: io::Result<()> = moved.try_read_io(|_| { ran.set(true); Ok(()) });
    assert!(r.is_err() && !ran.get());
    assert!(matches!(moved_listener.poll_accept_with(&mut cx, |_| { ran.set(true); Ok(1) }), Poll::Ready(Err(_))));
    assert!(!ran.get());
    drop(moved);
    drop(moved_listener);
    assert!(os2.is_registered(310), "dropping the moved stream deregistered this reactor's resource");
    assert_eq!(os2.stats().deregisters, 0);
    assert!(readiness::is_readable(rid(&own)), "the moved stream touched this reactor's flags");
    // Nothing was armed for the moved stream: an edge on this reactor's own
    // resource does not wake its waker.
    assert!(os2.ready(310, true, true));
    park(&rt2);
    assert_eq!(count(&wakes), 0);
    drop(own);
    os2.registered()
  });
  assert_eq!(other.join().unwrap(), 0);
  assert!(os1.is_registered(300) && os1.is_registered(301), "the moved registrations are their own reactor's to release");
  assert_eq!(os1.stats().deregisters, 0);
  drop(rt1);
}

// ---------------------------------------------------------------------------
// Drop: a stream or listener deregisters its fd within its drop, on its own
// reactor, before the owner (which keeps the fd open until then) closes it,
// and frees its readiness entry; nothing outlives it, however many are made.
// (The verified kernel's drop_step, which only records the deregistration in
// the ghost log, runs after it in the same drop; that order is the explicit
// `take()` in IoResource's Drop, which no runtime observation can see.)

#[test]
fn drop_deregisters_on_its_own_reactor() {
  let (rt, os) = mock_runtime();
  for round in 0..50 {
    let streams: Vec<TcpStream> = (0..500).map(|i| TcpStream::from_raw_fd(5000 + i).unwrap()).collect();
    let listeners: Vec<TcpListener> = (0..500).map(|i| TcpListener::from_raw_fd(6000 + i).unwrap()).collect();
    assert_eq!(os.registered(), 1000, "round {round}");
    assert_eq!(readiness::live_entries(), 1000, "round {round}");
    let before = os.stats().deregisters;
    drop(streams);
    assert_eq!(os.stats().deregisters, before + 500, "round {round}");
    assert!(!os.is_registered(5000), "round {round}");
    drop(listeners);
    assert_eq!(os.registered(), 0, "round {round}");
    assert_eq!(readiness::live_entries(), 0, "round {round}");
  }
  let st = os.stats();
  assert_eq!((st.registers, st.deregisters), (50_000, 50_000));
  drop(rt);
}

// A stream that outlives its runtime: a poll fails instead of acting on the
// next reactor's resource with the same rid, and its drop leaves that reactor
// alone (the dead reactor's readiness went with it).
#[test]
fn a_stream_outliving_its_runtime_leaves_the_next_one_alone() {
  let (rt1, _os1) = mock_runtime();
  let mut stale = TcpStream::from_raw_fd(7).unwrap();
  assert_eq!(readiness::live_entries(), 1);
  drop(rt1);
  assert_eq!(readiness::live_entries(), 0, "the dead reactor's readiness entries went with it");

  let (rt2, os2) = mock_runtime();
  let other = TcpStream::from_raw_fd(8).unwrap();
  assert_eq!(rid(&other), rid(&stale), "the scenario needs the two reactors' rids to collide");
  let (_wakes, waker) = counting_waker();
  let mut cx = Context::from_waker(&waker);
  assert!(matches!(stale.poll_write_with(&mut cx, |_| Ok(1usize)), Poll::Ready(Err(_))), "a stale stream was usable under the next reactor");
  drop(stale);
  assert!(os2.is_registered(8), "dropping the stale stream deregistered the next reactor's resource");
  assert_eq!(os2.stats().deregisters, 0);
  assert_eq!(readiness::live_entries(), 1);
  drop(other);
  assert_eq!(os2.registered(), 0);
  drop(rt2);
}

#[test]
fn a_stream_needs_a_reactor() {
  let e = TcpStream::from_raw_fd(3).expect_err("TcpStream::from_raw_fd outside a runtime");
  assert_eq!(e.kind(), ErrorKind::Other);
  let e = TcpListener::from_raw_fd(3).expect_err("TcpListener::from_raw_fd outside a runtime");
  assert_eq!(e.kind(), ErrorKind::Other);
}
