// lion_reactor::AsyncFd: readiness of a raw fd for tasks, over both the mio
// backend (real sockets and pipes) and the in-process mock backend (fake fds
// with injected, edge-triggered readiness). Every wait that could hang on a
// lost wakeup runs under a reactor-timer deadline, so a regression fails
// instead of wedging the test binary.

use lion_executor::os::mock::{MockBackend, MockOs};
use lion_executor::{spawn_local, Runtime, RuntimeBuilder};
use lion_reactor::os::RawFd;
use lion_reactor::{readiness, AsyncFd, Interest, IoResult, ReactorHandle, ResourceId, Source, Waker};
use lion_utility::time::{sleep, timeout};
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet, VecDeque};
use std::future::{poll_fn, Future};
use std::io::{self, ErrorKind, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::net::UnixStream;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll};
use std::time::Duration;

const LIMIT: Duration = Duration::from_secs(20);

fn mock_runtime() -> (Runtime, MockOs) {
  let (backend, os) = MockBackend::new();
  let rt = RuntimeBuilder::new().os_backend(Box::new(backend)).build().expect("runtime over the mock backend");
  (rt, os)
}

// Runs a test body under a reactor-timer deadline, so a lost wakeup anywhere in
// it fails the test instead of hanging it.
fn run<F: Future>(rt: &Runtime, body: F) -> F::Output {
  rt.block_on(async { timeout(LIMIT, body).await.expect("test body hung (a lost wakeup?)") })
}

fn socketpair() -> (UnixStream, UnixStream) {
  let (a, b) = UnixStream::pair().expect("socketpair");
  a.set_nonblocking(true).unwrap();
  b.set_nonblocking(true).unwrap();
  (a, b)
}

fn pattern(i: usize) -> u8 {
  (i.wrapping_mul(31) ^ (i >> 7)) as u8
}

async fn write_all_stream(fd: &AsyncFd, s: &UnixStream, mut data: &[u8]) {
  while !data.is_empty() {
    let n = fd.write_io(|_| { let mut w = s; w.write(data) }).await.expect("write");
    data = &data[n..];
  }
}

// ---------------------------------------------------------------------------
// Echo over a socketpair (mio backend).

#[test]
fn echo_over_a_socketpair() {
  let rt = Runtime::new().expect("runtime");
  run(&rt, async {
    let (a, b) = socketpair();
    let server = spawn_local(async move {
      let fd = AsyncFd::new(b.as_raw_fd()).unwrap();
      let mut buf = vec![0u8; 8192];
      let mut total = 0usize;
      loop {
        let n = fd.read_io(|_| (&b).read(&mut buf)).await.expect("server read");
        if n == 0 {
          return total;
        }
        total += n;
        write_all_stream(&fd, &b, &buf[..n]).await;
      }
    });
    let fd = AsyncFd::new(a.as_raw_fd()).unwrap();
    let mut sent = 0usize;
    for round in 0..300usize {
      let len = 1 + (round * 977) % 16384;
      let msg: Vec<u8> = (sent..sent + len).map(pattern).collect();
      write_all_stream(&fd, &a, &msg).await;
      let mut got = vec![0u8; len];
      let mut have = 0;
      while have < len {
        let n = timeout(LIMIT, fd.read_io(|_| (&a).read(&mut got[have..])))
          .await
          .expect("echo reply lost")
          .expect("client read");
        assert!(n > 0, "server closed early");
        have += n;
      }
      assert_eq!(got, msg, "round {round}");
      sent += len;
    }
    drop(fd);
    a.shutdown(std::net::Shutdown::Write).unwrap();
    assert_eq!(timeout(LIMIT, server).await.expect("server hung").unwrap(), sent);
  });
}

// ---------------------------------------------------------------------------
// In-memory sockets over the mock backend: a byte queue per fd with a small
// capacity, and the edges a real kernel would deliver (a write makes the
// peer's read side ready, a read makes the peer's write side ready, a close
// makes the peer's read side ready with read_closed).

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
    let mut inbound = HashMap::new();
    inbound.insert(a, VecDeque::new());
    inbound.insert(b, VecDeque::new());
    let peer = HashMap::from([(a, b), (b, a)]);
    Rc::new(FakeNet {
      os,
      cap,
      inbound: RefCell::new(inbound),
      peer,
      write_closed: RefCell::new(HashSet::new()),
      would_blocks: Cell::new(0),
    })
  }

  fn would_block(&self) -> io::Error {
    self.would_blocks.set(self.would_blocks.get() + 1);
    io::Error::from(ErrorKind::WouldBlock)
  }

  fn read(&self, fd: RawFd, buf: &mut [u8]) -> io::Result<usize> {
    let peer = self.peer[&fd];
    let mut inbound = self.inbound.borrow_mut();
    let q = inbound.get_mut(&fd).unwrap();
    if q.is_empty() {
      return if self.write_closed.borrow().contains(&peer) { Ok(0) } else { Err(self.would_block()) };
    }
    let n = buf.len().min(q.len());
    for (dst, src) in buf.iter_mut().zip(q.drain(..n)) {
      *dst = src;
    }
    // Room freed in fd's receive queue: the peer may write again.
    self.os.ready(peer, false, true);
    Ok(n)
  }

  fn write(&self, fd: RawFd, data: &[u8]) -> io::Result<usize> {
    let peer = self.peer[&fd];
    let mut inbound = self.inbound.borrow_mut();
    let q = inbound.get_mut(&peer).unwrap();
    let room = self.cap - q.len();
    if room == 0 {
      return Err(self.would_block());
    }
    let n = room.min(data.len());
    q.extend(&data[..n]);
    // Data arrived at the peer.
    self.os.ready(peer, true, false);
    Ok(n)
  }

  fn close_write(&self, fd: RawFd) {
    self.write_closed.borrow_mut().insert(fd);
    let peer = self.peer[&fd];
    self.os.event(peer, lion_reactor::OsEvent { readable: true, read_closed: true, ..Default::default() });
  }
}

#[test]
fn echo_over_the_mock_backend() {
  let (rt, os) = mock_runtime();
  let (client_fd, server_fd) = (1000, 1001);
  // 64-byte queues: every message blocks both directions many times.
  let net = FakeNet::pair(os.clone(), client_fd, server_fd, 64);
  let total: usize = (0..200usize).map(|r| 1 + (r * 131) % 700).sum();
  let net2 = net.clone();
  run(&rt, async move {
    let net = net2;
    let server = {
      let net = net.clone();
      spawn_local(async move {
        let fd = AsyncFd::new(server_fd).unwrap();
        let mut buf = [0u8; 100];
        let mut echoed = 0usize;
        loop {
          let n = fd.read_io(|f| net.read(f, &mut buf)).await.unwrap();
          if n == 0 {
            net.close_write(server_fd);
            return echoed;
          }
          let mut data = &buf[..n];
          while !data.is_empty() {
            let w = fd.write_io(|f| net.write(f, data)).await.unwrap();
            data = &data[w..];
          }
          echoed += n;
        }
      })
    };
    // One AsyncFd, a writer task and a reader task on it.
    let fd = Rc::new(AsyncFd::new(client_fd).unwrap());
    let writer = {
      let (net, fd) = (net.clone(), fd.clone());
      spawn_local(async move {
        let mut i = 0usize;
        for r in 0..200usize {
          let len = 1 + (r * 131) % 700;
          let msg: Vec<u8> = (i..i + len).map(pattern).collect();
          let mut data = &msg[..];
          while !data.is_empty() {
            let w = fd.write_io(|f| net.write(f, data)).await.unwrap();
            data = &data[w..];
          }
          i += len;
        }
        net.close_write(client_fd);
      })
    };
    let reader = {
      let (net, fd) = (net.clone(), fd.clone());
      spawn_local(async move {
        let mut got = 0usize;
        let mut buf = [0u8; 50];
        loop {
          let n = fd.read_io(|f| net.read(f, &mut buf)).await.unwrap();
          if n == 0 {
            return got;
          }
          for (k, b) in buf[..n].iter().enumerate() {
            assert_eq!(*b, pattern(got + k), "byte {}", got + k);
          }
          got += n;
        }
      })
    };
    timeout(LIMIT, writer).await.expect("writer hung").unwrap();
    assert_eq!(timeout(LIMIT, reader).await.expect("reader hung").unwrap(), total);
    assert_eq!(timeout(LIMIT, server).await.expect("server hung").unwrap(), total);
  });
  assert!(net.would_blocks.get() > 100, "the queues never filled: {}", net.would_blocks.get());
  assert_eq!(os.registered(), 0, "every AsyncFd deregistered on drop");
}

// ---------------------------------------------------------------------------
// HANG_FIXING_STORY.md story 1, deterministically on the mock backend. A
// non-blocking connect is modelled as an operation that would block until the
// connection completes; completion delivers exactly one writable edge, and an
// idle connected socket never delivers another. The old Connect::poll consumed
// that edge's flag on its second poll and the first write then waited forever.

fn tick_until(rt: &Runtime, done: &Cell<bool>, ticks: usize) -> bool {
  for _ in 0..ticks {
    if done.get() {
      return true;
    }
    rt.tick_with_timeout(Duration::from_millis(5));
  }
  done.get()
}

#[test]
fn story1_two_poll_connect_keeps_the_real_write_edge() {
  let (rt, os) = mock_runtime();
  let fd = 10;
  let connected = Rc::new(Cell::new(false));
  let connect_polls = Rc::new(Cell::new(0));
  let done = Rc::new(Cell::new(false));
  {
    let (connected, connect_polls, done) = (connected.clone(), connect_polls.clone(), done.clone());
    let _ = rt.handle().spawn_local(async move {
      let afd = AsyncFd::new(fd).unwrap();
      afd
        .write_io(|_| {
          connect_polls.set(connect_polls.get() + 1);
          if connected.get() { Ok(()) } else { Err(io::Error::from(ErrorKind::WouldBlock)) }
        })
        .await
        .unwrap();
      // The first write of a connected, idle socket: no further edge will come.
      assert_eq!(afd.write_io(|_| Ok(5usize)).await.unwrap(), 5);
      done.set(true);
    });
  }
  // Poll #1: the optimistic flag, "not connected" (WouldBlock), waker armed.
  assert!(!tick_until(&rt, &done, 3));
  assert_eq!(connect_polls.get(), 1);
  // The connection completes: the one real writable edge.
  connected.set(true);
  assert!(os.ready(fd, false, true));
  // Poll #2 sees the edge's flag and connects; the write must not wait.
  assert!(tick_until(&rt, &done, 50), "the first write waited for an edge that never comes");
  assert_eq!(connect_polls.get(), 2);
}

// The negative control built into the suite: the old Connect::poll pattern,
// over the raw readiness API, on the same edge sequence, hangs.
struct OldConnect {
  rid: ResourceId,
  connected: Rc<Cell<bool>>,
}

impl Future for OldConnect {
  type Output = ();
  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
    if readiness::is_writable(self.rid) {
      // The bug: the flag is consumed on every observation, before knowing
      // whether the edge that set it was the last one.
      readiness::clear_writable(self.rid);
      if self.connected.get() {
        return Poll::Ready(());
      }
    }
    ReactorHandle::new().set_waker(self.rid, Interest::WRITABLE, Waker::from_std(cx.waker().clone()));
    Poll::Pending
  }
}

struct RawWriteReady {
  rid: ResourceId,
}

impl Future for RawWriteReady {
  type Output = ();
  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
    if readiness::is_writable(self.rid) {
      return Poll::Ready(());
    }
    ReactorHandle::new().set_waker(self.rid, Interest::WRITABLE, Waker::from_std(cx.waker().clone()));
    Poll::Pending
  }
}

#[test]
fn story1_old_connect_pattern_hangs() {
  let (rt, os) = mock_runtime();
  let fd = 11;
  let connected = Rc::new(Cell::new(false));
  let done = Rc::new(Cell::new(false));
  {
    let (connected, done) = (connected.clone(), done.clone());
    let _ = rt.handle().spawn_local(async move {
      let mut source = Source::new(fd);
      let rid = match ReactorHandle::new().register_io_resource(&mut source, Interest::READABLE_WRITABLE) {
        IoResult::Ok(rid) => rid,
        IoResult::Err(e) => panic!("register: {e:?}"),
      };
      readiness::init_readiness(rid);
      OldConnect { rid, connected }.await;
      RawWriteReady { rid }.await;
      done.set(true);
      let _ = ReactorHandle::new().deregister_io_resource(rid, &mut source);
    });
  }
  assert!(!tick_until(&rt, &done, 3));
  connected.set(true);
  assert!(os.ready(fd, false, true));
  assert!(!tick_until(&rt, &done, 50), "the old pattern no longer hangs: the scenario lost its teeth");
}

// ---------------------------------------------------------------------------
// A reader task and a writer task on one fd (mio backend): each direction has
// its own waker, and both block repeatedly.

#[test]
fn concurrent_reader_and_writer_on_one_fd() {
  const TOTAL: usize = 8 << 20;
  let rt = Runtime::new().expect("runtime");
  run(&rt, async {
    let (a, b) = socketpair();
    let server = spawn_local(async move {
      let fd = AsyncFd::new(b.as_raw_fd()).unwrap();
      let mut buf = vec![0u8; 16384];
      loop {
        let n = fd.read_io(|_| (&b).read(&mut buf)).await.unwrap();
        if n == 0 {
          return;
        }
        write_all_stream(&fd, &b, &buf[..n]).await;
      }
    });
    let a = Rc::new(a);
    let fd = Rc::new(AsyncFd::new(a.as_raw_fd()).unwrap());
    let blocked = Rc::new([Cell::new(0u64), Cell::new(0u64)]);
    let writer = {
      let (a, fd, blocked) = (a.clone(), fd.clone(), blocked.clone());
      spawn_local(async move {
        let data: Vec<u8> = (0..TOTAL).map(pattern).collect();
        let mut off = 0;
        while off < TOTAL {
          let end = (off + 65536).min(TOTAL);
          let n = fd
            .write_io(|_| {
              let r = (&*a).write(&data[off..end]);
              if matches!(&r, Err(e) if e.kind() == ErrorKind::WouldBlock) {
                blocked[1].set(blocked[1].get() + 1);
              }
              r
            })
            .await
            .unwrap();
          off += n;
        }
        a.shutdown(std::net::Shutdown::Write).unwrap();
      })
    };
    let reader = {
      let (a, fd, blocked) = (a.clone(), fd.clone(), blocked.clone());
      spawn_local(async move {
        let mut buf = vec![0u8; 32768];
        let mut got = 0usize;
        loop {
          let n = fd
            .read_io(|_| {
              let r = (&*a).read(&mut buf);
              if matches!(&r, Err(e) if e.kind() == ErrorKind::WouldBlock) {
                blocked[0].set(blocked[0].get() + 1);
              }
              r
            })
            .await
            .unwrap();
          if n == 0 {
            return got;
          }
          for (k, byte) in buf[..n].iter().enumerate() {
            assert_eq!(*byte, pattern(got + k));
          }
          got += n;
        }
      })
    };
    timeout(LIMIT, writer).await.expect("writer hung").unwrap();
    assert_eq!(timeout(LIMIT, reader).await.expect("reader hung").unwrap(), TOTAL);
    timeout(LIMIT, server).await.expect("server hung").unwrap();
    assert!(blocked[0].get() > 0 && blocked[1].get() > 0, "both directions must have blocked: {:?}", [blocked[0].get(), blocked[1].get()]);
  });
}

// ---------------------------------------------------------------------------
// An event carrying only EPOLLERR (a full pipe whose reader closed) wakes the
// writer waiting for space; its write then fails with EPIPE.

#[test]
fn error_only_event_wakes_a_waiting_writer() {
  let rt = Runtime::new().expect("runtime");
  run(&rt, async {
    let (sender, receiver) = mio::unix::pipe::new().expect("pipe");
    let fd = AsyncFd::new(sender.as_raw_fd()).unwrap();
    let chunk = vec![7u8; 65536];
    // Fill the pipe until the write would block.
    loop {
      let guard = fd.writable().await.unwrap();
      match guard.try_io(|_| (&sender).write(&chunk)) {
        Ok(_) => continue,
        Err(e) if e.kind() == ErrorKind::WouldBlock => break,
        Err(e) => panic!("fill: {e}"),
      }
    }
    let closer = spawn_local(async move {
      sleep(Duration::from_millis(20)).await;
      drop(receiver);
    });
    let r = timeout(Duration::from_secs(5), fd.write_io(|_| (&sender).write(&chunk)))
      .await
      .expect("the writer was not woken by the error-only event");
    assert_eq!(r.unwrap_err().kind(), ErrorKind::BrokenPipe);
    closer.await.unwrap();
  });
}

// ---------------------------------------------------------------------------
// Drop deregisters the fd and frees its readiness entry; nothing outlives the
// AsyncFd, however many are made.

#[test]
fn drop_deregisters_and_frees_the_readiness_entry() {
  let (rt, os) = mock_runtime();
  run(&rt, async {
    for round in 0..100 {
      let fds: Vec<AsyncFd> = (0..1000).map(|i| AsyncFd::new(5000 + i).unwrap()).collect();
      assert_eq!(os.registered(), 1000, "round {round}");
      assert_eq!(readiness::live_entries(), 1000, "round {round}");
      drop(fds);
      assert_eq!(os.registered(), 0, "round {round}");
      assert_eq!(readiness::live_entries(), 0, "round {round}");
    }
  });
  let st = os.stats();
  assert_eq!((st.registers, st.deregisters), (100_000, 100_000));
}

// An AsyncFd that outlives its runtime: polling it fails instead of acting on
// another reactor's rid, and dropping it leaves the successor reactor alone
// (which numbers its rids from 1 again). The dead reactor's readiness table
// went with it.
#[test]
fn asyncfd_outliving_its_runtime_leaves_the_next_one_alone() {
  let (rt1, _os1) = mock_runtime();
  let stale = rt1.block_on(async { AsyncFd::new(5).unwrap() });
  assert_eq!(readiness::live_entries(), 1);
  drop(rt1);
  assert_eq!(readiness::live_entries(), 0, "the dead reactor's readiness entries went with it");

  let (rt2, os2) = mock_runtime();
  let os = os2.clone();
  rt2.block_on(async move {
    let os2 = os;
    let other = AsyncFd::new(6).unwrap();
    let r = poll_fn(|cx| Poll::Ready(stale.poll_read_ready(cx).map(|r| r.map(|g| g.fd())))).await;
    match r {
      Poll::Ready(Err(_)) => {}
      _ => panic!("a stale AsyncFd was usable under another reactor"),
    }
    drop(stale);
    assert!(os2.is_registered(6), "dropping the stale AsyncFd deregistered another reactor's resource");
    assert_eq!(os2.stats().deregisters, 0);
    assert_eq!(readiness::live_entries(), 1);
    drop(other);
  });
  assert_eq!(os2.registered(), 0);
}

#[test]
fn asyncfd_needs_a_reactor() {
  let e = AsyncFd::new(3).expect_err("AsyncFd::new outside a runtime");
  assert_eq!(e.kind(), ErrorKind::Other);
}

// Invariant 4: the waker stored is exactly the caller's `cx.waker()`, not the
// task's. A combinator that polls a sub-future with a waker of its own (here a
// bare counting waker, standing for select/join/FuturesUnordered's per-child
// wakers) is the one woken by the edge.
struct CountingWaker(std::sync::atomic::AtomicUsize);

impl std::task::Wake for CountingWaker {
  fn wake(self: std::sync::Arc<Self>) {
    self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
  }
  fn wake_by_ref(self: &std::sync::Arc<Self>) {
    self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
  }
}

#[test]
fn the_callers_waker_is_the_one_woken() {
  let (rt, os) = mock_runtime();
  run(&rt, async {
    let fd = AsyncFd::new(20).unwrap();
    let counter = std::sync::Arc::new(CountingWaker(std::sync::atomic::AtomicUsize::new(0)));
    let waker = std::task::Waker::from(counter.clone());
    let mut cx = Context::from_waker(&waker);
    // Consume the optimistic flag with a WouldBlock; the counting waker is armed.
    let first = fd.poll_read_io(&mut cx, |_| Err::<(), _>(io::Error::from(ErrorKind::WouldBlock)));
    assert!(first.is_pending());
    assert!(os.ready(20, true, false));
    // Let the runtime park and deliver the edge.
    sleep(Duration::from_millis(10)).await;
    assert_eq!(counter.0.load(std::sync::atomic::Ordering::SeqCst), 1, "the sub-future's waker was not the one woken");
    assert!(fd.poll_read_io(&mut cx, |_| Ok::<u8, io::Error>(1)).is_ready());
  });
}
