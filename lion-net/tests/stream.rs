// lion_net::{TcpStream, TcpListener}: the OS-free stream and listener over a
// raw fd, on a runtime with the mio backend and real loopback TCP sockets (the
// mock-backend cases are in tests/mock.rs).
// Socket syscalls come from a test `SocketOps` over std (the embedder's role),
// or from closures. Several tests poll by hand with a counting waker, to pin
// what a poll registers and whether it wakes itself.

use lion_executor::Runtime;
use lion_net::{SocketOps, TcpListener, TcpStream};
use lion_reactor::{readiness, RawFd};
use std::cell::Cell;
use std::future::poll_fn;
use std::io::{self, ErrorKind, Read, Write};
use std::mem::ManuallyDrop;
use std::net::{SocketAddr, TcpListener as StdListener, TcpStream as StdStream};
use std::os::fd::{AsRawFd, FromRawFd, IntoRawFd};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};
use std::time::{Duration, Instant};

// The embedder's syscalls, over std on borrowed fds.
struct StdOps;

fn borrowed_stream(fd: RawFd) -> ManuallyDrop<StdStream> {
  ManuallyDrop::new(unsafe { StdStream::from_raw_fd(fd) })
}

impl SocketOps for StdOps {
  fn recv(&self, fd: RawFd, buf: &mut [u8]) -> io::Result<usize> {
    let mut s = borrowed_stream(fd);
    s.read(buf)
  }
  fn send(&self, fd: RawFd, buf: &[u8]) -> io::Result<usize> {
    let mut s = borrowed_stream(fd);
    s.write(buf)
  }
  fn accept(&self, listener: RawFd) -> io::Result<RawFd> {
    let l = ManuallyDrop::new(unsafe { StdListener::from_raw_fd(listener) });
    let (s, _) = l.accept()?;
    s.set_nonblocking(true)?;
    Ok(s.into_raw_fd())
  }
}

// A waker that counts its wakes.
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

// Lets the runtime park once (processing io events) and come back.
async fn yield_once() {
  let mut yielded = false;
  poll_fn(|cx| {
    if yielded {
      Poll::Ready(())
    } else {
      yielded = true;
      cx.waker().wake_by_ref();
      Poll::Pending
    }
  })
  .await
}

// Drives the runtime from outside any task until `done` holds; false if it
// still does not after 20 s, so a lost wakeup fails the test instead of
// hanging it.
fn tick_until(rt: &Runtime, done: impl Fn() -> bool) -> bool {
  let deadline = Instant::now() + Duration::from_secs(20);
  while !done() {
    if Instant::now() >= deadline {
      return false;
    }
    rt.tick_with_timeout(Duration::from_millis(1));
  }
  true
}

// Parks until `done` holds, failing after a deadline instead of hanging.
async fn park_until(mut done: impl FnMut() -> bool) {
  let deadline = Instant::now() + Duration::from_secs(10);
  while !done() {
    assert!(Instant::now() < deadline, "condition never held (a lost wakeup?)");
    std::thread::sleep(Duration::from_millis(1));
    yield_once().await;
  }
}

fn tcp_pair() -> (StdStream, StdStream) {
  let l = StdListener::bind("127.0.0.1:0").unwrap();
  let a = StdStream::connect(l.local_addr().unwrap()).unwrap();
  let (b, _) = l.accept().unwrap();
  a.set_nonblocking(true).unwrap();
  b.set_nonblocking(true).unwrap();
  (a, b)
}

fn rid(s: &TcpStream) -> lion_reactor::ResourceId {
  s.resource_id().unwrap()
}

#[test]
fn echo_through_listener_and_streams_with_socket_ops() {
  let rt = Runtime::new().unwrap();
  let result = Rc::new(Cell::new(None::<(usize, usize)>));
  let out = result.clone();
  let _ = rt.handle().spawn_local(async move {
    let std_listener = StdListener::bind("127.0.0.1:0").unwrap();
    std_listener.set_nonblocking(true).unwrap();
    let addr: SocketAddr = std_listener.local_addr().unwrap();
    let mut listener = TcpListener::from_raw_fd(std_listener.as_raw_fd()).unwrap();

    let server = lion_executor::spawn_local(async move {
      let ops = StdOps;
      let fd = poll_fn(|cx| listener.poll_accept(cx, &ops)).await.expect("accept");
      let owned = unsafe { StdStream::from_raw_fd(fd) };
      // No Nagle: the echo writes in pieces, and Nagle plus delayed ACK would
      // add ~40 ms per round on loopback.
      owned.set_nodelay(true).unwrap();
      let mut s = TcpStream::from_raw_fd(owned.as_raw_fd()).unwrap();
      let mut buf = vec![0u8; 4096];
      let mut total = 0usize;
      loop {
        let n = poll_fn(|cx| s.poll_read(cx, &ops, &mut buf)).await.expect("server read");
        if n == 0 {
          break;
        }
        total += n;
        let mut off = 0;
        while off < n {
          off += poll_fn(|cx| s.poll_write(cx, &ops, &buf[off..n])).await.expect("server write");
        }
      }
      drop(s);
      drop(owned);
      drop(listener);
      drop(std_listener);
      total
    });

    let client_std = StdStream::connect(addr).unwrap();
    client_std.set_nonblocking(true).unwrap();
    client_std.set_nodelay(true).unwrap();
    let mut c = TcpStream::from_raw_fd(client_std.as_raw_fd()).unwrap();
    let ops = StdOps;
    let mut sent = 0usize;
    for round in 0..200usize {
      let len = 1 + (round * 977) % 20000;
      let msg: Vec<u8> = (0..len).map(|i| (i + round) as u8).collect();
      let mut off = 0;
      while off < len {
        off += poll_fn(|cx| c.poll_write(cx, &ops, &msg[off..])).await.expect("client write");
      }
      let mut got = vec![0u8; len];
      let mut have = 0;
      while have < len {
        let n = poll_fn(|cx| c.poll_read(cx, &ops, &mut got[have..])).await.expect("client read");
        assert!(n > 0, "server closed early");
        have += n;
      }
      assert_eq!(got, msg, "round {round}");
      sent += len;
    }
    client_std.shutdown(std::net::Shutdown::Write).unwrap();
    let echoed = server.await.unwrap();
    drop(c);
    out.set(Some((sent, echoed)));
  });
  assert!(tick_until(&rt, || result.get().is_some()), "the echo hung (a lost wakeup?)");
  let (sent, echoed) = result.get().unwrap();
  assert_eq!(echoed, sent);
}

// Audit item 1: a WouldBlock clears the readiness of the direction that saw
// it, and only that one.
#[test]
fn would_block_clears_only_its_own_direction() {
  let rt = Runtime::new().unwrap();
  rt.block_on(async {
    let (a, _b) = tcp_pair();
    let s = TcpStream::from_raw_fd(a.as_raw_fd()).unwrap();
    // Invariant 5: both directions start ready.
    assert!(readiness::is_readable(rid(&s)) && readiness::is_writable(rid(&s)));
    let r: io::Result<()> = s.try_write_io(|_| Err(io::Error::from(ErrorKind::WouldBlock)));
    assert_eq!(r.unwrap_err().kind(), ErrorKind::WouldBlock);
    assert!(!readiness::is_writable(rid(&s)), "write WouldBlock left the write flag set");
    assert!(readiness::is_readable(rid(&s)), "write WouldBlock cleared the read flag");
    let r: io::Result<()> = s.try_read_io(|_| Err(io::Error::from(ErrorKind::WouldBlock)));
    assert!(r.is_err());
    assert!(!readiness::is_readable(rid(&s)));
    // Not ready: try_*_io returns WouldBlock without running the operation.
    let ran = std::cell::Cell::new(false);
    let r: io::Result<()> = s.try_read_io(|_| { ran.set(true); Ok(()) });
    assert_eq!(r.unwrap_err().kind(), ErrorKind::WouldBlock);
    assert!(!ran.get());
  });
}

// Audit items 2 and 4: a poll that must wait registers the caller's waker and
// returns Pending without waking itself; the next edge wakes exactly that
// waker.
#[test]
fn a_wait_parks_on_the_callers_waker_and_does_not_spin() {
  let rt = Runtime::new().unwrap();
  rt.block_on(async {
    let (a, mut b) = tcp_pair();
    let mut s = TcpStream::from_raw_fd(a.as_raw_fd()).unwrap();
    let (count, waker) = counting_waker();
    let mut cx = Context::from_waker(&waker);
    let mut buf = [0u8; 64];
    let calls = std::cell::Cell::new(0u32);

    // Nothing to read: the optimistic first read returns WouldBlock, so the
    // kernel arms and the poll is Pending, with no self-wake.
    let polled = s.poll_read_with(&mut cx, |fd| { calls.set(calls.get() + 1); StdOps.recv(fd, &mut buf) });
    assert!(polled.is_pending());
    assert_eq!(calls.get(), 1);
    assert_eq!(count.0.load(Ordering::SeqCst), 0, "a Pending poll woke itself (busy loop)");

    // Not ready now: a second poll makes no syscall and stays parked.
    let polled = s.poll_read_with(&mut cx, |fd| { calls.set(calls.get() + 1); StdOps.recv(fd, &mut buf) });
    assert!(polled.is_pending());
    assert_eq!(calls.get(), 1, "a poll ran the operation without readiness");

    // poll_read_ready parks the same way.
    assert!(s.poll_read_ready(&mut cx).is_pending());
    assert_eq!(count.0.load(Ordering::SeqCst), 0, "poll_read_ready woke itself (busy loop)");

    // Data arrives: the park that sees the edge wakes the registered waker.
    b.write_all(b"hello").unwrap();
    park_until(|| count.0.load(Ordering::SeqCst) > 0).await;
    let n = match s.poll_read_with(&mut cx, |fd| StdOps.recv(fd, &mut buf)) {
      Poll::Ready(r) => r.unwrap(),
      Poll::Pending => panic!("woken but not readable"),
    };
    assert_eq!(&buf[..n], b"hello");
  });
}

// Audit item 3 (decided): a short read leaves the readiness set (invariant 2);
// the next poll's read returns WouldBlock, which clears it and arms.
#[test]
fn a_short_read_keeps_readiness_until_would_block() {
  let rt = Runtime::new().unwrap();
  rt.block_on(async {
    let (a, mut b) = tcp_pair();
    let mut s = TcpStream::from_raw_fd(a.as_raw_fd()).unwrap();
    b.write_all(&[7u8; 10]).unwrap();
    std::thread::sleep(Duration::from_millis(20));
    let (_count, waker) = counting_waker();
    let mut cx = Context::from_waker(&waker);
    let mut buf = [0u8; 100];
    match s.poll_read(&mut cx, &StdOps, &mut buf) {
      Poll::Ready(Ok(10)) => {}
      other => panic!("expected a 10-byte read, got {other:?}"),
    }
    assert!(readiness::is_readable(rid(&s)), "a short read cleared the read flag");
    assert!(s.poll_read(&mut cx, &StdOps, &mut buf).is_pending());
    assert!(!readiness::is_readable(rid(&s)), "WouldBlock left the read flag set");
  });
}

// Audit item 5: the stream is Send and Sync without `unsafe impl`, because
// misuse off its reactor's thread fails closed.
#[test]
fn stream_used_on_another_thread_fails_closed() {
  fn assert_send_sync<T: Send + Sync>() {}
  assert_send_sync::<TcpStream>();
  assert_send_sync::<TcpListener>();

  let rt = Runtime::new().unwrap();
  let (a, _b) = tcp_pair();
  let s = rt.block_on(async { TcpStream::from_raw_fd(a.as_raw_fd()).unwrap() });
  let a_fd = a.as_raw_fd();
  let moved = std::thread::spawn(move || {
    // Another thread with its own reactor: same rid numbering, different epoch.
    let rt2 = Runtime::new().unwrap();
    let mut s = s;
    let r = rt2.block_on(async {
      let (_c, waker) = counting_waker();
      let mut cx = Context::from_waker(&waker);
      let mut buf = [0u8; 8];
      let mine = TcpStream::from_raw_fd(a_fd); // rid 1 on this reactor too
      let r = s.poll_read_with(&mut cx, |fd| StdOps.recv(fd, &mut buf));
      drop(mine);
      r
    });
    (r, s)
  });
  let (r, s) = moved.join().unwrap();
  match r {
    Poll::Ready(Err(e)) => assert_eq!(e.kind(), ErrorKind::Other),
    other => panic!("a poll off the stream's reactor did not fail closed: {other:?}"),
  }
  rt.block_on(async move {
    let live = readiness::live_entries();
    drop(s);
    assert_eq!(readiness::live_entries(), live - 1, "drop on the owner thread deregisters");
  });
  drop(a);
}

// A stream or listener deregisters on drop, before the owner closes the fd.
#[test]
fn drop_deregisters() {
  let rt = Runtime::new().unwrap();
  rt.block_on(async {
    let before = readiness::live_entries();
    let (a, _b) = tcp_pair();
    let s = TcpStream::from_raw_fd(a.as_raw_fd()).unwrap();
    let l_std = StdListener::bind("127.0.0.1:0").unwrap();
    l_std.set_nonblocking(true).unwrap();
    let l = TcpListener::from_raw_fd(l_std.as_raw_fd()).unwrap();
    assert_eq!(readiness::live_entries(), before + 2);
    drop(s);
    drop(l);
    assert_eq!(readiness::live_entries(), before);
  });
}
