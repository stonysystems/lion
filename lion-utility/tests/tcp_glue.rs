// Regressions for the tokio-shaped TCP glue (feature `mio`), now a shell over
// lion-net's stream: the audit of 2026-10-04 (SRPC docs/dev/lion-tcp-plan.md)
// found `try_io` ignoring its interest and `poll_read_ready` busy-waking.

use lion_executor::{spawn, Runtime};
use lion_reactor::{readiness, Interest};
use lion_utility::net::{OwnedReadHalf, OwnedWriteHalf, TcpListener, TcpStream, UdpSocket};
use lion_utility::time::timeout;
use std::future::poll_fn;
use std::io::{self, ErrorKind};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};
use std::time::Duration;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

struct Counter(AtomicUsize);
impl Wake for Counter {
  fn wake(self: Arc<Self>) {
    self.0.fetch_add(1, Ordering::SeqCst);
  }
  fn wake_by_ref(self: &Arc<Self>) {
    self.0.fetch_add(1, Ordering::SeqCst);
  }
}

async fn connected_pair() -> (TcpStream, TcpStream) {
  let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
  let addr = listener.local_addr().unwrap();
  let client = TcpStream::connect(addr).await.unwrap();
  let (server, _) = listener.accept().await.unwrap();
  (client, server)
}

// Audit item 1: `try_io(WRITABLE, ..)` that returns WouldBlock consumes the
// write readiness, not the read readiness.
#[test]
fn try_io_clears_the_direction_its_interest_names() {
  let rt = Runtime::new().unwrap();
  rt.block_on(async {
    let (client, _server) = connected_pair().await;
    let rid = client.resource_id();
    assert!(readiness::is_writable(rid));
    let r: io::Result<()> = client.try_io(Interest::WRITABLE, || Err(io::Error::from(ErrorKind::WouldBlock)));
    assert_eq!(r.unwrap_err().kind(), ErrorKind::WouldBlock);
    assert!(!readiness::is_writable(rid), "a write WouldBlock left the write readiness set");
    assert!(readiness::is_readable(rid), "a write WouldBlock cleared the read readiness");
    // Not writable now: try_io returns WouldBlock without running `f`.
    let ran = std::cell::Cell::new(false);
    let r: io::Result<()> = client.try_io(Interest::WRITABLE, || { ran.set(true); Ok(()) });
    assert_eq!(r.unwrap_err().kind(), ErrorKind::WouldBlock);
    assert!(!ran.get(), "try_io ran its operation without readiness");
    // A read on the read readiness runs (and a success leaves it set).
    let r: io::Result<u8> = client.try_io(Interest::READABLE, || Ok(7));
    assert_eq!(r.unwrap(), 7);
    assert!(readiness::is_readable(rid));
  });
}

// Audit item 2: `poll_read_ready` on a stream that is not readable registers
// the caller's waker and returns Pending without waking it; data wakes it.
#[test]
fn poll_read_ready_parks_instead_of_spinning() {
  let rt = Runtime::new().unwrap();
  rt.block_on(async {
    let (mut client, mut server) = connected_pair().await;
    // Consume the optimistic initial readiness the way a reader would.
    let r: io::Result<usize> = client.try_io(Interest::READABLE, || Err(io::Error::from(ErrorKind::WouldBlock)));
    assert!(r.is_err());
    let count = Arc::new(Counter(AtomicUsize::new(0)));
    let waker = Waker::from(count.clone());
    let mut cx = Context::from_waker(&waker);
    assert!(client.poll_read_ready(&mut cx).is_pending());
    assert_eq!(count.0.load(Ordering::SeqCst), 0, "poll_read_ready woke itself: a busy loop");
    server.write_all(b"x").await.unwrap();
    let woke = timeout(Duration::from_secs(10), poll_fn(|_cx| {
      if count.0.load(Ordering::SeqCst) > 0 { Poll::Ready(()) } else { _cx.waker().wake_by_ref(); Poll::Pending }
    }))
    .await;
    assert!(woke.is_ok(), "the read edge never woke the registered waker");
    assert!(client.poll_read_ready(&mut cx).is_ready());
  });
}

// Audit item 5: the stream, the listener, the split halves and the UDP socket
// are Send (and Sync where they were) with no `unsafe impl`, and the halves
// still work from `spawn`ed (Send) tasks.
#[test]
fn split_halves_are_send_and_echo() {
  fn assert_send<T: Send>() {}
  fn assert_send_sync<T: Send + Sync>() {}
  assert_send_sync::<TcpStream>();
  assert_send_sync::<TcpListener>();
  assert_send_sync::<UdpSocket>();
  assert_send::<OwnedReadHalf>();
  assert_send::<OwnedWriteHalf>();

  let rt = Runtime::new().unwrap();
  rt.block_on(async {
    let (client, server) = connected_pair().await;
    let (mut r, mut w) = server.into_split();
    let echo = spawn(async move {
      let mut buf = [0u8; 1024];
      loop {
        let n = r.read(&mut buf).await.unwrap();
        if n == 0 {
          return;
        }
        w.write_all(&buf[..n]).await.unwrap();
      }
    });
    let (mut cr, mut cw) = client.into_split();
    for i in 0..50u8 {
      let msg = [i; 100];
      cw.write_all(&msg).await.unwrap();
      let mut got = [0u8; 100];
      timeout(Duration::from_secs(10), cr.read_exact(&mut got)).await.expect("echo hung").unwrap();
      assert_eq!(got, msg);
    }
    cw.shutdown().await.unwrap();
    timeout(Duration::from_secs(10), echo).await.expect("echo task hung").unwrap();
  });
}
