// Bounded-memory regression for id churn. Resource ids and task ids are
// monotone and never reused, so every container keyed by them must hold memory
// in proportion to its LIVE entries, not to the ids ever allocated. This test
// churns through ~200k task ids and ~600k resource ids (fired timers, cancelled
// timers, UDP sockets, plus a trickle of real TCP connections) with only a
// bounded number alive at any moment, and asserts that resident memory stops
// growing after warm-up. A container that is a window indexed by id (the old
// `Vec<Option<V>>` slab / vec-map and the `Vec<u8>` / `Vec<bool>` TLS flag
// tables) grows by tens of MB over this run; a map keyed by id does not.
//
// Kept in its own test binary: RSS is process-wide, so no other test may run
// concurrently in this process.

use lion_executor::{spawn, Runtime};
use lion_reactor::Duration;
use lion_utility::net::{TcpListener, TcpStream, UdpSocket};
use lion_utility::time::sleep;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

// Resident set size of this process, in KiB.
fn rss_kib() -> u64 {
  let status = std::fs::read_to_string("/proc/self/status").expect("read /proc/self/status");
  for line in status.lines() {
    if let Some(rest) = line.strip_prefix("VmRSS:") {
      return rest.trim().trim_end_matches("kB").trim().parse().expect("parse VmRSS");
    }
  }
  panic!("no VmRSS line in /proc/self/status");
}

// Polls the inner future exactly once, then drops it. Used to register a timer
// and cancel it before it fires (Sleep's Drop deregisters the timer).
struct PollOnceThenDrop<F: Future + Unpin>(Option<F>);

impl<F: Future + Unpin> Future for PollOnceThenDrop<F> {
  type Output = ();
  fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
    if let Some(mut f) = self.0.take() {
      let _ = Pin::new(&mut f).poll(cx);
    }
    Poll::Ready(())
  }
}

const BATCH: u64 = 1000;
const TCP_PER_BATCH: u64 = 5;

// One batch: BATCH fresh tasks, each firing one timer, cancelling one timer and
// opening/closing one UDP socket; plus TCP_PER_BATCH connect/echo/close cycles.
async fn run_batch(batch: u64, echo_addr: std::net::SocketAddr) {
  let mut joins = Vec::with_capacity(BATCH as usize);
  for i in 0..BATCH {
    let n = batch * BATCH + i;
    joins.push(spawn(async move {
      // Fired timer. Vary the duration so consecutive registrations do not all
      // share one deadline (the reactor's same-deadline fast path reuses a rid).
      sleep(Duration::from_millis(1 + n % 2)).await;
      // Cancelled timer: registered, then dropped long before its deadline.
      PollOnceThenDrop(Some(sleep(Duration::from_millis(10_000 + n % 1000)))).await;
      // I/O resource: register + deregister, one readiness entry each.
      let sock = UdpSocket::bind("127.0.0.1:0").await.expect("udp bind");
      drop(sock);
    }));
  }
  for i in 0..TCP_PER_BATCH {
    joins.push(spawn(async move {
      let mut s = TcpStream::connect(echo_addr).await.expect("tcp connect");
      let b = [(i as u8).wrapping_add(1)];
      s.write_all(&b).await.expect("tcp write");
      let mut r = [0u8; 1];
      s.read_exact(&mut r).await.expect("tcp read");
      assert_eq!(r, b);
    }));
  }
  for j in joins {
    j.await.expect("task join");
  }
}

#[test]
fn id_churn_keeps_memory_bounded() {
  let warmup_batches: u64 = std::env::var("LION_BOUNDED_WARMUP")
    .ok().and_then(|v| v.parse().ok()).unwrap_or(20);
  let batches: u64 = std::env::var("LION_BOUNDED_BATCHES")
    .ok().and_then(|v| v.parse().ok()).unwrap_or(200);
  // Growth allowed after warm-up. The id-window representation grows by tens
  // of MB over the default 200 batches; the id-keyed maps stay flat, leaving
  // only allocator noise and the TID ledger (1 bit per task id ever spawned).
  let limit_kib: u64 = std::env::var("LION_BOUNDED_LIMIT_KIB")
    .ok().and_then(|v| v.parse().ok()).unwrap_or(4096);

  let rt = Runtime::new().expect("runtime");
  rt.block_on(async move {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("tcp bind");
    let echo_addr = listener.local_addr().expect("local addr");
    spawn(async move {
      loop {
        let (mut s, _) = match listener.accept().await {
          Ok(v) => v,
          Err(_) => return,
        };
        spawn(async move {
          let mut b = [0u8; 1];
          if s.read_exact(&mut b).await.is_ok() {
            let _ = s.write_all(&b).await;
          }
        });
      }
    });

    for b in 0..warmup_batches {
      run_batch(b, echo_addr).await;
    }
    let before = rss_kib();
    let t0 = std::time::Instant::now();
    for b in warmup_batches..warmup_batches + batches {
      run_batch(b, echo_addr).await;
    }
    let after = rss_kib();
    let growth = after.saturating_sub(before);
    eprintln!(
      "bounded_memory: {} batches x {} tasks in {:.2?}; VmRSS {} KiB -> {} KiB (growth {} KiB, limit {} KiB)",
      batches, BATCH + TCP_PER_BATCH, t0.elapsed(), before, after, growth, limit_kib
    );
    assert!(
      growth <= limit_kib,
      "resident memory grew by {} KiB over {} batches of id churn (limit {} KiB): \
       some id-keyed container is holding memory for dead ids",
      growth, batches, limit_kib
    );
  });
}
