// Foreign-thread wake latency. A task's waker woken from another thread goes
// through the runtime's cross-thread queue and interrupts the reactor park. The
// idle park is 100 ms, so a wake that only surfaced at the next park timeout
// would show up as tens of milliseconds of latency; an interrupted park shows
// well under a millisecond. Kept in its own test binary so no other test's
// threads compete for the CPU while it measures.

use lion_executor::{spawn, Runtime};
use lion_utility::time::timeout;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};
use std::time::{Duration, Instant};

#[derive(Default)]
struct Slot {
  woken: bool,
  waker: Option<Waker>,
}

// Pending until another thread sets `woken`; stores the task's waker for it.
struct WaitForSlot(Arc<Mutex<Slot>>);

impl Future for WaitForSlot {
  type Output = Instant;
  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Instant> {
    let mut slot = self.0.lock().unwrap();
    if slot.woken {
      Poll::Ready(Instant::now())
    } else {
      slot.waker = Some(cx.waker().clone());
      Poll::Pending
    }
  }
}

#[test]
fn foreign_thread_wake_interrupts_idle_park() {
  const TRIALS: usize = 8;
  const LIMIT: Duration = Duration::from_millis(25);
  let rt = Runtime::new().expect("runtime");
  let mut latencies = Vec::with_capacity(TRIALS);
  for trial in 0..TRIALS {
    let latency = rt.block_on(async move {
      let slot = Arc::new(Mutex::new(Slot::default()));
      let task = spawn(WaitForSlot(slot.clone()));
      // Let the runtime go idle and park, then wake the task from outside at a
      // point that lands somewhere inside a 100 ms park.
      let waker_thread = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(150 + 13 * trial as u64));
        let mut s = slot.lock().unwrap();
        s.woken = true;
        let waker = s.waker.take().expect("task parked without a waker");
        drop(s);
        let woke_at = Instant::now();
        waker.wake();
        woke_at
      });
      let polled_at = timeout(Duration::from_secs(5), task)
        .await
        .expect("woken task never ran")
        .expect("task failed");
      let woke_at = waker_thread.join().unwrap();
      polled_at.saturating_duration_since(woke_at)
    });
    latencies.push(latency);
  }
  let max = latencies.iter().max().copied().unwrap();
  eprintln!("foreign wake -> poll latencies: {:?}", latencies);
  assert!(
    max < LIMIT,
    "a foreign-thread wake took {:?} to reach its task (limit {:?}); the park was not interrupted",
    max,
    LIMIT
  );
}
