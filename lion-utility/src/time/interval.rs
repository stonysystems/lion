// Trusted combinator: a periodic timer built on the verified Sleep. Each tick is
// one verified Sleep; the verified interval_kernel owns the deadline ledger and
// proves it advances by exactly `period` per tick (strictly monotonic — no drift
// or regression). This layer performs the real Sleep in lockstep. Plain Rust /
// `verus::trusted`.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use super::interval_kernel::IntervalKernel;
use super::Sleep;
use lion_reactor::{Duration, Instant};
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct Interval {
  sleep: Sleep,
  ikern: IntervalKernel,
}

fn period_ticks(period: Duration) -> u64 {
  let n = period.as_millis();
  if n == 0 {
    1
  } else {
    n
  }
}

impl Interval {
  pub fn new(period: Duration) -> Self {
    Self::new_at(Instant::now() + period, period)
  }

  pub fn new_at(start: Instant, period: Duration) -> Self {
    // Tick unit: 1 tick = 1 ms. Instant.inner and Duration.as_millis() are both
    // milliseconds, so the instant<->tick conversion is exact (lossless); the
    // only adjustment is period_ticks clamping a zero period up to 1 tick.
    Self { sleep: Sleep::until(start), ikern: IntervalKernel::new(start.inner, period_ticks(period)) }
  }

  pub async fn tick(&mut self) -> Instant {
    std::future::poll_fn(|cx| self.poll_tick(cx)).await
  }

  pub fn poll_tick(&mut self, cx: &mut Context<'_>) -> Poll<Instant> {
    match Pin::new(&mut self.sleep).poll(cx) {
      Poll::Ready(()) => {
        let now = Instant::now();
        // The verified ledger decides the next deadline (first + fires*period,
        // proven drift-free); re-arm the Sleep to that ABSOLUTE deadline, not
        // to now() + period.
        let next = self.ikern.tick_step();
        self.sleep = Sleep::until(Instant { inner: next });
        Poll::Ready(now)
      }
      Poll::Pending => Poll::Pending,
    }
  }
}

pub fn interval(period: impl Into<Duration>) -> Interval {
  Interval::new(period.into())
}

pub fn interval_at(start: Instant, period: impl Into<Duration>) -> Interval {
  Interval::new_at(start, period.into())
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::task::Waker;

  // No-drift (F6): the armed deadline after n fires is first + n*period at tick
  // granularity, derived from the verified ledger — NOT now() + period. Fired
  // deadlines are placed in the past so each Sleep completes without touching
  // the reactor (now >= deadline never registers a timer).
  #[test]
  fn interval_third_deadline_is_first_plus_two_periods() {
    let _ = Instant::now(); // anchor the process clock
    std::thread::sleep(std::time::Duration::from_millis(10));
    let start = Instant { inner: 0 };
    let period = Duration::from_millis(1);
    let mut iv = interval_at(start, period);
    assert_eq!(iv.ikern.deadline, 0); // kernel initialized with the REAL start
    assert_eq!(iv.sleep.deadline().inner, 0);
    let mut cx = Context::from_waker(Waker::noop());
    assert!(iv.poll_tick(&mut cx).is_ready()); // fire 1 (deadline = 0)
    assert!(iv.poll_tick(&mut cx).is_ready()); // fire 2 (deadline = 1)
    // Wall-clock now is >= 10ms, but the third deadline must be exactly
    // first + 2*period — no accumulation from re-arming off now().
    assert_eq!(iv.ikern.deadline, 2);
    assert_eq!(iv.sleep.deadline().inner, 2);
  }
}
