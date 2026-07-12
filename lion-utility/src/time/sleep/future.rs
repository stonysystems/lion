// Thin trusted glue: wraps the verified SleepKernel as a real Future. This whole
// module is the genuine trust boundary (Pin/Waker, the real reactor calls, the
// system clock) — marked `verus::trusted` under Verus (like the reactor's own
// trusted leaves) and plain Rust under cargo. All invariant maintenance lives in
// the kernel (the verified `poll_step` / `drop_step`); this layer only performs
// the real reactor effects and feeds their results back.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use lion_reactor::{Duration, Instant, ReactorHandle, ResourceId, Waker, IoResult};
use crate::time::sleep::kernel::{SleepKernel, SleepAction};

pub struct Sleep {
  kernel: SleepKernel,
}

impl Sleep {
  pub fn new(deadline: Instant) -> Self {
    Sleep { kernel: SleepKernel::new(deadline.inner) }
  }

  pub fn until(deadline: Instant) -> Self {
    Self::new(deadline)
  }

  pub fn for_duration(duration: Duration) -> Self {
    Self::new(Instant::now() + duration)
  }

  pub fn deadline(&self) -> Instant {
    Instant { inner: self.kernel.deadline }
  }

  pub fn reset(&mut self, deadline: Instant) {
    if let Some(rid) = self.kernel.rid {
      ReactorHandle::new().deregister_timer(ResourceId(rid));
    }
    self.kernel.reset_step(deadline.inner);
  }
}

// Free functions mirroring the lion::time / tokio::time surface.
/// Sleeps until `duration` has elapsed.
///
/// # Panics
///
/// Polling the returned `Sleep` panics if the reactor refuses the timer
/// registration before the deadline (the kernel's `Fail` decision): with no
/// wake source, completing early or suspending forever would both be unsound.
/// This matches Tokio's time-driver failure semantics.
pub fn sleep(duration: impl Into<Duration>) -> Sleep {
  Sleep::for_duration(duration.into())
}

/// Sleeps until `deadline`. Same panic contract as [`sleep`].
pub fn sleep_until(deadline: Instant) -> Sleep {
  Sleep::until(deadline)
}

impl Future for Sleep {
  type Output = ();

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
    let this = self.get_mut();
    // Park-cycle cached clock (== wheel.elapsed == max logged timestamp):
    // avoids a clock_gettime per poll. Deciding against an older clock can
    // only delay completion by at most one reactor cycle — never early — and
    // `deadline > cached` implies register_timer's `deadline > elapsed`
    // precondition exactly. Falls back to the real clock before first park.
    let now = ReactorHandle::cached_now().unwrap_or_else(Instant::now);

    // Observe the real clock + register result; the kernel decides Suspend/Complete.
    let reg: Option<u64> = if now.inner >= this.kernel.deadline {
      None
    } else {
      let handle = ReactorHandle::new();
      if let Some(rid) = this.kernel.rid {
        handle.deregister_timer(ResourceId(rid));
      }
      let waker = Waker::from_std(cx.waker().clone());
      let deadline = Instant { inner: this.kernel.deadline };
      match handle.register_timer(deadline, waker) {
        IoResult::Ok(rid) => Some(rid.0),
        IoResult::Err(_) => None,
      }
    };

    match this.kernel.poll_step(now.inner, reg) {
      SleepAction::Suspend => Poll::Pending,
      SleepAction::Complete => Poll::Ready(()),
      // Deadline not reached but the reactor refused the timer registration:
      // there is no wake source, so neither Pending (lost wakeup) nor Ready
      // (early completion) is sound — matching Tokio's time-driver failure
      // semantics, panic.
      SleepAction::Fail => panic!("lion: reactor timer registration failed"),
    }
  }
}

impl Drop for Sleep {
  fn drop(&mut self) {
    if let Some(rid) = self.kernel.rid {
      ReactorHandle::new().deregister_timer(ResourceId(rid));
    }
    self.kernel.drop_step();
  }
}
