// Trusted combinator: races a future against the verified Sleep. The suspend
// decision is made by the verified timeout_kernel (poll_step), which proves
// timeout is Pending only when both sub-futures are Pending — so every Pending
// carries a wake source (the wrapped future's own, or the verified Sleep's
// timer). This layer only relays the two polls and follows the decision.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use super::timeout_kernel::{poll_step, TimeoutAction};
use super::Sleep;
use lion_reactor::Duration;
use std::fmt;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Elapsed;

impl fmt::Display for Elapsed {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "deadline has elapsed")
  }
}

impl std::error::Error for Elapsed {}

pub struct Timeout<F> {
  future: Pin<Box<F>>,
  sleep: Pin<Box<Sleep>>,
}

impl<F: Future> Future for Timeout<F> {
  type Output = Result<F::Output, Elapsed>;

  fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    // Observe both readiness bits; the verified kernel decides.
    let mut out = None;
    let fut_ready = match self.future.as_mut().poll(cx) {
      Poll::Ready(o) => {
        out = Some(o);
        true
      }
      Poll::Pending => false,
    };
    let sleep_ready =
      if fut_ready { false } else { matches!(self.sleep.as_mut().poll(cx), Poll::Ready(())) };
    match poll_step(fut_ready, sleep_ready) {
      TimeoutAction::ReadyOk => Poll::Ready(Ok(out.unwrap())),
      TimeoutAction::ReadyElapsed => Poll::Ready(Err(Elapsed)),
      TimeoutAction::Pending => Poll::Pending,
    }
  }
}

pub fn timeout<F: Future>(duration: impl Into<Duration>, future: F) -> Timeout<F> {
  Timeout {
    future: Box::pin(future),
    sleep: Box::pin(Sleep::for_duration(duration.into())),
  }
}
