use lion_reactor::{Reactor as LionReactor, ReactorGuard as LionReactorGuard};
use super::{Duration, Instant};
use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub struct Reactor {
  inner: LionReactor,
}

#[verifier::external_body]
pub struct ReactorGuard {
  inner: LionReactorGuard,
}

impl Reactor {
  #[verifier::external_body]
  pub fn new(reactor: LionReactor) -> (result: Self)
  {
  Reactor { inner: reactor }
  }
}

} // end verus!

impl Reactor {
  pub(crate) fn enter(&mut self) -> ReactorGuard {
  ReactorGuard {
    inner: self.inner.enter(),
  }
  }

  pub(crate) fn park(&mut self, timeout: Option<Duration>) {
  self.inner.park(timeout.map(|d| d.into_reactor()));
  }

  pub(crate) fn next_deadline(&mut self) -> Option<Instant> {
  self.inner.next_deadline().map(Instant::from)
  }

  #[inline]
  pub(crate) fn flush_pending_deregister(&mut self) {
  self.inner.flush_pending_deregister();
  }
}
