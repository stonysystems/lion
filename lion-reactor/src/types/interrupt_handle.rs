use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use vstd::prelude::*;

pub struct InterruptHandleShared {
  waker: mio::Waker,
  notified: AtomicBool,
}

#[derive(Clone)]
pub struct InterruptHandleInner(pub Arc<InterruptHandleShared>);

impl InterruptHandleInner {
  pub fn new(waker: mio::Waker) -> Self {
    InterruptHandleInner(Arc::new(InterruptHandleShared {
      waker,
      notified: AtomicBool::new(false),
    }))
  }

  pub fn wake(&self) {
    if !self.0.notified.swap(true, Ordering::AcqRel) {
      self.0.waker.wake().expect("failed to wake reactor");
    }
  }

  pub fn reset(&self) {
    self.0.notified.store(false, Ordering::Release);
  }
}

verus! {

#[verifier::external_body]
pub struct InterruptHandle {
  pub(crate) inner: InterruptHandleInner,
}

impl View for InterruptHandle {
  type V = int;

  #[verifier::external_body]
  spec fn view(&self) -> int {
    unimplemented!()
  }
}

impl Clone for InterruptHandle {
  #[verifier::external_body]
  fn clone(&self) -> Self {
    InterruptHandle {
      inner: self.inner.clone(),
    }
  }
}

impl InterruptHandle {
  #[verifier::external_body]
  pub fn wake(&self) {
    self.inner.wake()
  }

  #[verifier::external_body]
  pub fn reset(&self) {
    self.inner.reset()
  }
}

}
