#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::reactor::{Reactor, ReactorGuard};
use std::cell::Cell;

thread_local! {
  static CURRENT_REACTOR: Cell<Option<*mut Reactor>> = const { Cell::new(None) };
}

impl Reactor {
  pub fn enter(&mut self) -> ReactorGuard {
    CURRENT_REACTOR.with(|r| {
      r.set(Some(self as *mut Reactor));
    });
    ReactorGuard { _private: () }
  }
}

impl Drop for ReactorGuard {
  fn drop(&mut self) {
    CURRENT_REACTOR.with(|r| {
      r.set(None);
    });
  }
}

pub(crate) fn with_current_reactor<F, R>(f: F) -> Option<R>
where
  F: FnOnce(&mut Reactor) -> R,
{
  CURRENT_REACTOR.with(|r| {
    let ptr = r.get();
    ptr.and_then(|ptr| unsafe { ptr.as_mut().map(f) })
  })
}
