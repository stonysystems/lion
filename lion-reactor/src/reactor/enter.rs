#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::reactor::{Reactor, ReactorGuard};
use std::cell::Cell;

thread_local! {
  static CURRENT_REACTOR: Cell<Option<*mut Reactor>> = const { Cell::new(None) };
}

impl Reactor {
  // Installs this reactor as the thread's current one. Entering while another
  // reactor is current replaces it; callers that must not (lion-executor's
  // Runtime) check `is_entered_on_current_thread` first.
  pub fn enter(&mut self) -> ReactorGuard {
    let ptr = self as *mut Reactor;
    CURRENT_REACTOR.with(|r| {
      r.set(Some(ptr));
    });
    ReactorGuard { reactor: ptr as usize }
  }

  /// Whether a reactor is entered on this thread.
  pub fn is_entered_on_current_thread() -> bool {
    CURRENT_REACTOR.try_with(|r| r.get().is_some()).unwrap_or(false)
  }
}

// Clears only what this guard installed: if a later `enter` replaced this
// reactor, the newer entry stays.
impl Drop for ReactorGuard {
  fn drop(&mut self) {
    let _ = CURRENT_REACTOR.try_with(|r| {
      if r.get().map(|p| p as usize) == Some(self.reactor) {
        r.set(None);
        crate::handle::clear_cached_now();
      }
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
