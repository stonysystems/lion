// Trusted glue: watch (single value + version; receivers wake on change). The
// wake protocol is the verified WaiterKernel (receiver parks → PassWaker; a send
// drains the queue waking every parked receiver → one WakeWaker each, the
// notify_waiters shape). value/version + drop flag are data-glue. verus::trusted
// under Verus, plain Rust under cargo.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::sync::waiter::kernel::{SignalAction, WaitAction, WaiterKernel};
use crate::sync::watch_kernel::WatchKernel;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};

struct WatchInner<T> {
  rx_kernel: WaiterKernel,
  value: T,
  wkern: WatchKernel,
  waiters: Vec<(u64, Waker)>,
  tx_dropped: bool,
  next_id: u64,
}

pub struct Sender<T> {
  inner: Arc<Mutex<WatchInner<T>>>,
}

pub struct Receiver<T> {
  inner: Arc<Mutex<WatchInner<T>>>,
  seen_version: u64,
}

#[derive(Debug)]
pub struct RecvError;

impl std::fmt::Display for RecvError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "channel closed")
  }
}

impl std::error::Error for RecvError {}

pub fn channel<T>(init: T) -> (Sender<T>, Receiver<T>) {
  let inner = Arc::new(Mutex::new(WatchInner {
    rx_kernel: WaiterKernel::new(),
    value: init,
    wkern: WatchKernel::new(),
    waiters: Vec::new(),
    tx_dropped: false,
    next_id: 0,
  }));
  (Sender { inner: inner.clone() }, Receiver { inner, seen_version: 1 })
}

// Drain every parked receiver (drives rx_kernel, one WakeWaker per waiter).
fn wake_all<T>(g: &mut WatchInner<T>) -> Vec<Waker> {
  let mut out: Vec<Waker> = Vec::new();
  while g.rx_kernel.queue.len() > 0 {
    match g.rx_kernel.signal_step(0) {
      SignalAction::Woke(id) => {
        if let Some(pos) = g.waiters.iter().position(|(wid, _)| *wid == id) {
          out.push(g.waiters.remove(pos).1);
        }
      }
      SignalAction::Stored => break,
    }
  }
  out
}

impl<T> Sender<T> {
  pub fn send(&self, value: T) -> Result<(), T> {
    let mut g = self.inner.lock().unwrap();
    g.value = value;
    // send_step carries no decision: it returns the new version, which the
    // kernel also retains in g.wkern.version (the value receivers compare).
    g.wkern.send_step();
    let wakers = wake_all(&mut g);
    drop(g);
    for w in wakers {
      w.wake();
    }
    Ok(())
  }

  pub fn send_replace(&self, value: T) -> T {
    let mut g = self.inner.lock().unwrap();
    let old = std::mem::replace(&mut g.value, value);
    // send_step carries no decision (returns the new version, kept in
    // g.wkern.version).
    g.wkern.send_step();
    let wakers = wake_all(&mut g);
    drop(g);
    for w in wakers {
      w.wake();
    }
    old
  }

  pub fn send_modify<F: FnOnce(&mut T)>(&self, f: F) {
    let mut g = self.inner.lock().unwrap();
    f(&mut g.value);
    // send_step carries no decision (returns the new version, kept in
    // g.wkern.version).
    g.wkern.send_step();
    let wakers = wake_all(&mut g);
    drop(g);
    for w in wakers {
      w.wake();
    }
  }

  pub fn borrow(&self) -> WatchRef<'_, T> {
    WatchRef { guard: self.inner.lock().unwrap() }
  }

  pub fn subscribe(&self) -> Receiver<T> {
    let g = self.inner.lock().unwrap();
    let version = g.wkern.version;
    drop(g);
    Receiver { inner: self.inner.clone(), seen_version: version }
  }
}

impl<T> Drop for Sender<T> {
  fn drop(&mut self) {
    let mut g = self.inner.lock().unwrap();
    g.tx_dropped = true;
    let wakers = wake_all(&mut g);
    drop(g);
    for w in wakers {
      w.wake();
    }
  }
}

pub struct WatchRef<'a, T> {
  guard: std::sync::MutexGuard<'a, WatchInner<T>>,
}

impl<'a, T> std::ops::Deref for WatchRef<'a, T> {
  type Target = T;
  fn deref(&self) -> &T {
    &self.guard.value
  }
}

impl<T> Receiver<T> {
  pub fn changed(&mut self) -> Changed<'_, T> {
    Changed { rx: self, id: 0, parked: false }
  }

  pub fn borrow(&self) -> WatchRef<'_, T> {
    WatchRef { guard: self.inner.lock().unwrap() }
  }

  pub fn borrow_and_update(&mut self) -> WatchRef<'_, T> {
    let guard = self.inner.lock().unwrap();
    self.seen_version = guard.wkern.version;
    WatchRef { guard }
  }

  pub fn has_changed(&self) -> Result<bool, RecvError> {
    let g = self.inner.lock().unwrap();
    if g.tx_dropped && g.wkern.version == self.seen_version {
      return Err(RecvError);
    }
    Ok(g.wkern.version != self.seen_version)
  }

  pub async fn wait_for(
    &mut self,
    mut f: impl FnMut(&T) -> bool,
  ) -> Result<WatchRef<'_, T>, RecvError> {
    // Wait until the predicate holds (no borrow escapes this loop).
    loop {
      let matched = {
        let g = self.inner.lock().unwrap();
        let m = f(&g.value);
        if !m && g.tx_dropped {
          return Err(RecvError);
        }
        m
      };
      if matched {
        break;
      }
      self.changed().await?;
    }
    // Predicate held; hand back a ref (acquired after the loop, so no borrow clash).
    let g = self.inner.lock().unwrap();
    self.seen_version = g.wkern.version;
    Ok(WatchRef { guard: g })
  }
}

impl<T> std::fmt::Debug for Sender<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("watch::Sender").finish_non_exhaustive()
  }
}

impl<T> std::fmt::Debug for Receiver<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("watch::Receiver").finish_non_exhaustive()
  }
}

impl<T> Clone for Receiver<T> {
  fn clone(&self) -> Self {
    Receiver { inner: self.inner.clone(), seen_version: self.seen_version }
  }
}

pub struct Changed<'a, T> {
  rx: &'a mut Receiver<T>,
  id: u64,
  parked: bool,
}

impl<'a, T> Future for Changed<'a, T> {
  type Output = Result<(), RecvError>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = self.get_mut();
    let mut g = this.rx.inner.lock().unwrap();
    loop {
      if g.wkern.version != this.rx.seen_version {
        this.rx.seen_version = g.wkern.version;
        return Poll::Ready(Ok(()));
      }
      if g.tx_dropped {
        return Poll::Ready(Err(RecvError));
      }
      if this.parked {
        let id = this.id;
        if let Some(pos) = g.waiters.iter().position(|(wid, _)| *wid == id) {
          g.waiters[pos].1 = cx.waker().clone();
        }
        return Poll::Pending;
      }
      let id = g.next_id;
      g.next_id += 1;
      match g.rx_kernel.wait_step(id) {
        WaitAction::Ready => {
          // Kernel consumed a stored wake hint instead of enqueuing us
          // (unreachable under wake_all's drain-only signaling, handled
          // mechanically): NOT parked — re-check the version immediately.
          continue;
        }
        WaitAction::Park(_) => {
          this.id = id;
          g.waiters.push((id, cx.waker().clone()));
          this.parked = true;
          return Poll::Pending;
        }
      }
    }
  }
}

impl<'a, T> Drop for Changed<'a, T> {
  fn drop(&mut self) {
    if !self.parked {
      return;
    }
    // Withdraw the parked receiver. No forwarding needed: every wake here is a
    // broadcast (send / sender-drop drives wake_all, draining the whole queue
    // under the same lock that bumps the version), so a woken-but-never-polled
    // Changed was already fully deregistered and the change stays observable
    // via the persistent version counter.
    let mut g = self.rx.inner.lock().unwrap();
    if g.rx_kernel.remove_step(self.id) {
      if let Some(pos) = g.waiters.iter().position(|(wid, _)| *wid == self.id) {
        g.waiters.remove(pos);
      }
    }
  }
}
