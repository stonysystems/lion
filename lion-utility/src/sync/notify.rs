// Trusted glue: a real Notify wrapping the verified WaiterKernel. This module is
// the trust boundary (Mutex, Arc/AtomicBool, real Waker, Pin) — `verus::trusted`
// under Verus, plain Rust under cargo. Every control decision (consume a permit
// vs park, wake a waiter vs store a permit, and *which* waiter) is made by the
// kernel's verified wait_step/signal_step; the glue only assigns waker ids, holds
// the real wakers, and performs wake().
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::sync::waiter::kernel::{SignalAction, WaitAction, WaiterKernel};
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};

// Woken-flag values: how a parked waiter's notification was delivered. A Drop of
// a woken-but-never-polled Notified must forward a notify_one delivery (one-shot,
// would otherwise be lost) but not a notify_waiters one (broadcast).
const PENDING: u8 = 0;
const NOTIFIED_ONE: u8 = 1;
const NOTIFIED_ALL: u8 = 2;

struct NotifyInner {
  kernel: WaiterKernel,
  // Real-waker storage for parked waiters: (id, woken-flag, waker). The kernel
  // owns the queue *order*; this maps the id it returns back to the real waker.
  wakers: Vec<(u64, Arc<AtomicU8>, Waker)>,
  next_id: u64,
}

pub struct Notify {
  inner: Mutex<NotifyInner>,
}

// One notify_one delivery: the kernel decides who/whether, skipping ids whose
// waiter was dropped. The woken flag is set under the lock (so a concurrent Drop
// never sees dequeued-but-unflagged); the caller performs wake() after unlocking.
// Shared by notify_one and Notified::drop's forwarding path.
fn deliver_one(g: &mut NotifyInner) -> Option<Waker> {
  loop {
    match g.kernel.signal_step(0) {
      SignalAction::Woke(id) => {
        if let Some(pos) = g.wakers.iter().position(|(wid, _, _)| *wid == id) {
          let (_, flag, waker) = g.wakers.remove(pos);
          flag.store(NOTIFIED_ONE, Ordering::Release);
          return Some(waker);
        }
        // dead id (waiter dropped) — kernel already removed it; keep going.
      }
      SignalAction::Stored => return None,
    }
  }
}

impl Default for Notify {
  fn default() -> Self {
    Self::new()
  }
}

impl Notify {
  pub fn new() -> Self {
    Notify {
      inner: Mutex::new(NotifyInner {
        kernel: WaiterKernel::new(),
        wakers: Vec::new(),
        next_id: 0,
      }),
    }
  }

  pub fn notify_one(&self) {
    let mut g = self.inner.lock().unwrap();
    let w = deliver_one(&mut g);
    drop(g);
    if let Some(w) = w {
      w.wake();
    }
  }

  pub fn notify_waiters(&self) {
    let mut g = self.inner.lock().unwrap();
    let mut to_wake: Vec<Waker> = Vec::new();
    // Drain exactly the currently-parked waiters (never store a permit): only
    // call signal_step while the kernel queue is non-empty. Flags are set under
    // the lock so a concurrent Drop never sees dequeued-but-unflagged.
    while g.kernel.queue.len() > 0 {
      match g.kernel.signal_step(0) {
        SignalAction::Woke(id) => {
          if let Some(pos) = g.wakers.iter().position(|(wid, _, _)| *wid == id) {
            let (_, flag, waker) = g.wakers.remove(pos);
            flag.store(NOTIFIED_ALL, Ordering::Release);
            to_wake.push(waker);
          }
        }
        SignalAction::Stored => break,
      }
    }
    drop(g);
    for waker in to_wake {
      waker.wake();
    }
  }

  pub fn notified(&self) -> Notified<'_> {
    Notified {
      notify: self,
      id: 0,
      flag: Arc::new(AtomicU8::new(PENDING)),
      parked: false,
      completed: false,
    }
  }
}

pub struct Notified<'a> {
  notify: &'a Notify,
  id: u64,
  flag: Arc<AtomicU8>,
  parked: bool,
  completed: bool,
}

impl<'a> Future for Notified<'a> {
  type Output = ();

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
    let this = unsafe { self.get_unchecked_mut() };
    if this.flag.load(Ordering::Acquire) != PENDING {
      this.completed = true;
      return Poll::Ready(());
    }
    let mut g = this.notify.inner.lock().unwrap();
    if !this.parked {
      // First effective poll: let the kernel decide ready-vs-park.
      this.id = g.next_id;
      g.next_id += 1;
      match g.kernel.wait_step(this.id) {
        WaitAction::Ready => {
          this.completed = true;
          Poll::Ready(())
        }
        WaitAction::Park(id) => {
          this.parked = true;
          g.wakers.push((id, this.flag.clone(), cx.waker().clone()));
          Poll::Pending
        }
      }
    } else {
      // Already parked (not yet woken): refresh the stored waker, stay pending.
      let id = this.id;
      if let Some(pos) = g.wakers.iter().position(|(wid, _, _)| *wid == id) {
        g.wakers[pos].2 = cx.waker().clone();
      }
      Poll::Pending
    }
  }
}

impl<'a> Drop for Notified<'a> {
  fn drop(&mut self) {
    if self.completed || !self.parked {
      // Finished normally (flag consumed or Ready on first poll), or never
      // parked — nothing was enqueued, nothing to cancel.
      return;
    }
    let mut g = self.notify.inner.lock().unwrap();
    if g.kernel.remove_step(self.id) {
      // Still parked: fully withdrawn (kernel queue + real-waker entry).
      if let Some(pos) = g.wakers.iter().position(|(wid, _, _)| *wid == self.id) {
        g.wakers.remove(pos);
      }
    } else if self.flag.load(Ordering::Acquire) == NOTIFIED_ONE {
      // notify_one picked us (dequeued + flagged) but we were never polled:
      // forward the one-shot notification so it is not lost.
      if g.kernel.permit < u64::MAX {
        let w = deliver_one(&mut g);
        drop(g);
        if let Some(w) = w {
          w.wake();
        }
      }
      // else: permit saturated — unreachable in practice (F9); drop the forward.
    }
    // else: NOTIFIED_ALL (broadcast — every parked waiter was already woken,
    // nothing to forward) — the signal path already removed our entries.
  }
}
