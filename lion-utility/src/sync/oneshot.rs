// Trusted glue: a oneshot channel over TWO verified kernels — OneshotKernel
// (the value-transfer state machine: send-once, at-most-once delivery) decides
// every data transition, and WaiterKernel routes the receiver's wakeup (park =
// wait_step Park, wake = signal_step Woke(id) mapped through the one-entry
// id->waker slot). The glue only moves the real T as the kernels direct and
// performs wake(). verus::trusted under Verus, plain Rust under cargo.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::sync::oneshot_kernel::{OneshotKernel, RecvDecision};
use crate::sync::waiter::kernel::{SignalAction, WaitAction, WaiterKernel};
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};

#[derive(Debug)]
pub struct RecvError;

impl std::fmt::Display for RecvError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "channel closed")
  }
}

impl std::error::Error for RecvError {}

struct OneshotInner<T> {
  okernel: OneshotKernel,
  wkernel: WaiterKernel,
  value: Option<T>,
  // The single-receiver id->waker map (oneshot has ONE receiver, so one entry).
  rx_waker: Option<(u64, Waker)>,
  rx_dropped: bool,
  next_id: u64,
}

pub struct Sender<T> {
  inner: Arc<Mutex<OneshotInner<T>>>,
}

pub struct Receiver<T> {
  inner: Arc<Mutex<OneshotInner<T>>>,
  id: u64,
  parked: bool,
}

pub fn channel<T>() -> (Sender<T>, Receiver<T>) {
  let inner = Arc::new(Mutex::new(OneshotInner {
    okernel: OneshotKernel::new(),
    wkernel: WaiterKernel::new(),
    value: None,
    rx_waker: None,
    rx_dropped: false,
    next_id: 0,
  }));
  (Sender { inner: inner.clone() }, Receiver { inner, id: 0, parked: false })
}

// Route one wkernel signal to the real waker (the single-receiver analog of
// notify's deliver_one): Woke(id) maps through the id->waker slot; Stored means
// no receiver was parked — the stored permit makes a later wait_step return
// Ready, which the receiver's poll answers by re-checking the oneshot state.
fn deliver<T>(g: &mut OneshotInner<T>) -> Option<Waker> {
  match g.wkernel.signal_step(0) {
    SignalAction::Woke(id) => match g.rx_waker.take() {
      Some((wid, w)) if wid == id => Some(w),
      other => {
        // Stale queue entry (receiver already withdrawn): no waker to run.
        g.rx_waker = other;
        None
      }
    },
    SignalAction::Stored => None,
  }
}

// A (formerly) parked receiver leaves: withdraw it from the kernel queue and
// tidy the waker slot. If remove_step reports it was already dequeued (woken
// but never polled) there is nothing to forward — this is the only receiver.
fn withdraw_rx<T>(g: &mut OneshotInner<T>, id: u64) {
  let _ = g.wkernel.remove_step(id);
  if g.rx_waker.as_ref().map_or(false, |(wid, _)| *wid == id) {
    g.rx_waker = None;
  }
}

impl<T> Sender<T> {
  pub fn send(self, value: T) -> Result<(), T> {
    let mut g = self.inner.lock().unwrap();
    if g.rx_dropped {
      return Err(value);
    }
    // OneshotKernel decides whether the value is accepted (first send).
    if g.okernel.send_step() {
      g.value = Some(value);
      let w = deliver(&mut g);
      drop(g);
      if let Some(w) = w {
        w.wake();
      }
      Ok(())
    } else {
      Err(value)
    }
  }
}

impl<T> Drop for Sender<T> {
  fn drop(&mut self) {
    let mut g = self.inner.lock().unwrap();
    g.okernel.close_step();
    let w = deliver(&mut g);
    drop(g);
    if let Some(w) = w {
      w.wake();
    }
  }
}

impl<T> Future for Receiver<T> {
  type Output = Result<T, RecvError>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = unsafe { self.get_unchecked_mut() };
    let mut g = this.inner.lock().unwrap();
    loop {
      match g.okernel.recv_step() {
        RecvDecision::Ready => {
          if this.parked {
            withdraw_rx(&mut g, this.id);
            this.parked = false;
          }
          return Poll::Ready(Ok(g.value.take().unwrap()));
        }
        RecvDecision::Closed => {
          if this.parked {
            withdraw_rx(&mut g, this.id);
            this.parked = false;
          }
          return Poll::Ready(Err(RecvError));
        }
        RecvDecision::Park => {
          if this.parked {
            // Already enqueued: refresh the stored waker, stay pending.
            if let Some((wid, w)) = g.rx_waker.as_mut() {
              if *wid == this.id {
                *w = cx.waker().clone();
              }
            }
            return Poll::Pending;
          }
          let id = g.next_id;
          g.next_id += 1;
          match g.wkernel.wait_step(id) {
            WaitAction::Ready => {
              // A stored signal was consumed (send/close signaled before we
              // parked): NOT enqueued — re-check the oneshot state.
              continue;
            }
            WaitAction::Park(_) => {
              this.id = id;
              this.parked = true;
              g.rx_waker = Some((id, cx.waker().clone()));
              return Poll::Pending;
            }
          }
        }
      }
    }
  }
}

impl<T> Drop for Receiver<T> {
  fn drop(&mut self) {
    let mut g = self.inner.lock().unwrap();
    g.rx_dropped = true;
    if self.parked {
      withdraw_rx(&mut g, self.id);
    }
  }
}
