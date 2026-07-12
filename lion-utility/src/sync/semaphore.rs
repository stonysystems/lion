// Trusted glue: a counting Semaphore over the verified WaiterKernel (one permit
// per acquire). verus::trusted under Verus, plain Rust under cargo. The kernel
// owns permit accounting, the waiter queue and every decision (grant vs park,
// wake vs store, which waiter); the glue only assigns ids, holds real wakers and
// calls wake(). acquire_many / acquire_owned are not provided (not needed by the
// target call sites); add them on demand.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::sync::waiter::kernel::{SignalAction, WaitAction, WaiterKernel};
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};

pub(crate) struct SemaphoreInner {
  pub(crate) kernel: WaiterKernel,
  pub(crate) wakers: Vec<(u64, Arc<AtomicBool>, Waker)>,
  pub(crate) next_id: u64,
  pub(crate) closed: bool,
}

pub struct Semaphore {
  pub(crate) inner: Arc<Mutex<SemaphoreInner>>,
}

#[derive(Debug)]
pub struct AcquireError;

impl std::fmt::Display for AcquireError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "semaphore closed")
  }
}

impl std::error::Error for AcquireError {}

impl std::fmt::Debug for Semaphore {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("Semaphore").finish_non_exhaustive()
  }
}

// Distribute `n` permits: each goes to the next live head waiter (skipping
// dropped ids the kernel cleans as it dequeues) or is stored by the kernel.
// Granted flags are set under the lock (so a concurrent Drop never sees
// dequeued-but-unflagged); the caller performs wake() after unlocking.
fn signal_n(inner: &mut SemaphoreInner, n: usize) -> Vec<Waker> {
  let mut to_wake: Vec<Waker> = Vec::new();
  for _ in 0..n {
    loop {
      match inner.kernel.signal_step(0) {
        SignalAction::Woke(id) => {
          if let Some(pos) = inner.wakers.iter().position(|(wid, _, _)| *wid == id) {
            let (_, flag, waker) = inner.wakers.remove(pos);
            flag.store(true, Ordering::Release);
            to_wake.push(waker);
            break;
          }
          // dead id (waiter dropped) — try the next one for this permit.
        }
        SignalAction::Stored => break,
      }
    }
  }
  to_wake
}

pub(crate) fn do_release(m: &Mutex<SemaphoreInner>, n: usize) {
  let mut g = m.lock().unwrap();
  let to_wake = signal_n(&mut g, n);
  drop(g);
  for waker in to_wake {
    waker.wake();
  }
}

// Shared cancellation path (Acquire's and Mutex's LockOwned's Drop): withdraw a
// dropped waiter, forwarding its permit if a release granted one it never polled.
pub(crate) fn drop_acquire_inner(
  m: &Mutex<SemaphoreInner>,
  granted: &Arc<AtomicBool>,
  id: u64,
  parked: bool,
) {
  if !parked {
    // Never enqueued (never polled, or Ready/closed on first poll).
    return;
  }
  let mut g = m.lock().unwrap();
  if g.kernel.remove_step(id) {
    // Still parked: fully withdrawn (kernel queue + real-waker entry).
    if let Some(pos) = g.wakers.iter().position(|(wid, _, _)| *wid == id) {
      g.wakers.remove(pos);
    }
  } else if granted.load(Ordering::Acquire) {
    // A release granted us a permit that was never polled: forward it to the
    // next waiter (or store it back) so it is not leaked — a leaked permit on a
    // Mutex's semaphore would deadlock the mutex forever.
    if g.kernel.permit < u64::MAX {
      let to_wake = signal_n(&mut g, 1);
      drop(g);
      for waker in to_wake {
        waker.wake();
      }
    }
    // else: permit saturated — unreachable in practice (F9); drop the forward.
  }
  // else: dequeued without a grant (close() woke everyone) — nothing to return.
}

// Shared acquire poll, used by both the borrowed Acquire and Mutex's owned lock.
pub(crate) fn poll_acquire_inner(
  m: &Mutex<SemaphoreInner>,
  granted: &Arc<AtomicBool>,
  id: &mut u64,
  parked: &mut bool,
  cx: &Context<'_>,
) -> Poll<Result<(), AcquireError>> {
  if granted.load(Ordering::Acquire) {
    return Poll::Ready(Ok(()));
  }
  let mut g = m.lock().unwrap();
  if g.closed {
    return Poll::Ready(Err(AcquireError));
  }
  if !*parked {
    *id = g.next_id;
    g.next_id += 1;
    match g.kernel.wait_step(*id) {
      WaitAction::Ready => Poll::Ready(Ok(())),
      WaitAction::Park(pid) => {
        *parked = true;
        g.wakers.push((pid, granted.clone(), cx.waker().clone()));
        Poll::Pending
      }
    }
  } else {
    let wid = *id;
    if let Some(pos) = g.wakers.iter().position(|(x, _, _)| *x == wid) {
      g.wakers[pos].2 = cx.waker().clone();
    }
    Poll::Pending
  }
}

impl Semaphore {
  pub fn new(permits: usize) -> Self {
    Semaphore {
      inner: Arc::new(Mutex::new(SemaphoreInner {
        kernel: WaiterKernel::with_permits(permits as u64),
        wakers: Vec::new(),
        next_id: 0,
        closed: false,
      })),
    }
  }

  pub fn available_permits(&self) -> usize {
    self.inner.lock().unwrap().kernel.permit as usize
  }

  pub fn try_acquire(&self) -> Result<SemaphorePermit<'_>, ()> {
    let mut g = self.inner.lock().unwrap();
    if g.closed {
      return Err(());
    }
    if g.kernel.try_acquire_step() {
      Ok(SemaphorePermit { sem: self, permits: 1 })
    } else {
      Err(())
    }
  }

  pub fn add_permits(&self, n: usize) {
    do_release(&self.inner, n);
  }

  pub(crate) fn release(&self, n: usize) {
    do_release(&self.inner, n);
  }

  pub fn close(&self) {
    let mut g = self.inner.lock().unwrap();
    g.closed = true;
    let wakers: Vec<Waker> = std::mem::take(&mut g.wakers).into_iter().map(|(_, _, w)| w).collect();
    drop(g);
    for waker in wakers {
      waker.wake();
    }
  }

  pub fn acquire(&self) -> Acquire<'_> {
    Acquire {
      sem: self,
      granted: Arc::new(AtomicBool::new(false)),
      id: 0,
      parked: false,
      completed: false,
    }
  }
}

pub struct Acquire<'a> {
  sem: &'a Semaphore,
  granted: Arc<AtomicBool>,
  id: u64,
  parked: bool,
  completed: bool,
}

impl<'a> Future for Acquire<'a> {
  type Output = Result<SemaphorePermit<'a>, AcquireError>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = unsafe { self.get_unchecked_mut() };
    match poll_acquire_inner(&this.sem.inner, &this.granted, &mut this.id, &mut this.parked, cx) {
      Poll::Ready(Ok(())) => {
        // The permit now lives in the SemaphorePermit (released by its Drop).
        this.completed = true;
        Poll::Ready(Ok(SemaphorePermit { sem: this.sem, permits: 1 }))
      }
      Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
      Poll::Pending => Poll::Pending,
    }
  }
}

impl<'a> Drop for Acquire<'a> {
  fn drop(&mut self) {
    if self.completed {
      return;
    }
    drop_acquire_inner(&self.sem.inner, &self.granted, self.id, self.parked);
  }
}

pub struct SemaphorePermit<'a> {
  sem: &'a Semaphore,
  permits: usize,
}

impl<'a> SemaphorePermit<'a> {
  pub fn forget(mut self) {
    self.permits = 0;
  }
}

impl<'a> Drop for SemaphorePermit<'a> {
  fn drop(&mut self) {
    if self.permits > 0 {
      self.sem.release(self.permits);
    }
  }
}
