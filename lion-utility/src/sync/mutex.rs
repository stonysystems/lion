// Trusted glue: an async Mutex as a 1-permit Semaphore + UnsafeCell, exactly as
// tokio layers it. verus::trusted under Verus, plain Rust under cargo. All lock
// arbitration is the verified WaiterKernel inside the Semaphore; this module only
// adds the data cell and the guard types.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::sync::semaphore::{drop_acquire_inner, poll_acquire_inner, Acquire, Semaphore, SemaphorePermit};
use std::cell::UnsafeCell;
use std::future::Future;
use std::ops::{Deref, DerefMut};
use std::pin::Pin;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::task::{Context, Poll};

pub struct Mutex<T: ?Sized> {
  sem: Semaphore,
  data: UnsafeCell<T>,
}

unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}

impl<T> Mutex<T> {
  pub fn new(value: T) -> Self {
    Mutex { sem: Semaphore::new(1), data: UnsafeCell::new(value) }
  }

  pub fn into_inner(self) -> T {
    self.data.into_inner()
  }
}

impl<T: ?Sized> Mutex<T> {
  pub fn lock(&self) -> Lock<'_, T> {
    Lock { mutex: self, acquire: self.sem.acquire() }
  }

  pub fn try_lock(&self) -> Result<MutexGuard<'_, T>, ()> {
    match self.sem.try_acquire() {
      Ok(permit) => Ok(MutexGuard { mutex: self, _permit: permit }),
      Err(()) => Err(()),
    }
  }

  pub fn get_mut(&mut self) -> &mut T {
    unsafe { &mut *self.data.get() }
  }

  pub fn lock_owned(self: Arc<Self>) -> LockOwned<T> {
    LockOwned { mutex: Some(self), granted: Arc::new(AtomicBool::new(false)), id: 0, parked: false }
  }

  pub fn try_lock_owned(self: Arc<Self>) -> Result<OwnedMutexGuard<T>, ()> {
    let acquired = match self.sem.try_acquire() {
      Ok(permit) => {
        permit.forget();
        true
      }
      Err(()) => false,
    };
    if acquired {
      Ok(OwnedMutexGuard { mutex: self })
    } else {
      Err(())
    }
  }
}

// Cancellation safety: dropping a parked Lock drops its inner Acquire, whose
// Drop withdraws the waiter / forwards an unpolled grant — no impl needed here.
pub struct Lock<'a, T: ?Sized> {
  mutex: &'a Mutex<T>,
  acquire: Acquire<'a>,
}

impl<'a, T: ?Sized> Future for Lock<'a, T> {
  type Output = MutexGuard<'a, T>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = unsafe { self.get_unchecked_mut() };
    match Pin::new(&mut this.acquire).poll(cx) {
      Poll::Ready(Ok(permit)) => Poll::Ready(MutexGuard { mutex: this.mutex, _permit: permit }),
      Poll::Ready(Err(_)) => unreachable!("mutex semaphore never closes"),
      Poll::Pending => Poll::Pending,
    }
  }
}

pub struct MutexGuard<'a, T: ?Sized> {
  mutex: &'a Mutex<T>,
  _permit: SemaphorePermit<'a>,
}

impl<'a, T: ?Sized> Deref for MutexGuard<'a, T> {
  type Target = T;
  fn deref(&self) -> &T {
    unsafe { &*self.mutex.data.get() }
  }
}

impl<'a, T: ?Sized> DerefMut for MutexGuard<'a, T> {
  fn deref_mut(&mut self) -> &mut T {
    unsafe { &mut *self.mutex.data.get() }
  }
}

// ── Owned variants (Arc<Mutex<T>>::lock_owned) ──
pub struct LockOwned<T: ?Sized> {
  mutex: Option<Arc<Mutex<T>>>,
  granted: Arc<AtomicBool>,
  id: u64,
  parked: bool,
}

impl<T: ?Sized> Future for LockOwned<T> {
  type Output = OwnedMutexGuard<T>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = unsafe { self.get_unchecked_mut() };
    let m = this.mutex.as_ref().expect("LockOwned polled after completion");
    match poll_acquire_inner(&m.sem.inner, &this.granted, &mut this.id, &mut this.parked, cx) {
      Poll::Ready(Ok(())) => {
        let mutex = this.mutex.take().unwrap();
        Poll::Ready(OwnedMutexGuard { mutex })
      }
      Poll::Ready(Err(_)) => unreachable!("mutex semaphore never closes"),
      Poll::Pending => Poll::Pending,
    }
  }
}

impl<T: ?Sized> Drop for LockOwned<T> {
  fn drop(&mut self) {
    // `mutex` is None exactly when poll completed (the guard owns the lock).
    if let Some(m) = self.mutex.take() {
      drop_acquire_inner(&m.sem.inner, &self.granted, self.id, self.parked);
    }
  }
}

pub struct OwnedMutexGuard<T: ?Sized> {
  mutex: Arc<Mutex<T>>,
}

impl<T: ?Sized> Deref for OwnedMutexGuard<T> {
  type Target = T;
  fn deref(&self) -> &T {
    unsafe { &*self.mutex.data.get() }
  }
}

impl<T: ?Sized> DerefMut for OwnedMutexGuard<T> {
  fn deref_mut(&mut self) -> &mut T {
    unsafe { &mut *self.mutex.data.get() }
  }
}

impl<T: ?Sized> Drop for OwnedMutexGuard<T> {
  fn drop(&mut self) {
    self.mutex.sem.release(1);
  }
}
