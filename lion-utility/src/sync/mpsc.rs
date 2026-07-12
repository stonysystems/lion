// Trusted glue: mpsc (multi-producer, single-consumer) over THREE verified
// kernels: ChannelKernel decides every data transition (push/pop/reserve/fill,
// capacity) and proves FIFO / no-loss / capacity; two WaiterKernels handle wakeup
// (rx parks when empty, a bounded tx parks when full). The glue holds the real T
// VecDeque and moves values in lockstep with the ChannelKernel's decisions, and
// performs wake(). verus::trusted under Verus, plain Rust under cargo.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::sync::channel_kernel::ChannelKernel;
use crate::sync::waiter::kernel::{SignalAction, WaitAction, WaiterKernel};
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};

#[derive(Debug)]
pub struct SendError<T>(pub T);

impl<T> std::fmt::Display for SendError<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "channel closed")
  }
}

impl<T: std::fmt::Debug> std::error::Error for SendError<T> {}

#[derive(Debug)]
pub struct RecvError;

#[derive(Debug)]
pub enum TrySendError<T> {
  Full(T),
  Closed(T),
}

impl<T> std::fmt::Display for TrySendError<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      TrySendError::Full(_) => write!(f, "channel full"),
      TrySendError::Closed(_) => write!(f, "channel closed"),
    }
  }
}

impl<T: std::fmt::Debug> std::error::Error for TrySendError<T> {}

// ── Bounded ──
struct BoundedInner<T> {
  rx_kernel: WaiterKernel,
  tx_kernel: WaiterKernel,
  ckernel: ChannelKernel,
  buffer: VecDeque<T>,
  rx_waker: Option<Waker>,
  tx_wakers: Vec<(u64, Waker)>,
  sender_count: usize,
  rx_closed: bool,
  rx_next_id: u64,
  tx_next_id: u64,
}

pub struct Sender<T> {
  inner: Arc<Mutex<BoundedInner<T>>>,
}

pub struct Receiver<T> {
  inner: Arc<Mutex<BoundedInner<T>>>,
}

pub fn channel<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
  assert!(capacity > 0, "mpsc channel capacity must be positive");
  let inner = Arc::new(Mutex::new(BoundedInner {
    rx_kernel: WaiterKernel::new(),
    tx_kernel: WaiterKernel::new(),
    ckernel: ChannelKernel::new(capacity as u64),
    buffer: VecDeque::with_capacity(capacity),
    rx_waker: None,
    tx_wakers: Vec::new(),
    sender_count: 1,
    rx_closed: false,
    rx_next_id: 0,
    tx_next_id: 0,
  }));
  (Sender { inner: inner.clone() }, Receiver { inner })
}

fn wake_rx_bounded<T>(g: &mut BoundedInner<T>) -> Option<Waker> {
  let _ = g.rx_kernel.signal_step(0);
  g.rx_waker.take()
}

// Drain-only: a tx wake is a hint (the woken sender re-checks ckernel capacity
// on its next poll), so never store a permit — a stored tx permit would make a
// later wait_step return Ready (which the glue ignores), leaving that sender out
// of the kernel queue and thus never wakeable: a lost wakeup. Only signal while
// a waiter is actually parked, skipping ids whose sender future was dropped.
fn wake_one_tx_bounded<T>(g: &mut BoundedInner<T>) -> Option<Waker> {
  while g.tx_kernel.queue.len() > 0 {
    match g.tx_kernel.signal_step(0) {
      SignalAction::Woke(id) => {
        if let Some(pos) = g.tx_wakers.iter().position(|(wid, _)| *wid == id) {
          let (_, waker) = g.tx_wakers.remove(pos);
          return Some(waker);
        }
        // dead id (sender future dropped) — try the next parked sender.
      }
      SignalAction::Stored => return None,
    }
  }
  None
}

// A parked tx waiter withdraws (self-cleanup on direct completion, or its
// future's Drop): remove it from the kernel queue and the real-waker map.
fn remove_tx_waiter<T>(g: &mut BoundedInner<T>, id: u64) -> bool {
  let removed = g.tx_kernel.remove_step(id);
  if let Some(pos) = g.tx_wakers.iter().position(|(wid, _)| *wid == id) {
    g.tx_wakers.remove(pos);
  }
  removed
}

// Shared Drop path for Send/Reserve. A cancelled parked waiter is withdrawn; a
// woken-but-never-polled one (dequeued by wake_one_tx_bounded, so remove_step
// misses) has consumed a slot-free hint without using it — forward that hint to
// the next parked sender so it is not lost.
fn drop_tx_waiter<T>(m: &Mutex<BoundedInner<T>>, id: u64, parked: bool, completed: bool) {
  if completed || !parked {
    return;
  }
  let mut g = m.lock().unwrap();
  if !remove_tx_waiter(&mut g, id) {
    let w = wake_one_tx_bounded(&mut g);
    drop(g);
    if let Some(w) = w {
      w.wake();
    }
  }
}

impl<T> Sender<T> {
  pub fn send(&self, value: T) -> Send<'_, T> {
    Send { tx: self, value: Some(value), id: 0, parked: false, completed: false }
  }

  pub fn try_send(&self, value: T) -> Result<(), SendError<T>> {
    let mut g = self.inner.lock().unwrap();
    if g.rx_closed {
      return Err(SendError(value));
    }
    if g.ckernel.try_push() {
      g.buffer.push_back(value);
      let w = wake_rx_bounded(&mut g);
      drop(g);
      if let Some(w) = w {
        w.wake();
      }
      Ok(())
    } else {
      Err(SendError(value))
    }
  }

  pub fn is_closed(&self) -> bool {
    self.inner.lock().unwrap().rx_closed
  }

  pub fn reserve(&self) -> Reserve<'_, T> {
    Reserve { tx: self, id: 0, parked: false, completed: false }
  }

  pub fn try_reserve(&self) -> Result<Permit<'_, T>, TrySendError<()>> {
    let mut g = self.inner.lock().unwrap();
    if g.rx_closed {
      return Err(TrySendError::Closed(()));
    }
    if g.ckernel.reserve() {
      Ok(Permit { tx: self, done: false })
    } else {
      Err(TrySendError::Full(()))
    }
  }
}

// A reserved capacity slot. `send` fills it (no blocking); dropping it unreserved
// frees the slot and wakes a waiting sender.
pub struct Permit<'a, T> {
  tx: &'a Sender<T>,
  done: bool,
}

impl<'a, T> std::fmt::Debug for Permit<'a, T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("mpsc::Permit").finish_non_exhaustive()
  }
}

impl<'a, T> Permit<'a, T> {
  pub fn send(mut self, value: T) {
    let mut g = self.tx.inner.lock().unwrap();
    g.ckernel.fill();
    g.buffer.push_back(value);
    let w = wake_rx_bounded(&mut g);
    drop(g);
    if let Some(w) = w {
      w.wake();
    }
    self.done = true;
  }
}

impl<'a, T> Drop for Permit<'a, T> {
  fn drop(&mut self) {
    if !self.done {
      let mut g = self.tx.inner.lock().unwrap();
      g.ckernel.unreserve();
      let w = wake_one_tx_bounded(&mut g);
      drop(g);
      if let Some(w) = w {
        w.wake();
      }
    }
  }
}

pub struct Reserve<'a, T> {
  tx: &'a Sender<T>,
  id: u64,
  parked: bool,
  completed: bool,
}

impl<'a, T> Future for Reserve<'a, T> {
  type Output = Result<Permit<'a, T>, SendError<()>>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = unsafe { self.get_unchecked_mut() };
    let mut g = this.tx.inner.lock().unwrap();
    loop {
      if g.rx_closed {
        return Poll::Ready(Err(SendError(())));
      }
      if g.ckernel.reserve() {
        if this.parked {
          // Completed directly while (possibly) still parked: withdraw so a
          // later wake hint is not consumed by this finished waiter.
          remove_tx_waiter(&mut g, this.id);
        }
        this.completed = true;
        return Poll::Ready(Ok(Permit { tx: this.tx, done: false }));
      }
      // Full: still parked from a previous poll — refresh the stored waker.
      if this.parked && g.tx_wakers.iter().any(|(wid, _)| *wid == this.id) {
        let id = this.id;
        if let Some(pos) = g.tx_wakers.iter().position(|(wid, _)| *wid == id) {
          g.tx_wakers[pos].1 = cx.waker().clone();
        }
        return Poll::Pending;
      }
      // Park (once per park-episode): the kernel decides Ready vs Park.
      let id = g.tx_next_id;
      g.tx_next_id += 1;
      match g.tx_kernel.wait_step(id) {
        WaitAction::Ready => {
          // Kernel consumed a stored slot hint instead of enqueuing us
          // (unreachable under U2's drain-only tx wakes, handled mechanically):
          // we are NOT parked, so re-attempt the reserve fast path.
          continue;
        }
        WaitAction::Park(_) => {
          this.id = id;
          g.tx_wakers.push((id, cx.waker().clone()));
          this.parked = true;
          return Poll::Pending;
        }
      }
    }
  }
}

impl<'a, T> Drop for Reserve<'a, T> {
  fn drop(&mut self) {
    drop_tx_waiter(&self.tx.inner, self.id, self.parked, self.completed);
  }
}

impl<T> Clone for Sender<T> {
  fn clone(&self) -> Self {
    let mut g = self.inner.lock().unwrap();
    g.sender_count += 1;
    drop(g);
    Sender { inner: self.inner.clone() }
  }
}

impl<T> Drop for Sender<T> {
  fn drop(&mut self) {
    let mut g = self.inner.lock().unwrap();
    g.sender_count -= 1;
    if g.sender_count == 0 {
      let w = wake_rx_bounded(&mut g);
      drop(g);
      if let Some(w) = w {
        w.wake();
      }
    }
  }
}

pub struct Send<'a, T> {
  tx: &'a Sender<T>,
  value: Option<T>,
  id: u64,
  parked: bool,
  completed: bool,
}

impl<'a, T> Future for Send<'a, T> {
  type Output = Result<(), SendError<T>>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = unsafe { self.get_unchecked_mut() };
    let mut g = this.tx.inner.lock().unwrap();
    loop {
      if g.rx_closed {
        return Poll::Ready(Err(SendError(this.value.take().unwrap())));
      }
      if g.ckernel.try_push() {
        g.buffer.push_back(this.value.take().unwrap());
        if this.parked {
          // Completed directly while (possibly) still parked: withdraw so a
          // later wake hint is not consumed by this finished waiter.
          remove_tx_waiter(&mut g, this.id);
        }
        this.completed = true;
        let w = wake_rx_bounded(&mut g);
        drop(g);
        if let Some(w) = w {
          w.wake();
        }
        return Poll::Ready(Ok(()));
      }
      // Full: still parked from a previous poll — refresh the stored waker.
      if this.parked && g.tx_wakers.iter().any(|(wid, _)| *wid == this.id) {
        let id = this.id;
        if let Some(pos) = g.tx_wakers.iter().position(|(wid, _)| *wid == id) {
          g.tx_wakers[pos].1 = cx.waker().clone();
        }
        return Poll::Pending;
      }
      // Park (once per park-episode): the kernel decides Ready vs Park.
      let id = g.tx_next_id;
      g.tx_next_id += 1;
      match g.tx_kernel.wait_step(id) {
        WaitAction::Ready => {
          // Kernel consumed a stored slot hint instead of enqueuing us
          // (unreachable under U2's drain-only tx wakes, handled mechanically):
          // we are NOT parked, so re-attempt the push fast path.
          continue;
        }
        WaitAction::Park(_) => {
          this.id = id;
          g.tx_wakers.push((id, cx.waker().clone()));
          this.parked = true;
          return Poll::Pending;
        }
      }
    }
  }
}

impl<'a, T> Drop for Send<'a, T> {
  fn drop(&mut self) {
    drop_tx_waiter(&self.tx.inner, self.id, self.parked, self.completed);
  }
}

impl<T> Receiver<T> {
  pub fn recv(&mut self) -> Recv<'_, T> {
    Recv { rx: self, id: 0, parked: false }
  }

  pub fn try_recv(&mut self) -> Result<T, ()> {
    let mut g = self.inner.lock().unwrap();
    if g.ckernel.pop() {
      let value = g.buffer.pop_front().unwrap();
      let w = wake_one_tx_bounded(&mut g);
      drop(g);
      if let Some(w) = w {
        w.wake();
      }
      Ok(value)
    } else {
      Err(())
    }
  }

  pub fn close(&mut self) {
    let mut g = self.inner.lock().unwrap();
    g.rx_closed = true;
    let wakers: Vec<Waker> = std::mem::take(&mut g.tx_wakers).into_iter().map(|(_, w)| w).collect();
    drop(g);
    for w in wakers {
      w.wake();
    }
  }
}

impl<T> Drop for Receiver<T> {
  fn drop(&mut self) {
    self.close();
  }
}

pub struct Recv<'a, T> {
  rx: &'a mut Receiver<T>,
  id: u64,
  parked: bool,
}

impl<'a, T> Future for Recv<'a, T> {
  type Output = Option<T>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = self.get_mut();
    let mut g = this.rx.inner.lock().unwrap();
    loop {
      if g.ckernel.pop() {
        let value = g.buffer.pop_front().unwrap();
        let w = wake_one_tx_bounded(&mut g);
        drop(g);
        if let Some(w) = w {
          w.wake();
        }
        return Poll::Ready(Some(value));
      }
      if g.sender_count == 0 {
        return Poll::Ready(None);
      }
      if this.parked {
        break;
      }
      let id = g.rx_next_id;
      g.rx_next_id += 1;
      match g.rx_kernel.wait_step(id) {
        WaitAction::Ready => {
          // Kernel consumed a stored rx wake hint (a value was produced while
          // no receiver was parked; per U2 rx permits can accumulate). Ready
          // means we are NOT enqueued — re-attempt the pop instead of parking.
          continue;
        }
        WaitAction::Park(_) => {
          this.id = id;
          this.parked = true;
          break;
        }
      }
    }
    g.rx_waker = Some(cx.waker().clone());
    Poll::Pending
  }
}

impl<'a, T> Drop for Recv<'a, T> {
  fn drop(&mut self) {
    if !self.parked {
      return;
    }
    // Withdraw the parked receiver. No forwarding needed: the consumer is
    // single (recv takes &mut Receiver), so no other rx waiter exists, and a
    // delivered-but-unpolled value simply stays in the buffer for the next recv.
    let mut g = self.rx.inner.lock().unwrap();
    let _ = g.rx_kernel.remove_step(self.id);
    g.rx_waker = None;
  }
}

// ── Unbounded ── (a ChannelKernel with effectively unbounded capacity)
struct UnboundedInner<T> {
  rx_kernel: WaiterKernel,
  ckernel: ChannelKernel,
  buffer: VecDeque<T>,
  rx_waker: Option<Waker>,
  sender_count: usize,
  rx_closed: bool,
  rx_next_id: u64,
}

pub struct UnboundedSender<T> {
  inner: Arc<Mutex<UnboundedInner<T>>>,
}

pub struct UnboundedReceiver<T> {
  inner: Arc<Mutex<UnboundedInner<T>>>,
}

pub fn unbounded_channel<T>() -> (UnboundedSender<T>, UnboundedReceiver<T>) {
  let inner = Arc::new(Mutex::new(UnboundedInner {
    rx_kernel: WaiterKernel::new(),
    ckernel: ChannelKernel::new(u64::MAX),
    buffer: VecDeque::new(),
    rx_waker: None,
    sender_count: 1,
    rx_closed: false,
    rx_next_id: 0,
  }));
  (UnboundedSender { inner: inner.clone() }, UnboundedReceiver { inner })
}

fn wake_rx_unbounded<T>(g: &mut UnboundedInner<T>) -> Option<Waker> {
  let _ = g.rx_kernel.signal_step(0);
  g.rx_waker.take()
}

impl<T> UnboundedSender<T> {
  pub fn send(&self, value: T) -> Result<(), SendError<T>> {
    let mut g = self.inner.lock().unwrap();
    if g.rx_closed {
      return Err(SendError(value));
    }
    let _ = g.ckernel.try_push();
    g.buffer.push_back(value);
    let w = wake_rx_unbounded(&mut g);
    drop(g);
    if let Some(w) = w {
      w.wake();
    }
    Ok(())
  }

  pub fn is_closed(&self) -> bool {
    self.inner.lock().unwrap().rx_closed
  }
}

impl<T> Clone for UnboundedSender<T> {
  fn clone(&self) -> Self {
    let mut g = self.inner.lock().unwrap();
    g.sender_count += 1;
    drop(g);
    UnboundedSender { inner: self.inner.clone() }
  }
}

impl<T> Drop for UnboundedSender<T> {
  fn drop(&mut self) {
    let mut g = self.inner.lock().unwrap();
    g.sender_count -= 1;
    if g.sender_count == 0 {
      let w = wake_rx_unbounded(&mut g);
      drop(g);
      if let Some(w) = w {
        w.wake();
      }
    }
  }
}

impl<T> UnboundedReceiver<T> {
  pub fn recv(&mut self) -> UnboundedRecv<'_, T> {
    UnboundedRecv { rx: self, id: 0, parked: false }
  }

  pub fn try_recv(&mut self) -> Result<T, ()> {
    let mut g = self.inner.lock().unwrap();
    if g.ckernel.pop() {
      Ok(g.buffer.pop_front().unwrap())
    } else {
      Err(())
    }
  }

  pub fn close(&mut self) {
    let mut g = self.inner.lock().unwrap();
    g.rx_closed = true;
  }
}

impl<T> Drop for UnboundedReceiver<T> {
  fn drop(&mut self) {
    self.close();
  }
}

pub struct UnboundedRecv<'a, T> {
  rx: &'a mut UnboundedReceiver<T>,
  id: u64,
  parked: bool,
}

impl<'a, T> Future for UnboundedRecv<'a, T> {
  type Output = Option<T>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = self.get_mut();
    let mut g = this.rx.inner.lock().unwrap();
    loop {
      if g.ckernel.pop() {
        return Poll::Ready(Some(g.buffer.pop_front().unwrap()));
      }
      if g.sender_count == 0 {
        return Poll::Ready(None);
      }
      if this.parked {
        break;
      }
      let id = g.rx_next_id;
      g.rx_next_id += 1;
      match g.rx_kernel.wait_step(id) {
        WaitAction::Ready => {
          // Stored rx wake hint consumed (value produced with no parked
          // receiver): NOT enqueued — re-attempt the pop instead of parking.
          continue;
        }
        WaitAction::Park(_) => {
          this.id = id;
          this.parked = true;
          break;
        }
      }
    }
    g.rx_waker = Some(cx.waker().clone());
    Poll::Pending
  }
}

impl<'a, T> Drop for UnboundedRecv<'a, T> {
  fn drop(&mut self) {
    if !self.parked {
      return;
    }
    // Same as the bounded Recv: single consumer, nothing to forward.
    let mut g = self.rx.inner.lock().unwrap();
    let _ = g.rx_kernel.remove_step(self.id);
    g.rx_waker = None;
  }
}
