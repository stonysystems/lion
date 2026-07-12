// Trusted glue: broadcast (multi-producer, multi-consumer ring buffer). Each
// receiver tracks its own seq cursor; a send appends a slot and wakes every
// parked receiver. The wake protocol is the verified WaiterKernel (receiver parks
// → PassWaker; send drains the queue → one WakeWaker each). The ring buffer + seq
// cursors + closed flag are data-glue. verus::trusted under Verus, plain Rust
// under cargo.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::sync::broadcast_kernel::{BRecv, BroadcastKernel};
use crate::sync::waiter::kernel::{SignalAction, WaitAction, WaiterKernel};
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};

#[derive(Debug)]
pub struct SendError<T>(pub T);

#[derive(Debug, Clone)]
pub enum RecvError {
  Closed,
  Lagged(u64),
}

impl std::fmt::Display for RecvError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      RecvError::Closed => write!(f, "channel closed"),
      RecvError::Lagged(n) => write!(f, "lagged by {n}"),
    }
  }
}

impl std::error::Error for RecvError {}

struct Slot<T> {
  value: T,
  seq: u64,
}

struct BroadcastInner<T> {
  rx_kernel: WaiterKernel,
  bkern: BroadcastKernel,
  buffer: VecDeque<Slot<T>>,
  waiters: Vec<(u64, Waker)>,
  closed: bool,
  next_id: u64,
  sender_count: usize,
}

pub struct Sender<T> {
  inner: Arc<Mutex<BroadcastInner<T>>>,
}

pub struct Receiver<T> {
  inner: Arc<Mutex<BroadcastInner<T>>>,
  next_seq: u64,
}

pub fn channel<T: Clone>(capacity: usize) -> (Sender<T>, Receiver<T>) {
  assert!(capacity > 0, "broadcast channel capacity must be > 0");
  let inner = Arc::new(Mutex::new(BroadcastInner {
    rx_kernel: WaiterKernel::new(),
    bkern: BroadcastKernel::new(capacity as u64),
    buffer: VecDeque::with_capacity(capacity),
    waiters: Vec::new(),
    closed: false,
    next_id: 0,
    sender_count: 1,
  }));
  (Sender { inner: inner.clone() }, Receiver { inner, next_seq: 0 })
}

fn wake_all<T>(g: &mut BroadcastInner<T>) -> Vec<Waker> {
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

impl<T: Clone> Sender<T> {
  pub fn send(&self, value: T) -> Result<usize, SendError<T>> {
    let mut g = self.inner.lock().unwrap();
    if g.closed {
      return Err(SendError(value));
    }
    let seq = g.bkern.send_step();
    if g.buffer.len() == g.bkern.capacity as usize {
      g.buffer.pop_front();
    }
    g.buffer.push_back(Slot { value, seq });
    let receiver_count = Arc::strong_count(&self.inner) - 1;
    let wakers = wake_all(&mut g);
    drop(g);
    for w in wakers {
      w.wake();
    }
    Ok(receiver_count)
  }

  pub fn subscribe(&self) -> Receiver<T> {
    let g = self.inner.lock().unwrap();
    let next_seq = g.bkern.next_seq;
    drop(g);
    Receiver { inner: self.inner.clone(), next_seq }
  }

  pub fn receiver_count(&self) -> usize {
    Arc::strong_count(&self.inner) - 1
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
      g.closed = true;
      let wakers = wake_all(&mut g);
      drop(g);
      for w in wakers {
        w.wake();
      }
    }
  }
}

impl<T: Clone> Receiver<T> {
  pub fn recv(&mut self) -> Recv<'_, T> {
    Recv { rx: self, id: 0, parked: false }
  }

  pub fn try_recv(&mut self) -> Result<T, RecvError> {
    let g = self.inner.lock().unwrap();
    match g.bkern.recv_step(self.next_seq) {
      BRecv::Lagged { skipped, new_cursor } => {
        self.next_seq = new_cursor;
        Err(RecvError::Lagged(skipped))
      }
      BRecv::Ready { seq } => {
        let mut val = None;
        for slot in g.buffer.iter() {
          if slot.seq == seq {
            val = Some(slot.value.clone());
            break;
          }
        }
        self.next_seq = seq + 1;
        Ok(val.unwrap())
      }
      BRecv::Park => Err(RecvError::Closed),
    }
  }

  pub fn resubscribe(&self) -> Receiver<T> {
    let g = self.inner.lock().unwrap();
    let next_seq = g.bkern.next_seq;
    drop(g);
    Receiver { inner: self.inner.clone(), next_seq }
  }
}

impl<T: Clone> Clone for Receiver<T> {
  fn clone(&self) -> Self {
    Receiver { inner: self.inner.clone(), next_seq: self.next_seq }
  }
}

pub struct Recv<'a, T> {
  rx: &'a mut Receiver<T>,
  id: u64,
  parked: bool,
}

impl<'a, T: Clone> Future for Recv<'a, T> {
  type Output = Result<T, RecvError>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = self.get_mut();
    let mut g = this.rx.inner.lock().unwrap();

    loop {
    match g.bkern.recv_step(this.rx.next_seq) {
      BRecv::Lagged { skipped, new_cursor } => {
        this.rx.next_seq = new_cursor;
        return Poll::Ready(Err(RecvError::Lagged(skipped)));
      }
      BRecv::Ready { seq } => {
        let mut val = None;
        for slot in g.buffer.iter() {
          if slot.seq == seq {
            val = Some(slot.value.clone());
            break;
          }
        }
        this.rx.next_seq = seq + 1;
        return Poll::Ready(Ok(val.unwrap()));
      }
      BRecv::Park => {}
    }

    if g.closed {
      return Poll::Ready(Err(RecvError::Closed));
    }

    if !this.parked {
      this.id = g.next_id;
      g.next_id += 1;
      match g.rx_kernel.wait_step(this.id) {
        // Stale stored permit consumed (unreachable under drain-only wake_all,
        // handled mechanically per F2): not enqueued — re-check the ring.
        WaitAction::Ready => continue,
        WaitAction::Park(_) => {
          g.waiters.push((this.id, cx.waker().clone()));
          this.parked = true;
        }
      }
    } else {
      let id = this.id;
      if let Some(pos) = g.waiters.iter().position(|(wid, _)| *wid == id) {
        g.waiters[pos].1 = cx.waker().clone();
      }
    }
    return Poll::Pending;
    }
  }
}

// Cancellation tidy (F3 pattern): a parked Recv dropped before its wake
// withdraws from the kernel queue and the waiter map. No forwarding needed —
// broadcast wakes drain the whole queue, so no permit can be lost; this only
// prevents a stale-waker wake for the dead id.
impl<'a, T> Drop for Recv<'a, T> {
  fn drop(&mut self) {
    if !self.parked {
      return;
    }
    if let Ok(mut g) = self.rx.inner.lock() {
      let _ = g.rx_kernel.remove_step(self.id);
      let id = self.id;
      if let Some(pos) = g.waiters.iter().position(|(wid, _)| *wid == id) {
        g.waiters.remove(pos);
      }
    }
  }
}
