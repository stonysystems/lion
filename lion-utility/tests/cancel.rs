// U2 cancellation-safety regressions: dropping a waiting future must withdraw
// its parked waiter (kernel remove_step) and forward an already-delivered
// one-shot grant instead of swallowing it. Futures are driven manually with a
// noop waker — no runtime needed.

use lion_utility::sync::{mpsc, watch, Mutex, Notify, Semaphore};
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

fn poll_once<F: Future + ?Sized>(f: &mut Pin<Box<F>>) -> Poll<F::Output> {
  let mut cx = Context::from_waker(Waker::noop());
  f.as_mut().poll(&mut cx)
}

// (a) A cancelled parked mutex.lock() must not deadlock the mutex.
#[test]
fn cancelled_mutex_lock_does_not_deadlock() {
  let m = Mutex::new(0u32);
  let mut a = Box::pin(m.lock());
  let guard = match poll_once(&mut a) {
    Poll::Ready(g) => g,
    Poll::Pending => panic!("uncontended lock must be ready"),
  };
  let mut b = Box::pin(m.lock());
  assert!(poll_once(&mut b).is_pending());
  drop(b); // cancel B while parked
  drop(guard); // A unlocks
  let mut c = Box::pin(m.lock());
  assert!(matches!(poll_once(&mut c), Poll::Ready(_)), "mutex deadlocked by cancelled waiter");
}

// (a') Same for the owned variant (its Drop path is separate from Acquire's).
#[test]
fn cancelled_lock_owned_does_not_deadlock() {
  let m = std::sync::Arc::new(Mutex::new(0u32));
  let mut a = Box::pin(m.clone().lock_owned());
  let guard = match poll_once(&mut a) {
    Poll::Ready(g) => g,
    Poll::Pending => panic!("uncontended lock must be ready"),
  };
  let mut b = Box::pin(m.clone().lock_owned());
  assert!(poll_once(&mut b).is_pending());
  drop(b);
  drop(guard);
  let mut c = Box::pin(m.clone().lock_owned());
  assert!(matches!(poll_once(&mut c), Poll::Ready(_)));
}

// (b) A dropped parked Notified must not swallow a later notify_one.
#[test]
fn dropped_notified_does_not_swallow_notify_one() {
  let n = Notify::new();
  let mut w1 = Box::pin(n.notified());
  let mut w2 = Box::pin(n.notified());
  assert!(poll_once(&mut w1).is_pending());
  assert!(poll_once(&mut w2).is_pending());
  drop(w1); // cancel the head waiter
  n.notify_one();
  assert!(matches!(poll_once(&mut w2), Poll::Ready(())), "notification swallowed by dead waiter");
}

// (c) A dropped parked Acquire must not swallow a later released permit.
#[test]
fn dropped_acquire_does_not_swallow_permit() {
  let s = Semaphore::new(0);
  let mut a1 = Box::pin(s.acquire());
  assert!(poll_once(&mut a1).is_pending());
  drop(a1);
  s.add_permits(1);
  let mut a2 = Box::pin(s.acquire());
  assert!(matches!(poll_once(&mut a2), Poll::Ready(Ok(_))), "permit swallowed by dead waiter");
}

// (d) Signal-then-drop forwarding: a permit granted to a waiter that is dropped
// before ever being polled must be forwarded to the next waiter.
#[test]
fn granted_then_dropped_acquire_forwards_permit() {
  let s = Semaphore::new(0);
  let mut w1 = Box::pin(s.acquire());
  let mut w2 = Box::pin(s.acquire());
  assert!(poll_once(&mut w1).is_pending());
  assert!(poll_once(&mut w2).is_pending());
  s.add_permits(1); // grants w1 (dequeued + flagged), never polled
  drop(w1); // must forward the permit to w2
  let permit = match poll_once(&mut w2) {
    Poll::Ready(Ok(p)) => p,
    _ => panic!("granted permit lost on drop"),
  };
  assert_eq!(s.available_permits(), 0); // exactly the one forwarded permit, held
  drop(permit);
  assert_eq!(s.available_permits(), 1);
}

// (d') Same forwarding for Notify: notify_one delivered to w1, w1 dropped
// unpolled — w2 must receive the notification.
#[test]
fn notified_then_dropped_forwards_notification() {
  let n = Notify::new();
  let mut w1 = Box::pin(n.notified());
  let mut w2 = Box::pin(n.notified());
  assert!(poll_once(&mut w1).is_pending());
  assert!(poll_once(&mut w2).is_pending());
  n.notify_one(); // delivered to w1
  drop(w1); // never polled — must forward to w2
  assert!(matches!(poll_once(&mut w2), Poll::Ready(())), "notification lost on drop");
}

// notify_waiters is a broadcast: a woken-then-dropped waiter must NOT forward
// (that would leave a phantom stored permit completing a future notified()).
#[test]
fn notify_waiters_drop_does_not_leak_permit() {
  let n = Notify::new();
  let mut w1 = Box::pin(n.notified());
  assert!(poll_once(&mut w1).is_pending());
  n.notify_waiters();
  drop(w1); // woken by broadcast, never polled — nothing to forward
  let mut w2 = Box::pin(n.notified());
  assert!(poll_once(&mut w2).is_pending(), "broadcast drop leaked a stored permit");
}

// A normally completed waiter's drop must not fabricate a notification.
#[test]
fn completed_notified_drop_is_inert() {
  let n = Notify::new();
  let mut w1 = Box::pin(n.notified());
  assert!(poll_once(&mut w1).is_pending());
  n.notify_one();
  assert!(matches!(poll_once(&mut w1), Poll::Ready(()))); // consumed normally
  drop(w1);
  let mut w2 = Box::pin(n.notified());
  assert!(poll_once(&mut w2).is_pending(), "completed waiter forwarded a phantom notification");
}

// mpsc: a woken-but-dropped bounded sender must forward the slot-free hint to
// the next parked sender (and a cancelled parked sender must not swallow it).
#[test]
fn mpsc_cancelled_send_forwards_slot_hint() {
  let (tx, mut rx) = mpsc::channel::<u32>(1);
  tx.try_send(1).unwrap(); // full
  let mut s1 = Box::pin(tx.send(2));
  let mut s2 = Box::pin(tx.send(3));
  assert!(poll_once(&mut s1).is_pending());
  assert!(poll_once(&mut s2).is_pending());
  assert_eq!(rx.try_recv().unwrap(), 1); // frees a slot, wake hint goes to s1
  drop(s1); // never polled — hint must pass to s2
  assert!(matches!(poll_once(&mut s2), Poll::Ready(Ok(()))), "slot hint lost on drop");
  assert_eq!(rx.try_recv().unwrap(), 3);
}

#[test]
fn mpsc_dropped_parked_send_does_not_swallow_wakeup() {
  let (tx, mut rx) = mpsc::channel::<u32>(1);
  tx.try_send(1).unwrap();
  let mut s1 = Box::pin(tx.send(2));
  let mut s2 = Box::pin(tx.send(3));
  assert!(poll_once(&mut s1).is_pending());
  assert!(poll_once(&mut s2).is_pending());
  drop(s1); // cancelled while parked
  assert_eq!(rx.try_recv().unwrap(), 1); // wake hint must reach s2, not dead s1
  assert!(matches!(poll_once(&mut s2), Poll::Ready(Ok(()))));
  assert_eq!(rx.try_recv().unwrap(), 3);
}

// mpsc: a cancelled parked Recv leaves the channel usable for the next recv.
#[test]
fn mpsc_cancelled_recv_is_clean() {
  let (tx, mut rx) = mpsc::channel::<u32>(1);
  {
    let mut r = Box::pin(rx.recv());
    assert!(poll_once(&mut r).is_pending());
  } // r dropped while parked
  tx.try_send(7).unwrap();
  let mut r2 = Box::pin(rx.recv());
  assert!(matches!(poll_once(&mut r2), Poll::Ready(Some(7))));
}

// watch: a cancelled parked Changed is withdrawn; a later change still reaches
// a fresh Changed.
#[test]
fn watch_cancelled_changed_is_clean() {
  let (tx, mut rx) = watch::channel(0u32);
  {
    let mut c1 = Box::pin(rx.changed());
    assert!(poll_once(&mut c1).is_pending());
  } // c1 dropped while parked
  tx.send(1).unwrap();
  let mut c2 = Box::pin(rx.changed());
  assert!(matches!(poll_once(&mut c2), Poll::Ready(Ok(()))));
}
