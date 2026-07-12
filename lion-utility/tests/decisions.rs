// U3 decision-consumption regressions: glue must consume verified kernel
// decisions instead of discarding them. Futures are driven
// manually with a noop waker — no runtime needed.

use lion_utility::sync::{broadcast, mpsc, oneshot, watch};
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

fn poll_once<F: Future + ?Sized>(f: &mut Pin<Box<F>>) -> Poll<F::Output> {
  let mut cx = Context::from_waker(Waker::noop());
  f.as_mut().poll(&mut cx)
}

// ── Step 1: mpsc consumes wait_step decisions ──

// A stale rx wake hint (stored permit from a send that arrived while no
// receiver was parked, then consumed by try_recv) makes rx_kernel.wait_step
// return Ready. The glue must consume that decision (re-attempt the pop, do
// not treat itself as parked) and still end up genuinely parked + wakeable.
#[test]
fn mpsc_recv_drains_stale_wake_hint_then_parks() {
  let (tx, mut rx) = mpsc::channel::<u32>(2);
  tx.try_send(1).unwrap(); // stores an rx wake hint (no receiver parked)
  assert_eq!(rx.try_recv().unwrap(), 1); // value consumed; hint is now stale
  let mut r = Box::pin(rx.recv());
  assert!(poll_once(&mut r).is_pending()); // Ready hint consumed, then parked
  tx.try_send(2).unwrap(); // must reach the (actually parked) receiver
  assert!(matches!(poll_once(&mut r), Poll::Ready(Some(2))));
}

// Same for the unbounded receiver.
#[test]
fn mpsc_unbounded_recv_drains_stale_wake_hint_then_parks() {
  let (tx, mut rx) = mpsc::unbounded_channel::<u32>();
  tx.send(1).unwrap();
  assert_eq!(rx.try_recv().unwrap(), 1);
  let mut r = Box::pin(rx.recv());
  assert!(poll_once(&mut r).is_pending());
  tx.send(2).unwrap();
  assert!(matches!(poll_once(&mut r), Poll::Ready(Some(2))));
}

// With capacity available, send and recv complete on first poll — no parking.
#[test]
fn mpsc_ping_pong_no_park_when_capacity_available() {
  let (tx, mut rx) = mpsc::channel::<u32>(1);
  for i in 0..3u32 {
    let mut s = Box::pin(tx.send(i));
    assert!(matches!(poll_once(&mut s), Poll::Ready(Ok(()))));
    drop(s);
    let mut r = Box::pin(rx.recv());
    assert!(matches!(poll_once(&mut r), Poll::Ready(Some(v)) if v == i));
  }
}

// Full-channel send parks, is woken by a recv, and completes on repoll (the
// Park decision path plus wake routing stays intact after the rewrite).
#[test]
fn mpsc_send_parks_then_completes_after_recv() {
  let (tx, mut rx) = mpsc::channel::<u32>(1);
  tx.try_send(1).unwrap();
  let mut s = Box::pin(tx.send(2));
  assert!(poll_once(&mut s).is_pending());
  assert_eq!(rx.try_recv().unwrap(), 1);
  assert!(matches!(poll_once(&mut s), Poll::Ready(Ok(()))));
  assert_eq!(rx.try_recv().unwrap(), 2);
}

// ── Step 2: oneshot routed through the WaiterKernel ──

#[test]
fn oneshot_send_then_poll() {
  let (tx, rx) = oneshot::channel::<u32>();
  tx.send(7).unwrap();
  let mut r = Box::pin(rx);
  assert!(matches!(poll_once(&mut r), Poll::Ready(Ok(7))));
}

#[test]
fn oneshot_poll_then_send_wakes() {
  let (tx, rx) = oneshot::channel::<u32>();
  let mut r = Box::pin(rx);
  assert!(poll_once(&mut r).is_pending()); // parked via the WaiterKernel
  tx.send(9).unwrap(); // signal_step routes the wake to the parked receiver
  assert!(matches!(poll_once(&mut r), Poll::Ready(Ok(9))));
}

#[test]
fn oneshot_receiver_drop_then_send_does_not_panic() {
  let (tx, rx) = oneshot::channel::<u32>();
  drop(rx);
  assert_eq!(tx.send(1), Err(1));
}

#[test]
fn oneshot_parked_receiver_drop_then_send_does_not_panic() {
  let (tx, rx) = oneshot::channel::<u32>();
  let mut r = Box::pin(rx);
  assert!(poll_once(&mut r).is_pending());
  drop(r); // parked receiver withdrawn (kernel remove_step + waker slot tidy)
  assert_eq!(tx.send(1), Err(1));
}

#[test]
fn oneshot_sender_drop_wakes_receiver_with_err() {
  let (tx, rx) = oneshot::channel::<u32>();
  let mut r = Box::pin(rx);
  assert!(poll_once(&mut r).is_pending());
  drop(tx);
  assert!(matches!(poll_once(&mut r), Poll::Ready(Err(_))));
}

// ── Step 2: watch Changed still parks/wakes after decision consumption ──

#[test]
fn watch_changed_parks_then_sees_send() {
  let (tx, mut rx) = watch::channel(0u32);
  let mut c = Box::pin(rx.changed());
  assert!(poll_once(&mut c).is_pending());
  tx.send(1).unwrap();
  assert!(matches!(poll_once(&mut c), Poll::Ready(Ok(()))));
  drop(c);
  assert_eq!(*rx.borrow(), 1);
}

// ── Step 4: broadcast rejects capacity 0 ──

#[test]
#[should_panic(expected = "broadcast channel capacity must be > 0")]
fn broadcast_capacity_zero_panics() {
  let _ = broadcast::channel::<u32>(0);
}
