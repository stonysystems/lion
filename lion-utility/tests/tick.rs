// Runtime::tick / tick_with_timeout: an embedder drives the runtime from its
// own loop. A tick runs one iteration of block_on's loop; when idle it parks
// for at most its bound (100 ms for tick), cut short by timers and wakes.
// Kept in its own test binary: it measures wall-clock time.

use lion_executor::{spawn, spawn_local, Runtime};
use lion_utility::time::sleep;
use std::future::Future;
use std::pin::Pin;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll, Waker};
use std::time::{Duration, Instant};

fn poll_now<F: Future + Unpin>(f: &mut F) -> Poll<F::Output> {
  Pin::new(f).poll(&mut Context::from_waker(Waker::noop()))
}

// Ticks until `done`, failing after 5 s.
fn tick_until(rt: &Runtime, done: &AtomicBool, step: impl Fn(&Runtime)) -> usize {
  let t0 = Instant::now();
  let mut ticks = 0;
  while !done.load(Ordering::SeqCst) {
    assert!(t0.elapsed() < Duration::from_secs(5), "tick loop made no progress in 5 s ({} ticks)", ticks);
    step(rt);
    ticks += 1;
  }
  ticks
}

#[test]
fn tick_drives_spawned_tasks_to_completion() {
  let rt = Runtime::new().expect("runtime");
  let done = Arc::new(AtomicBool::new(false));
  let d = done.clone();
  // A timer, a nested spawn and a foreign-thread wake inside the task.
  let mut task = rt.handle().spawn(async move {
    sleep(Duration::from_millis(20)).await;
    let nested = spawn(async { 40u32 }).await.expect("nested");
    let (tx, rx) = std::sync::mpsc::channel::<u32>();
    let flag = Arc::new(AtomicBool::new(false));
    let f2 = flag.clone();
    std::thread::spawn(move || {
      std::thread::sleep(Duration::from_millis(10));
      tx.send(2).unwrap();
      f2.store(true, Ordering::SeqCst);
    });
    while !flag.load(Ordering::SeqCst) {
      sleep(Duration::from_millis(1)).await;
    }
    d.store(true, Ordering::SeqCst);
    nested + rx.recv().unwrap()
  });
  let local_done = Rc::new(std::cell::Cell::new(false));
  let ld = local_done.clone();
  let mut local = rt.handle().spawn_local(async move {
    sleep(Duration::from_millis(5)).await;
    ld.set(true);
  });
  let ticks = tick_until(&rt, &done, |rt| rt.tick());
  assert!(ticks >= 2, "one tick cannot have covered a 20 ms sleep");
  match poll_now(&mut task) {
    Poll::Ready(Ok(v)) => assert_eq!(v, 42),
    other => panic!("task not resolved after its body finished: {:?}", other.map(|r| r.is_ok())),
  }
  // The local task's 5 ms sleep ended long before; one more tick at most.
  rt.tick_with_timeout(Duration::ZERO);
  assert!(local_done.get());
  assert!(matches!(poll_now(&mut local), Poll::Ready(Ok(()))));
}

#[test]
fn idle_tick_parks_for_at_most_its_bound() {
  let rt = Runtime::new().expect("runtime");
  // Settle: consume any wake left over from construction.
  rt.tick_with_timeout(Duration::ZERO);
  rt.tick_with_timeout(Duration::ZERO);

  let t0 = Instant::now();
  for _ in 0..100 {
    rt.tick_with_timeout(Duration::ZERO);
  }
  let zero = t0.elapsed();
  assert!(zero < Duration::from_millis(50), "100 non-blocking ticks took {:?}", zero);

  let t0 = Instant::now();
  rt.tick_with_timeout(Duration::from_millis(15));
  let bounded = t0.elapsed();
  assert!(bounded >= Duration::from_millis(12) && bounded < Duration::from_millis(80), "15 ms idle tick took {:?}", bounded);

  let t0 = Instant::now();
  rt.tick();
  let default = t0.elapsed();
  assert!(default >= Duration::from_millis(60) && default < Duration::from_millis(1000), "idle tick took {:?}", default);

  // A timer due sooner cuts a long bound short.
  let done = Arc::new(AtomicBool::new(false));
  let d = done.clone();
  let _t = rt.handle().spawn(async move {
    sleep(Duration::from_millis(10)).await;
    d.store(true, Ordering::SeqCst);
  });
  let t0 = Instant::now();
  tick_until(&rt, &done, |rt| rt.tick_with_timeout(Duration::from_secs(10)));
  assert!(t0.elapsed() < Duration::from_secs(1), "a 10 ms timer waited {:?}", t0.elapsed());

  // A spawn from another thread interrupts a long idle park.
  let done = Arc::new(AtomicBool::new(false));
  let d = done.clone();
  let handle = rt.handle().clone();
  let spawner = std::thread::spawn(move || {
    std::thread::sleep(Duration::from_millis(20));
    let _ = handle.spawn(async move { d.store(true, Ordering::SeqCst) });
  });
  let t0 = Instant::now();
  tick_until(&rt, &done, |rt| rt.tick_with_timeout(Duration::from_secs(10)));
  assert!(t0.elapsed() < Duration::from_secs(1), "a foreign spawn waited {:?}", t0.elapsed());
  spawner.join().unwrap();
}

#[test]
fn tick_is_not_reentrant() {
  let rt = Rc::new(Runtime::new().expect("runtime"));
  let inside_block_on = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| rt.block_on(async { rt.tick() })));
  assert!(inside_block_on.is_err(), "tick inside block_on must panic");
  let r = rt.clone();
  let in_task = rt.block_on(spawn_local(async move { r.tick() }));
  assert!(in_task.expect_err("tick inside a task must panic").is_panic());
  // The runtime still works afterwards.
  assert_eq!(rt.block_on(spawn(async { 1u32 })).expect("runtime broke"), 1);
}
