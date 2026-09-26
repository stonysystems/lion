// Panic isolation and cancellation. A task that panics finishes with a panic
// JoinError while the runtime keeps running; JoinHandle::abort drops the
// task's future on the runtime's thread and resolves the handle as cancelled;
// a task that is dropped unfinished (its runtime went away) resolves its handle
// as cancelled too. Every await of a JoinHandle is bounded by a timeout, so a
// regression fails instead of hanging.

use lion_executor::{spawn, spawn_blocking, JoinError, Runtime};
use lion_utility::time::{sleep, timeout};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::ThreadId;
use std::time::Duration;

const BOUND: Duration = Duration::from_secs(5);

// Records whether, and on which thread, it was dropped.
struct DropProbe {
  dropped: Arc<AtomicBool>,
  thread: Arc<Mutex<Option<ThreadId>>>,
}

impl Drop for DropProbe {
  fn drop(&mut self) {
    *self.thread.lock().unwrap() = Some(std::thread::current().id());
    self.dropped.store(true, Ordering::SeqCst);
  }
}

fn probe() -> (DropProbe, Arc<AtomicBool>, Arc<Mutex<Option<ThreadId>>>) {
  let dropped = Arc::new(AtomicBool::new(false));
  let thread = Arc::new(Mutex::new(None));
  (DropProbe { dropped: dropped.clone(), thread: thread.clone() }, dropped, thread)
}

fn panic_message(err: JoinError) -> String {
  assert!(err.is_panic(), "expected a panic JoinError, got {:?}", err);
  let payload = err.into_panic();
  if let Some(s) = payload.downcast_ref::<&'static str>() {
    s.to_string()
  } else {
    payload.downcast_ref::<String>().cloned().unwrap_or_default()
  }
}

#[test]
fn panicking_task_yields_panic_error_and_runtime_keeps_running() {
  let rt = Runtime::new().expect("runtime");
  rt.block_on(async {
    let (guard, dropped, _) = probe();
    // Panics on its second poll, with a live timer and a drop probe in scope.
    let bad = spawn(async move {
      let _guard = guard;
      let _pending_timer = sleep(Duration::from_secs(60));
      sleep(Duration::from_millis(5)).await;
      panic!("boom after a sleep");
    });
    let good = spawn(async {
      sleep(Duration::from_millis(20)).await;
      7u32
    });
    let bad = timeout(BOUND, bad).await.expect("panicked task's handle hung");
    assert_eq!(panic_message(bad.expect_err("a panicked task must not return Ok")), "boom after a sleep");
    assert!(dropped.load(Ordering::SeqCst), "panicked task's future was not dropped");
    let good = timeout(BOUND, good).await.expect("sibling task hung after a panic");
    assert_eq!(good.expect("sibling task failed"), 7);
    // The runtime still accepts and runs new work.
    let later = timeout(BOUND, spawn(async { 11u32 })).await.expect("new task hung");
    assert_eq!(later.expect("new task failed"), 11);
    // A panic on the very first poll is contained the same way.
    let first = timeout(BOUND, spawn(async { panic!("boom at once") })).await.expect("hung");
    assert_eq!(panic_message(first.map(|()| ()).expect_err("must fail")), "boom at once");
  });
}

#[test]
fn abort_drops_future_on_owner_thread_and_resolves_cancelled() {
  let rt = Runtime::new().expect("runtime");
  let owner = std::thread::current().id();
  rt.block_on(async move {
    let (guard, dropped, drop_thread) = probe();
    let polls = Arc::new(AtomicUsize::new(0));
    let polls2 = polls.clone();
    let task = spawn(async move {
      let _guard = guard;
      loop {
        polls2.fetch_add(1, Ordering::SeqCst);
        sleep(Duration::from_secs(60)).await;
      }
    });
    // Let the task start and park on its timer.
    sleep(Duration::from_millis(10)).await;
    assert_eq!(polls.load(Ordering::SeqCst), 1);
    assert!(!dropped.load(Ordering::SeqCst));
    task.abort();
    let joined = timeout(BOUND, task).await.expect("aborted task's handle hung");
    let err = joined.expect_err("an aborted task must not return Ok");
    assert!(err.is_cancelled(), "expected cancelled, got {:?}", err);
    assert!(dropped.load(Ordering::SeqCst), "aborted task's future was not dropped");
    assert_eq!(*drop_thread.lock().unwrap(), Some(owner), "future dropped off the runtime thread");
    assert_eq!(polls.load(Ordering::SeqCst), 1, "aborted future was polled again");
  });
}

#[test]
fn abort_before_first_poll_and_from_another_thread() {
  let rt = Runtime::new().expect("runtime");
  rt.block_on(async {
    // Aborted before the executor ever polled it: never polled, still resolves.
    let polled = Arc::new(AtomicBool::new(false));
    let polled2 = polled.clone();
    let (guard, dropped, _) = probe();
    let task = spawn(async move {
      let _guard = guard;
      polled2.store(true, Ordering::SeqCst);
    });
    task.abort();
    let err = timeout(BOUND, task).await.expect("hung").expect_err("must be cancelled");
    assert!(err.is_cancelled());
    assert!(!polled.load(Ordering::SeqCst), "aborted-before-start future was polled");
    assert!(dropped.load(Ordering::SeqCst));

    // Aborted from a foreign thread while parked: the wake crosses threads.
    let (guard, dropped, _) = probe();
    let task = spawn(async move {
      let _guard = guard;
      std::future::pending::<()>().await;
    });
    sleep(Duration::from_millis(10)).await;
    std::thread::scope(|s| {
      s.spawn(|| task.abort());
    });
    let err = timeout(BOUND, task).await.expect("hung").expect_err("must be cancelled");
    assert!(err.is_cancelled());
    assert!(dropped.load(Ordering::SeqCst));

    // Aborting a task that already finished keeps its result.
    let task = spawn(async { 5u32 });
    sleep(Duration::from_millis(10)).await;
    task.abort();
    assert_eq!(timeout(BOUND, task).await.expect("hung").expect("finished task lost its result"), 5);
  });
}

#[test]
fn handle_of_task_dropped_with_its_runtime_resolves_cancelled() {
  let (guard, dropped, _) = probe();
  let orphan = {
    let rt = Runtime::new().expect("runtime");
    rt.block_on(async move {
      let task = spawn(async move {
        let _guard = guard;
        std::future::pending::<()>().await;
      });
      sleep(Duration::from_millis(10)).await;
      task
    })
  };
  assert!(dropped.load(Ordering::SeqCst), "runtime drop did not drop the task's future");
  let rt = Runtime::new().expect("second runtime");
  let joined = rt.block_on(timeout(BOUND, orphan)).expect("orphaned handle hung");
  assert!(joined.expect_err("must be cancelled").is_cancelled());
}

#[test]
fn panicking_blocking_closure_yields_panic_error_and_pool_keeps_working() {
  let rt = Runtime::new().expect("runtime");
  rt.block_on(async {
    let workers = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    // Hit every worker with a panic, then check each still runs work.
    let mut bad = Vec::new();
    for i in 0..workers {
      bad.push(spawn_blocking(move || -> u32 { panic!("blocking boom {}", i) }));
    }
    for (i, h) in bad.into_iter().enumerate() {
      let err = timeout(BOUND, h).await.expect("panicked blocking handle hung").expect_err("must fail");
      assert_eq!(panic_message(err), format!("blocking boom {}", i));
    }
    let mut good = Vec::new();
    for i in 0..workers as u32 {
      good.push(spawn_blocking(move || i * 2));
    }
    for (i, h) in good.into_iter().enumerate() {
      let v = timeout(BOUND, h).await.expect("blocking pool stopped after a panic").expect("failed");
      assert_eq!(v, i as u32 * 2);
    }
  });
}
