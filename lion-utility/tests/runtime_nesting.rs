// One Lion runtime per thread. A second Runtime::new on a thread whose runtime
// is alive must fail without touching that runtime's thread-local state; the
// failed attempt's drop must not disturb it either. Before this, the second
// runtime overwrote the thread's executor handle, cross-thread context and
// reactor pointer, and dropping it cleared them under the first runtime.

use lion_executor::{spawn, Runtime};
use lion_utility::time::{sleep, timeout};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Duration;

const BOUND: Duration = Duration::from_secs(5);

// Drives timers, a local spawn and a spawn from another thread on `rt`.
fn exercise(rt: &Runtime, tag: u32) -> u32 {
  let handle = rt.handle().clone();
  let from_thread = std::thread::spawn(move || handle.spawn(async move { tag + 1 })).join().unwrap();
  rt.block_on(async move {
    sleep(Duration::from_millis(3)).await;
    let a = timeout(BOUND, spawn(async move { tag })).await.expect("task hung").expect("task failed");
    let b = timeout(BOUND, from_thread).await.expect("foreign spawn hung").expect("failed");
    a + b
  })
}

#[test]
fn second_runtime_on_a_thread_is_refused_and_the_first_keeps_working() {
  let rt = Runtime::new().expect("runtime");
  assert_eq!(exercise(&rt, 1), 3);

  let second = Runtime::new();
  let refused = match &second {
    Err(e) => e.kind() == std::io::ErrorKind::AlreadyExists,
    Ok(_) => false,
  };
  drop(second);
  let still_works = catch_unwind(AssertUnwindSafe(|| exercise(&rt, 10)));
  assert!(
    matches!(still_works, Ok(21)),
    "the first runtime broke after a second Runtime::new on its thread"
  );
  assert!(refused, "a second Runtime::new on a thread with a live runtime must fail with AlreadyExists");

  // Refused from inside block_on and from inside a task as well.
  rt.block_on(async {
    assert!(Runtime::new().is_err());
    let in_task = spawn(async { Runtime::new().is_err() });
    assert!(timeout(BOUND, in_task).await.expect("hung").expect("failed"));
  });
  assert_eq!(exercise(&rt, 100), 201);

  // Another thread runs its own runtime independently.
  let other = std::thread::spawn(|| {
    let rt = Runtime::new().expect("runtime on another thread");
    exercise(&rt, 1000)
  })
  .join()
  .unwrap();
  assert_eq!(other, 2001);
  assert_eq!(exercise(&rt, 5), 11);

  // Once the first runtime is dropped, the thread can create a new one.
  drop(rt);
  let rt = Runtime::new().expect("a runtime after the previous one was dropped");
  assert_eq!(exercise(&rt, 7), 15);
}

// lion-reactor's guard clears the thread's current reactor only if it is still
// the one that guard entered; a Runtime refuses to start over an entered one.
#[test]
fn reactor_guard_clears_only_its_own_entry() {
  use lion_reactor::{IoResult, Reactor};
  let new_reactor = || match Reactor::new() {
    IoResult::Ok((r, _)) => r,
    IoResult::Err(_) => panic!("reactor"),
  };
  let mut a = new_reactor();
  let mut b = new_reactor();
  assert!(!Reactor::is_entered_on_current_thread());
  let guard_a = a.enter();
  assert!(Runtime::new().is_err(), "a Runtime must not start over an entered reactor");
  let guard_b = b.enter();
  drop(guard_a);
  assert!(Reactor::is_entered_on_current_thread(), "an old guard cleared a newer reactor's entry");
  drop(guard_b);
  assert!(!Reactor::is_entered_on_current_thread());
  let rt = Runtime::new().expect("runtime once no reactor is entered");
  assert_eq!(exercise(&rt, 2), 5);
}
