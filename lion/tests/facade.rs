// The lion facade's tokio-shaped task surface: spawn_local and LocalSet accept
// futures that are not Send and run them on the runtime's thread; a nested
// runtime::Handle::block_on works inside task::block_in_place (a fresh thread)
// and is refused, without harm to the outer runtime, directly on its thread.

use std::rc::Rc;

#[test]
fn local_set_and_spawn_local_accept_non_send_futures() {
  let rt = lion::runtime::Builder::new_current_thread().build().expect("runtime");
  let local = lion::task::LocalSet::new();
  local.block_on(&rt, async {
    let rc = Rc::new(7u32);
    let via_set = local.spawn_local(async move { *rc + 1 });
    assert_eq!(via_set.await.expect("LocalSet task failed"), 8);
    let free = lion::task::spawn_local(async { Rc::new(9u32) });
    assert_eq!(*free.await.expect("spawn_local task failed"), 9);
    let run = local.run_until(async { Rc::new(10u32) }).await;
    assert_eq!(*run, 10);
  });
}

#[test]
fn nested_block_on_runs_inside_block_in_place_only() {
  let rt = lion::runtime::Builder::new_current_thread().build().expect("runtime");
  rt.block_on(async {
    let nested = lion::task::block_in_place(|| {
      lion::runtime::Handle::current().block_on(async { lion::spawn(async { 5u32 }).await.expect("nested task") })
    });
    assert_eq!(nested, 5);
    let direct = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      lion::runtime::Handle::current().block_on(async { 1u32 })
    }));
    assert!(direct.is_err(), "a nested runtime directly on a runtime thread must be refused");
    assert_eq!(lion::spawn(async { 6u32 }).await.expect("outer runtime broke"), 6);
  });
}
