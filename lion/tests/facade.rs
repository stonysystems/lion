// The lion facade's tokio-shaped task surface: spawn_local and LocalSet accept
// futures that are not Send and run them on the runtime's thread.

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
