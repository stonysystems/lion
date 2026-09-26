// spawn_local: a future that is not Send runs as a task on the runtime's own
// thread, and is rejected anywhere else. Tasks never migrate, so only the
// storage type needed Send; the owner-thread check at spawn is what keeps a
// !Send future on its thread.

use lion_executor::{spawn, spawn_local, Runtime};
use lion_utility::time::{sleep, timeout};
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::thread::ThreadId;
use std::time::Duration;

const BOUND: Duration = Duration::from_secs(5);

// !Send probe: records the thread it is dropped on.
struct LocalDropProbe {
  _not_send: Rc<()>,
  thread: Arc<Mutex<Option<ThreadId>>>,
}

impl Drop for LocalDropProbe {
  fn drop(&mut self) {
    *self.thread.lock().unwrap() = Some(std::thread::current().id());
  }
}

#[test]
fn rc_holding_future_runs_on_owner_thread() {
  let rt = Runtime::new().expect("runtime");
  let owner = std::thread::current().id();
  // Spawned through the handle before block_on starts.
  let counter = Rc::new(Cell::new(0u32));
  let c = counter.clone();
  let early = rt.handle().spawn_local(async move {
    c.set(c.get() + 1);
    Rc::new(std::thread::current().id())
  });
  rt.block_on(async {
    let shared = Rc::new(RefCell::new(Vec::new()));
    let mut handles = Vec::new();
    for i in 0..4u32 {
      let shared = shared.clone();
      let counter = counter.clone();
      // !Send across an await: Rcs alive over a sleep.
      handles.push(spawn_local(async move {
        let mine = Rc::new(i);
        sleep(Duration::from_millis(2 + i as u64)).await;
        shared.borrow_mut().push(*mine);
        counter.set(counter.get() + 1);
        // A local task may spawn more local tasks.
        spawn_local(async move { Rc::new(i * 10) })
      }));
    }
    for h in handles {
      let inner = timeout(BOUND, h).await.expect("local task hung").expect("local task failed");
      let out = timeout(BOUND, inner).await.expect("nested local task hung").expect("failed");
      assert!(*out % 10 == 0);
    }
    let ran_on = timeout(BOUND, early).await.expect("hung").expect("failed");
    assert_eq!(*ran_on, owner);
    assert_eq!(counter.get(), 5);
    let mut seen = shared.borrow().clone();
    seen.sort();
    assert_eq!(seen, vec![0, 1, 2, 3]);
  });
}

#[test]
fn local_task_is_dropped_on_owner_thread() {
  let owner = std::thread::current().id();
  // Aborted while parked, and left pending when the runtime is dropped.
  let aborted_at = Arc::new(Mutex::new(None));
  let orphaned_at = Arc::new(Mutex::new(None));
  let never_polled_at = Arc::new(Mutex::new(None));
  {
    let rt = Runtime::new().expect("runtime");
    let (a, o, n) = (aborted_at.clone(), orphaned_at.clone(), never_polled_at.clone());
    rt.block_on(async move {
      let probe = LocalDropProbe { _not_send: Rc::new(()), thread: a };
      let t = spawn_local(async move {
        let _p = probe;
        std::future::pending::<()>().await;
      });
      sleep(Duration::from_millis(5)).await;
      t.abort();
      assert!(timeout(BOUND, t).await.expect("hung").expect_err("aborted").is_cancelled());
      let probe = LocalDropProbe { _not_send: Rc::new(()), thread: o };
      let _pending = spawn_local(async move {
        let _p = probe;
        std::future::pending::<()>().await;
      });
      sleep(Duration::from_millis(5)).await;
      // Spawned but never admitted: still in the injection channel at drop.
      let probe = LocalDropProbe { _not_send: Rc::new(()), thread: n };
      let _queued = spawn_local(async move {
        let _p = probe;
      });
    });
  }
  assert_eq!(*aborted_at.lock().unwrap(), Some(owner));
  assert_eq!(*orphaned_at.lock().unwrap(), Some(owner));
  assert_eq!(*never_polled_at.lock().unwrap(), Some(owner));
}

#[test]
fn spawn_local_off_the_owner_thread_is_rejected() {
  let rt = Runtime::new().expect("runtime");
  let handle = rt.handle().clone();
  let spawned = Arc::new(Mutex::new(false));
  let s = spawned.clone();
  let attempt = std::thread::spawn(move || {
    let rc = Rc::new(1u32);
    let _h = handle.spawn_local(async move { *rc });
    *s.lock().unwrap() = true;
  })
  .join();
  assert!(attempt.is_err(), "spawn_local from a foreign thread must panic");
  assert!(!*spawned.lock().unwrap());
  // A thread with no runtime at all is rejected by the free function too.
  let bare = std::thread::spawn(|| {
    let _h = spawn_local(async { Rc::new(0u32) });
  })
  .join();
  assert!(bare.is_err(), "spawn_local without a runtime must panic");
  // The runtime is unaffected, and Send tasks from any thread still work.
  let handle = rt.handle().clone();
  let from_thread = std::thread::spawn(move || handle.spawn(async { 3u32 })).join().unwrap();
  rt.block_on(async {
    assert_eq!(timeout(BOUND, from_thread).await.expect("hung").expect("failed"), 3);
    assert_eq!(timeout(BOUND, spawn(async { 4u32 })).await.expect("hung").expect("failed"), 4);
    let local = spawn_local(async { Rc::new(5u32) });
    assert_eq!(*timeout(BOUND, local).await.expect("hung").expect("failed"), 5);
  });
}
