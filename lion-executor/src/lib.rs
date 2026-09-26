#![allow(unused_imports)]
#![allow(unused_braces)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(dead_code)]
#![allow(unused_mut)]

use vstd::prelude::*;

mod collections;
mod config;
mod executor;
mod framework;
mod spec;
mod proof;
pub mod types;
mod handle;
pub mod tls;
pub mod blocking;

use std::future::Future;
use std::pin::pin;
use std::task::{Context, Poll};
use std::cell::RefCell;
use std::sync::Arc;
use std::marker::PhantomData;
use lion_reactor::Reactor;
use config::RuntimeConfig;
use handle::InnerHandle;
use collections::mpsc_queue;
use types::{BoxedFuture, ReactorGuard, Task, TaskId, WakeSource};
use executor::Executor;

#[derive(Clone)]
pub struct ExecutorHandle {
  inner: InnerHandle,
}

impl ExecutorHandle {
  pub fn spawn<T: Send + 'static>(&self, future: impl Future<Output = T> + Send + 'static) -> types::JoinHandle<T> {
  self.inner.spawn(future)
  }

  /// Spawns a future that need not be `Send` onto this handle's runtime. The
  /// task is polled and dropped only on the runtime's own thread (the thread
  /// that created the `Runtime`).
  ///
  /// # Panics
  ///
  /// If called on any other thread. Use [`ExecutorHandle::spawn`] from there.
  pub fn spawn_local<F>(&self, future: F) -> types::JoinHandle<F::Output>
  where
    F: Future + 'static,
    F::Output: 'static,
  {
  self.inner.spawn_local(future)
  }
}

thread_local! {
  static CURRENT_HANDLE: RefCell<Option<ExecutorHandle>> = RefCell::new(None);
}

/// A single-threaded Lion runtime. It is bound to the thread that creates it
/// (it is neither `Send` nor `Sync`): that thread drives it, and `spawn_local`
/// tasks live only there. A thread runs at most one Lion runtime at a time:
/// `Runtime::new` on a thread whose runtime is still alive fails with
/// `ErrorKind::AlreadyExists` (use another thread, e.g. `block_in_place` in the
/// `lion` facade). Once the runtime is dropped, the thread may create another.
///
/// ```compile_fail
/// fn assert_send<T: Send>() {}
/// assert_send::<lion_executor::Runtime>();
/// ```
pub struct Runtime {
  // Field order is drop order: the executor (its tasks and the injection
  // receiver) goes first, while the reactor guard is still in place.
  executor: RefCell<Box<Executor>>,
  handle: ExecutorHandle,
  _guard: ReactorGuard,
  // Last: releases this runtime's thread-local registrations after everything
  // above is gone, so task destructors that spawn or wake still find it.
  _thread: ThreadBinding,
  // !Send: the executor may hold spawn_local tasks, which must be dropped on
  // this thread (see types/boxed_future.rs, OwnerThreadOnly).
  _not_send: PhantomData<*const ()>,
}

// What a Runtime installed in its thread's TLS, released on drop. Each entry is
// cleared only if it is still this runtime's; the per-thread wake queues are
// reset only if the cross-thread context was, i.e. if this was the thread's
// runtime. Uses try_with throughout: a Runtime kept in a thread_local may drop
// while the thread's other TLS is being destroyed.
struct ThreadBinding {
  runtime_id: usize,
  cross_thread_queue: Arc<tls::CrossThreadQueue>,
}

impl Drop for ThreadBinding {
  fn drop(&mut self) {
    let _ = CURRENT_HANDLE.try_with(|h| {
      if let Ok(mut h) = h.try_borrow_mut() {
        if h.as_ref().is_some_and(|x| x.inner.runtime_id() == self.runtime_id) {
          *h = None;
        }
      }
    });
    tls::release_runtime_thread_state(&self.cross_thread_queue);
  }
}

// Whether this thread already has a live Lion runtime (or a bare lion-reactor
// Reactor entered). A thread whose TLS is being torn down counts as busy.
fn runtime_is_live_on_this_thread() -> bool {
  CURRENT_HANDLE.try_with(|h| h.borrow().is_some()).unwrap_or(true)
    || tls::has_cross_thread_ctx()
    || Reactor::is_entered_on_current_thread()
}

impl Runtime {
  pub fn new() -> std::io::Result<Self> {
  RuntimeBuilder::new().build()
  }

  fn with_config(config: RuntimeConfig) -> std::io::Result<Self> {
  // Before anything is created or installed: a refused Runtime::new leaves
  // this thread's runtime, and its TLS, untouched.
  if runtime_is_live_on_this_thread() {
    return Err(std::io::Error::new(
      std::io::ErrorKind::AlreadyExists,
      "a Lion runtime is already running on this thread; runtimes do not nest (run the new one on another thread)",
    ));
  }
  let (reactor, interrupt_handle) = match Reactor::new() {
    lion_reactor::IoResult::Ok(r) => r,
    lion_reactor::IoResult::Err(_) => {
    return Err(std::io::Error::new(
      std::io::ErrorKind::Other,
      "Failed to create reactor",
    ))
    }
  };

  let cross_thread_queue = tls::CrossThreadQueue::new();
  tls::set_cross_thread_ctx(
    cross_thread_queue.clone(),
    interrupt_handle.clone(),
    std::thread::current().id(),
  );

  let (injection_sender, injection_receiver) = mpsc_queue();
  let mut executor = Box::new(Executor::new(reactor, injection_receiver, config));
  let guard = executor.enter();
  let inner_handle = InnerHandle::new(injection_sender, interrupt_handle);
  let handle = ExecutorHandle { inner: inner_handle };

  CURRENT_HANDLE.with(|h| {
    *h.borrow_mut() = Some(handle.clone());
  });
  let thread = ThreadBinding { runtime_id: handle.inner.runtime_id(), cross_thread_queue };

  Ok(Runtime {
    executor: RefCell::new(executor),
    handle,
    _guard: guard,
    _thread: thread,
    _not_send: PhantomData,
  })
  }

  pub fn handle(&self) -> &ExecutorHandle {
  &self.handle
  }

  pub fn block_on<F: Future>(&self, future: F) -> F::Output {
    let mut future = pin!(future);
    let block_on_task_id = TaskId(u64::MAX);
    let waker = types::create_waker(block_on_task_id, WakeSource::Task, false);
    let mut context = Context::from_waker(&waker);

    loop {
      let poll_result = {
        let _current = tls::CurrentTaskGuard::enter(block_on_task_id);
        future.as_mut().poll(&mut context)
      };
      if let Poll::Ready(result) = poll_result {
        return result;
      }
      let mut exec = self.executor.borrow_mut();
      exec.tick();
    }
  }
}

pub fn spawn<T: Send + 'static>(future: impl Future<Output = T> + Send + 'static) -> JoinHandle<T> {
  CURRENT_HANDLE.with(|h| {
  h.borrow()
    .as_ref()
    .expect("lion::spawn() called outside Lion runtime context")
    .spawn(future)
  })
}

/// Spawns a future that need not be `Send` onto the current thread's runtime.
/// It is polled and dropped only on this thread.
///
/// # Panics
///
/// If this thread has no running Lion runtime.
pub fn spawn_local<F>(future: F) -> JoinHandle<F::Output>
where
  F: Future + 'static,
  F::Output: 'static,
{
  CURRENT_HANDLE.with(|h| {
  h.borrow()
    .as_ref()
    .expect("lion::spawn_local() called outside Lion runtime context")
    .spawn_local(future)
  })
}

pub use types::JoinHandle;
pub use types::JoinSender;
pub use types::join_handle::JoinError;
pub use types::waker::create_reactor_waker_for_current;
pub use blocking::spawn_blocking;

pub struct RuntimeBuilder {
  config: RuntimeConfig,
}

impl RuntimeBuilder {
  pub fn new() -> Self {
  Self {
    config: RuntimeConfig::default(),
  }
  }

  pub fn event_interval(mut self, interval: usize) -> Self {
  assert!(interval > 0, "event_interval must be > 0");
  self.config.event_interval = interval;
  self
  }

  pub fn build(self) -> std::io::Result<Runtime> {
  Runtime::with_config(self.config)
  }
}

impl Default for RuntimeBuilder {
  fn default() -> Self {
  Self::new()
  }
}

verus! {

fn main() {
}

}
