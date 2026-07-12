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
}

thread_local! {
  static CURRENT_HANDLE: RefCell<Option<ExecutorHandle>> = RefCell::new(None);
}

pub struct Runtime {
  executor: RefCell<Box<Executor>>,
  handle: ExecutorHandle,
  _guard: ReactorGuard,
}

impl Runtime {
  pub fn new() -> std::io::Result<Self> {
  RuntimeBuilder::new().build()
  }

  fn with_config(config: RuntimeConfig) -> std::io::Result<Self> {
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
  types::init_global_ctx(
    cross_thread_queue.clone(),
    interrupt_handle.clone(),
    std::thread::current().id(),
  );
  tls::set_cross_thread_ctx(
    cross_thread_queue,
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

  Ok(Runtime {
    executor: RefCell::new(executor),
    handle,
    _guard: guard,
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
      tls::set_current_task(block_on_task_id);
      let poll_result = future.as_mut().poll(&mut context);
      tls::clear_current_task();
      if let Poll::Ready(result) = poll_result {
        return result;
      }
      let mut exec = self.executor.borrow_mut();
      exec.tick();
    }
  }
}

impl Drop for Runtime {
  fn drop(&mut self) {
  CURRENT_HANDLE.with(|h| {
    *h.borrow_mut() = None;
  });
  tls::clear_cross_thread_ctx();
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
