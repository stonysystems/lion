#![cfg_attr(verus_keep_ghost, verus::trusted)]

use std::sync::Arc;
use std::sync::OnceLock;
use std::task::{RawWaker, RawWakerVTable, Wake, Waker};
use super::TaskId;
use crate::tls;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum WakeSource {
  Reactor,
  Task,
}

} // end verus!

static GLOBAL_CTX: OnceLock<(Arc<tls::CrossThreadQueue>, lion_reactor::InterruptHandle, std::thread::ThreadId)> = OnceLock::new();

pub(crate) fn init_global_ctx(
  queue: Arc<tls::CrossThreadQueue>,
  interrupt: lion_reactor::InterruptHandle,
  thread_id: std::thread::ThreadId,
) {
  GLOBAL_CTX.set((queue, interrupt, thread_id)).ok();
}

static TASK_WAKER_VTABLE: RawWakerVTable = RawWakerVTable::new(
  task_raw_clone,
  task_raw_wake,
  task_raw_wake_by_ref,
  raw_drop,
);

unsafe fn task_raw_clone(data: *const ()) -> RawWaker {
  RawWaker::new(data, &TASK_WAKER_VTABLE)
}

unsafe fn task_raw_wake(data: *const ()) {
  task_raw_wake_impl(data);
}

unsafe fn task_raw_wake_by_ref(data: *const ()) {
  task_raw_wake_impl(data);
}

unsafe fn raw_drop(_data: *const ()) {}

unsafe fn task_raw_wake_impl(data: *const ()) {
  let task_id = TaskId(data as u64);
  if let Some((_, _, executor_tid)) = GLOBAL_CTX.get() {
    if std::thread::current().id() == *executor_tid {
      tls::push_task_ready(task_id);
      return;
    }
    let (queue, interrupt, _) = GLOBAL_CTX.get().unwrap();
    queue.push(task_id);
    interrupt.wake();
  }
}

pub(crate) fn create_raw_task_waker(task_id: TaskId) -> Waker {
  unsafe {
    let data = task_id.0 as *const ();
    Waker::from_raw(RawWaker::new(data, &TASK_WAKER_VTABLE))
  }
}

static REACTOR_WAKER_VTABLE: RawWakerVTable = RawWakerVTable::new(
  reactor_raw_clone,
  reactor_raw_wake,
  reactor_raw_wake_by_ref,
  raw_drop,
);

unsafe fn reactor_raw_clone(data: *const ()) -> RawWaker {
  RawWaker::new(data, &REACTOR_WAKER_VTABLE)
}

unsafe fn reactor_raw_wake(data: *const ()) {
  reactor_raw_wake_impl(data);
}

unsafe fn reactor_raw_wake_by_ref(data: *const ()) {
  reactor_raw_wake_impl(data);
}

unsafe fn reactor_raw_wake_impl(data: *const ()) {
  let task_id = TaskId(data as u64);
  tls::push_reactor_ready(task_id);
}

pub fn create_reactor_waker_for_current() -> Waker {
  let task_id = tls::get_current_task()
    .expect("create_reactor_waker_for_current called outside task context");
  unsafe {
    let data = task_id.0 as *const ();
    Waker::from_raw(RawWaker::new(data, &REACTOR_WAKER_VTABLE))
  }
}

pub(crate) fn create_waker(task_id: TaskId, source: WakeSource, defer: bool) -> Waker {
  let (queue, interrupt, thread_id) = tls::get_cross_thread_ctx();
  Waker::from(ExecutorWaker::new(task_id, source, defer, queue, interrupt, thread_id))
}

pub struct ExecutorWaker {
  task_id: TaskId,
  source: WakeSource,
  defer: bool,
  cross_thread_queue: Arc<tls::CrossThreadQueue>,
  interrupt: lion_reactor::InterruptHandle,
  executor_thread_id: std::thread::ThreadId,
}

unsafe impl Send for ExecutorWaker {}
unsafe impl Sync for ExecutorWaker {}

impl ExecutorWaker {
  pub(crate) fn new(
    task_id: TaskId,
    source: WakeSource,
    defer: bool,
    cross_thread_queue: Arc<tls::CrossThreadQueue>,
    interrupt: lion_reactor::InterruptHandle,
    executor_thread_id: std::thread::ThreadId,
  ) -> Arc<Self> {
    Arc::new(Self { task_id, source, defer, cross_thread_queue, interrupt, executor_thread_id })
  }

  fn wake_impl(&self) {
    if std::thread::current().id() == self.executor_thread_id {
      if self.defer {
        tls::push_deferred(self.task_id);
      } else {
        match self.source {
          WakeSource::Reactor => tls::push_reactor_ready(self.task_id),
          WakeSource::Task => tls::push_task_ready(self.task_id),
        }
      }
    } else {
      self.cross_thread_queue.push(self.task_id);
      self.interrupt.wake();
    }
  }

}

impl Wake for ExecutorWaker {
  fn wake(self: Arc<Self>) {
    self.wake_impl();
  }

  fn wake_by_ref(self: &Arc<Self>) {
    self.wake_impl();
  }
}
