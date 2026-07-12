#![cfg_attr(verus_keep_ghost, verus::trusted)]

use std::cell::{Cell, RefCell};
use std::sync::Arc;
use crate::collections::VecDeque;
use crate::types::TaskId;
use lion_reactor::InterruptHandle;

thread_local! {
  static REACTOR_READY_QUEUE: RefCell<VecDeque<TaskId>> = RefCell::new(VecDeque::new());
  static TASK_READY_QUEUE: RefCell<VecDeque<TaskId>> = RefCell::new(VecDeque::new());
  static DEFER_QUEUE: RefCell<VecDeque<TaskId>> = RefCell::new(VecDeque::new());
  static CURRENT_TASK: Cell<Option<TaskId>> = const { Cell::new(None) };
  static TASK_NOTIFIED: RefCell<Vec<bool>> = RefCell::new(Vec::new());
  static BLOCK_ON_YIELDED: Cell<bool> = const { Cell::new(false) };
}

pub(crate) fn set_block_on_yielded(v: bool) {
  BLOCK_ON_YIELDED.with(|c| c.set(v));
}

pub(crate) fn take_block_on_yielded() -> bool {
  BLOCK_ON_YIELDED.with(|c| {
    let v = c.get();
    c.set(false);
    v
  })
}

fn set_notified(task_id: TaskId) -> bool {
  if task_id.0 == u64::MAX {
    return true;
  }
  TASK_NOTIFIED.with(|n| {
    let mut v = n.borrow_mut();
    let idx = task_id.0 as usize;
    if idx >= v.len() {
      v.resize(idx + 1, false);
    }
    if v[idx] {
      return false;
    }
    v[idx] = true;
    true
  })
}

pub(crate) fn clear_notified(task_id: TaskId) {
  TASK_NOTIFIED.with(|n| {
    let mut v = n.borrow_mut();
    let idx = task_id.0 as usize;
    if idx < v.len() {
      v[idx] = false;
    }
  });
}

pub(crate) fn push_reactor_ready(task_id: TaskId) {
  if set_notified(task_id) {
    REACTOR_READY_QUEUE.with(|q| {
      q.borrow_mut().push_back(task_id);
    });
  }
}

pub(crate) fn push_task_ready(task_id: TaskId) {
  if set_notified(task_id) {
    TASK_READY_QUEUE.with(|q| {
      q.borrow_mut().push_back(task_id);
    });
  }
}

pub(crate) fn push_deferred(task_id: TaskId) {
  DEFER_QUEUE.with(|q| {
  q.borrow_mut().push_back(task_id);
  });
}


pub(crate) fn take_reactor_ready() -> VecDeque<TaskId> {
  REACTOR_READY_QUEUE.with(|q| {
  std::mem::take(&mut *q.borrow_mut())
  })
}

pub(crate) fn take_task_ready() -> VecDeque<TaskId> {
  TASK_READY_QUEUE.with(|q| {
  std::mem::take(&mut *q.borrow_mut())
  })
}

pub(crate) fn take_deferred() -> VecDeque<TaskId> {
  DEFER_QUEUE.with(|q| {
  std::mem::take(&mut *q.borrow_mut())
  })
}

pub fn set_current_task(task_id: TaskId) {
  CURRENT_TASK.with(|c| c.set(Some(task_id)));
}

pub fn clear_current_task() {
  CURRENT_TASK.with(|c| c.set(None));
}

pub fn get_current_task() -> Option<TaskId> {
  CURRENT_TASK.with(|c| c.get())
}

pub fn defer_current() {
  CURRENT_TASK.with(|c| {
  if let Some(task_id) = c.get() {
    if task_id.0 == u64::MAX {
      set_block_on_yielded(true);
    }
    push_deferred(task_id);
  } else {
    panic!("defer_current called outside of task context");
  }
  });
}

pub(crate) fn has_deferred() -> bool {
  DEFER_QUEUE.with(|q| !q.borrow().is_empty())
}

pub(crate) fn has_reactor_ready() -> bool {
  REACTOR_READY_QUEUE.with(|q| !q.borrow().is_empty())
}

pub(crate) fn has_task_ready() -> bool {
  TASK_READY_QUEUE.with(|q| !q.borrow().is_empty())
}

pub(crate) fn drain_task_ready_into(target: &mut VecDeque<TaskId>) {
  TASK_READY_QUEUE.with(|q| {
    let mut source = q.borrow_mut();
    while let Some(task_id) = source.pop_front() {
      target.push_back(task_id);
    }
  });
}

pub(crate) fn drain_reactor_ready_into(target: &mut VecDeque<TaskId>) {
  REACTOR_READY_QUEUE.with(|q| {
    let mut source = q.borrow_mut();
    while let Some(task_id) = source.pop_front() {
      target.push_back(task_id);
    }
  });
}

pub(crate) fn drain_deferred_into(target: &mut VecDeque<TaskId>) {
  DEFER_QUEUE.with(|q| {
    let mut source = q.borrow_mut();
    while let Some(task_id) = source.pop_front() {
      target.push_back(task_id);
    }
  });
}

pub(crate) struct CrossThreadQueue {
  inner: flume::Sender<TaskId>,
  receiver: flume::Receiver<TaskId>,
}

impl CrossThreadQueue {
  pub fn new() -> Arc<Self> {
    let (tx, rx) = flume::unbounded();
    Arc::new(Self { inner: tx, receiver: rx })
  }

  pub fn push(&self, task_id: TaskId) {
    self.inner.send(task_id).ok();
  }
}

thread_local! {
  static CROSS_THREAD_CTX: RefCell<Option<(Arc<CrossThreadQueue>, InterruptHandle, std::thread::ThreadId)>> = RefCell::new(None);
}

pub(crate) fn set_cross_thread_ctx(queue: Arc<CrossThreadQueue>, interrupt: InterruptHandle, thread_id: std::thread::ThreadId) {
  CROSS_THREAD_CTX.with(|c| *c.borrow_mut() = Some((queue, interrupt, thread_id)));
}

pub(crate) fn get_cross_thread_ctx() -> (Arc<CrossThreadQueue>, InterruptHandle, std::thread::ThreadId) {
  CROSS_THREAD_CTX.with(|c| c.borrow().as_ref().expect("cross-thread context not set").clone())
}

pub(crate) fn drain_cross_thread() {
  CROSS_THREAD_CTX.with(|c| {
    if let Some((queue, _, _)) = c.borrow().as_ref() {
      while let Ok(tid) = queue.receiver.try_recv() {
        push_task_ready(tid);
      }
    }
  });
}

pub(crate) fn reset_interrupt() {
  CROSS_THREAD_CTX.with(|c| {
    if let Some((_, interrupt, _)) = c.borrow().as_ref() {
      interrupt.reset();
    }
  });
}

pub(crate) fn clear_cross_thread_ctx() {
  CROSS_THREAD_CTX.with(|c| *c.borrow_mut() = None);
}
