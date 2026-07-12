use std::future::Future;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use lion_reactor::InterruptHandle;
use crate::collections::MpscSender;
use crate::types::{BoxedFuture, JoinHandle, JoinSender, Task, TaskId};

#[derive(Clone)]
pub(crate) struct InnerHandle {
  injection_queue: MpscSender<Task>,
  reactor_interrupt: InterruptHandle,
  task_id_counter: Arc<AtomicU64>,
  executor_thread_id: std::thread::ThreadId,
}

impl InnerHandle {
  pub(crate) fn new(
  injection_queue: MpscSender<Task>,
  reactor_interrupt: InterruptHandle,
  ) -> Self {
    Self {
      injection_queue,
      reactor_interrupt,
      task_id_counter: Arc::new(AtomicU64::new(1)),
      executor_thread_id: std::thread::current().id(),
    }
  }

  pub fn spawn<T: Send + 'static>(&self, future: impl Future<Output = T> + Send + 'static) -> JoinHandle<T> {
    let task_id = TaskId(self.task_id_counter.fetch_add(1, Ordering::SeqCst));
    let (handle, sender) = JoinHandle::new();
    let task = Task::new(task_id, BoxedFuture::with_join_sender(future, sender));
    self.injection_queue.send(task);
    let _ = self.reactor_interrupt.wake();
    handle
  }
}
