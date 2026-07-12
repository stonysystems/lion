use std::collections::VecDeque;
use std::sync::{Arc, Mutex, OnceLock};
use std::thread;
use crate::types::{JoinHandle, JoinSender};

struct Task {
  f: Box<dyn FnOnce() + Send>,
}

struct Worker {
  queue: Arc<Mutex<VecDeque<Task>>>,
  thread: thread::Thread,
}

pub struct BlockingPool {
  workers: Vec<Worker>,
  next: std::cell::Cell<usize>,
}

unsafe impl Sync for BlockingPool {}

impl BlockingPool {
  pub fn new(num_threads: usize) -> Self {
    let mut workers = Vec::with_capacity(num_threads);

    for _ in 0..num_threads {
      let queue = Arc::new(Mutex::new(VecDeque::<Task>::new()));
      let queue_clone = queue.clone();

      let h = thread::spawn(move || {
        loop {
          loop {
            let task = queue_clone.lock().unwrap().pop_front();
            match task {
              Some(t) => (t.f)(),
              None => break,
            }
          }
          thread::park();
        }
      });

      workers.push(Worker {
        queue,
        thread: h.thread().clone(),
      });

      std::mem::forget(h);
    }

    BlockingPool {
      workers,
      next: std::cell::Cell::new(0),
    }
  }

  pub fn spawn<F, R>(&self, f: F) -> JoinHandle<R>
  where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
  {
    let (handle, sender) = JoinHandle::new();
    let task = Task {
      f: Box::new(move || {
        sender.complete(f());
      }),
    };

    let n = self.workers.len();
    let idx = self.next.get() % n;
    self.next.set(idx + 1);

    let worker = &self.workers[idx];
    worker.queue.lock().unwrap().push_back(task);
    worker.thread.unpark();

    handle
  }
}

static GLOBAL: OnceLock<BlockingPool> = OnceLock::new();

pub fn spawn_blocking<F, R>(f: F) -> JoinHandle<R>
where
  F: FnOnce() -> R + Send + 'static,
  R: Send + 'static,
{
  GLOBAL
    .get_or_init(|| {
      let n = std::env::var("LION_BLOCKING_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| {
          std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
        });
      BlockingPool::new(n)
    })
    .spawn(f)
}
