use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use lion_executor::{Runtime, ExecutorHandle, JoinHandle};
use std::future::Future;
use lion_utility_verified::sync::oneshot;

struct MultiHandleInner {
  handles: Vec<ExecutorHandle>,
  next: AtomicUsize,
}

#[derive(Clone)]
pub struct MultiHandle {
  inner: Arc<MultiHandleInner>,
}

impl MultiHandle {
  pub fn spawn<T: Send + 'static>(&self, future: impl Future<Output = T> + Send + 'static) -> JoinHandle<T> {
    let idx = self.inner.next.fetch_add(1, Ordering::Relaxed) % self.inner.handles.len();
    self.inner.handles[idx].spawn(future)
  }

  pub fn executor_handle(&self) -> &ExecutorHandle {
    &self.inner.handles[0]
  }
}

pub struct MultiRuntime {
  main_runtime: Runtime,
  workers: Vec<thread::JoinHandle<()>>,
  handle: MultiHandle,
  shutdown_txs: Vec<oneshot::Sender<()>>,
}

impl MultiRuntime {
  pub fn new(num_threads: usize) -> std::io::Result<Self> {
    assert!(num_threads >= 1, "need at least 1 thread");

    let main_runtime = Runtime::new()?;
    let mut handles = vec![main_runtime.handle().clone()];

    let mut shutdown_txs = Vec::with_capacity(num_threads - 1);
    let mut workers = Vec::with_capacity(num_threads - 1);

    for _ in 1..num_threads {
      // Park-friendly shutdown: the oneshot receiver registers a waker and the
      // idle worker parks in the reactor; a self-waking flag poll here would
      // busy-spin the worker thread at 100% CPU.
      let (shutdown_tx, shutdown_rx) = oneshot::channel::<()>();
      let (tx, rx) = std::sync::mpsc::channel::<ExecutorHandle>();

      let worker = thread::spawn(move || {
        let rt = Runtime::new().expect("failed to create worker runtime");
        tx.send(rt.handle().clone()).unwrap();
        let _ = rt.block_on(shutdown_rx);
      });

      let worker_handle = rx.recv().expect("worker failed to start");
      handles.push(worker_handle);
      shutdown_txs.push(shutdown_tx);
      workers.push(worker);
    }

    let handle = MultiHandle {
      inner: Arc::new(MultiHandleInner {
        handles,
        next: AtomicUsize::new(0),
      }),
    };

    Ok(MultiRuntime {
      main_runtime,
      workers,
      handle,
      shutdown_txs,
    })
  }

  pub fn handle(&self) -> &MultiHandle {
    &self.handle
  }

  pub fn block_on<F: Future>(&self, future: F) -> F::Output {
    self.main_runtime.block_on(future)
  }
}

impl Drop for MultiRuntime {
  fn drop(&mut self) {
    for tx in self.shutdown_txs.drain(..) {
      let _ = tx.send(());
    }
    for worker in self.workers.drain(..) {
      let _ = worker.join();
    }
  }
}
