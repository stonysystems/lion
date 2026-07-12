pub mod multi;

pub use lion_executor::Runtime;
pub use lion_executor::RuntimeBuilder;
pub use lion_executor::ExecutorHandle as Handle;

pub use lion_executor::spawn;
pub use lion_executor::spawn_blocking;
pub use lion_executor::JoinHandle;
pub use lion_executor::JoinError;

pub use lion_macro::main;
pub use lion_macro::test;

pub mod task {
  pub use lion_utility_verified::yield_now;
  pub use crate::spawn_blocking;
  pub use crate::JoinHandle;

  // Trusted compat glue: a LocalSet API mirroring tokio's surface so the SAME
  // source can run on Lion. Lion is current-thread (thread-per-core), so a task
  // spawned "locally" is just a task on this thread's executor; the shim maps
  // spawn_local -> spawn and run_until -> awaiting the future (spawned tasks are
  // driven by the executor regardless of whether the LocalSet is being polled).
  #[derive(Default)]
  pub struct LocalSet;

  impl LocalSet {
    pub fn new() -> Self {
      LocalSet
    }

    pub fn spawn_local<F>(&self, future: F) -> JoinHandle<F::Output>
    where
      F: core::future::Future + Send + 'static,
      F::Output: Send + 'static,
    {
      crate::spawn(future)
    }

    pub async fn run_until<F: core::future::Future>(&self, future: F) -> F::Output {
      future.await
    }

    pub fn enter(&self) -> LocalEnterGuard {
      LocalEnterGuard
    }

    pub fn block_on<F: core::future::Future>(
      &self,
      rt: &crate::runtime::RuntimeInstance,
      future: F,
    ) -> F::Output {
      rt.block_on(future)
    }
  }

  pub struct LocalEnterGuard;

  pub fn spawn_local<F>(future: F) -> JoinHandle<F::Output>
  where
    F: core::future::Future + Send + 'static,
    F::Output: Send + 'static,
  {
    crate::spawn(future)
  }

  // Trusted compat glue: block_in_place mirrors tokio's API. Tokio runs the
  // blocking closure on the current worker (moving other tasks off it); Lion runs
  // it on an isolated scoped thread so that a nested block_on inside the closure
  // gets its own runtime/TLS and cannot perturb this worker's executor queues.
  // The worker thread blocks on the join, which is exactly block_in_place's
  // contract (this worker is given over to blocking work).
  pub fn block_in_place<F, R>(f: F) -> R
  where
    F: FnOnce() -> R + Send,
    R: Send,
  {
    std::thread::scope(|s| s.spawn(f).join().unwrap())
  }
}

pub mod io {
  // Lion's TcpStream implements tokio's AsyncRead/AsyncWrite; the read/write
  // extension traits are runtime-agnostic, so re-export tokio's io surface to
  // match its API (lets the same source use `<rt>::io::AsyncReadExt`).
  pub use tokio::io::*;
}

pub mod net {
  // TCP comes from the formally verified lion-utility crate; UdpSocket is not
  // yet ported, so it still comes from the legacy unverified crate.
  pub use lion_utility_verified::net::{TcpListener, TcpSocket, TcpStream, ToSocketAddrs};
  pub use lion_utility_verified::net::UdpSocket;
}

pub mod fs {
  pub use lion_utility_verified::fs::{
    read_to_string, read, write, metadata, remove_file, create_dir_all, rename, copy,
    canonicalize, create_dir, hard_link, read_dir, read_link, remove_dir, remove_dir_all, symlink_metadata,
  };
}

pub mod sync {
  // Cross-task signalling primitives now come from the formally verified
  // lion-utility crate: each is thin trusted glue over the verified WaiterKernel
  // (safety + PassWaker-Contract liveness), with the value/buffer as data-glue.
  pub use lion_utility_verified::sync::*;
}

pub mod time {
  // sleep/sleep_until now come from the formally verified lion-utility crate
  // (verified kernel + thin trusted glue); the rest still come from the legacy
  // unverified utility crate until they are ported.
  pub use lion_utility_verified::time::{sleep, sleep_until, Sleep};
  pub use lion_utility_verified::time::{timeout, interval, interval_at, Duration, Elapsed, Instant, Interval, Timeout};
}

pub mod runtime {
  pub use crate::Runtime;
  pub use crate::multi::{MultiRuntime, MultiHandle};

  // Trusted compat glue: a runtime Handle mirroring tokio's
  // `runtime::Handle::current().block_on(..)`. Used (inside block_in_place) to
  // drive a nested future to completion. On Lion this spins up a fresh
  // current-thread runtime on the calling thread; combined with block_in_place's
  // scoped-thread isolation, the nesting is sound (no outer TLS is clobbered).
  pub struct Handle;

  impl Handle {
    pub fn current() -> Handle {
      Handle
    }

    pub fn block_on<F: core::future::Future>(&self, future: F) -> F::Output {
      Runtime::new().unwrap().block_on(future)
    }
  }

  pub struct Builder {
    num_threads: usize,
  }

  impl Builder {
    pub fn new_current_thread() -> Self {
      Self { num_threads: 1 }
    }

    pub fn new_multi_thread() -> Self {
      let num_cpus = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);
      Self { num_threads: num_cpus }
    }

    pub fn enable_all(&mut self) -> &mut Self {
      self
    }

    pub fn enable_io(&mut self) -> &mut Self {
      self
    }

    pub fn enable_time(&mut self) -> &mut Self {
      self
    }

    pub fn thread_name(&mut self, _name: &str) -> &mut Self {
      self
    }

    pub fn worker_threads(&mut self, n: usize) -> &mut Self {
      self.num_threads = n;
      self
    }

    pub fn build(&mut self) -> std::io::Result<RuntimeInstance> {
      if self.num_threads <= 1 {
        Ok(RuntimeInstance::Single(Runtime::new()?))
      } else {
        Ok(RuntimeInstance::Multi(MultiRuntime::new(self.num_threads)?))
      }
    }
  }

  pub enum RuntimeInstance {
    Single(Runtime),
    Multi(MultiRuntime),
  }

  impl RuntimeInstance {
    pub fn block_on<F: std::future::Future>(&self, future: F) -> F::Output {
      match self {
        RuntimeInstance::Single(rt) => rt.block_on(future),
        RuntimeInstance::Multi(rt) => rt.block_on(future),
      }
    }

    pub fn handle(&self) -> &crate::Handle {
      match self {
        RuntimeInstance::Single(rt) => rt.handle(),
        RuntimeInstance::Multi(rt) => rt.handle().executor_handle(),
      }
    }
  }
}
