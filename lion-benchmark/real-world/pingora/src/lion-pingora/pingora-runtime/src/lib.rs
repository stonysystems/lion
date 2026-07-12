// Copyright 2026 Cloudflare, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Pingora async runtime backed by Lion.
//!
//! This crate provides two runtime flavors:
//! - `Steal`: a single Lion runtime (used for the server main loop)
//! - `NoSteal`: multiple Lion runtimes, one per thread, without work stealing

use once_cell::sync::{Lazy, OnceCell};
use rand::Rng;
use std::sync::Arc;
use std::thread::JoinHandle as ThreadJoinHandle;
use std::time::Duration;
use thread_local::ThreadLocal;
use lion::Handle as LionHandle;
use lion::runtime::Runtime as LionRuntime;
use tokio::runtime::{Builder as TokioBuilder, Handle as TokioHandle};

#[derive(Clone)]
pub enum Handle {
    Tokio(TokioHandle),
    Lion(LionHandle),
}

pub enum SpawnHandle<T> {
    Tokio(tokio::task::JoinHandle<T>),
    Lion(lion::JoinHandle<T>),
}

impl<T> std::future::Future for SpawnHandle<T> {
    type Output = Result<T, lion::JoinError>;
    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<Self::Output> {
        match self.get_mut() {
            SpawnHandle::Tokio(jh) => {
                match std::pin::Pin::new(jh).poll(cx) {
                    std::task::Poll::Ready(Ok(v)) => std::task::Poll::Ready(Ok(v)),
                    std::task::Poll::Ready(Err(_)) => std::task::Poll::Ready(Err(lion::JoinError)),
                    std::task::Poll::Pending => std::task::Poll::Pending,
                }
            }
            SpawnHandle::Lion(jh) => std::pin::Pin::new(jh).poll(cx),
        }
    }
}

impl Handle {
    pub fn spawn<F>(&self, future: F) -> SpawnHandle<F::Output>
    where
        F: std::future::Future + Send + 'static,
        F::Output: Send + 'static,
    {
        match self {
            Handle::Tokio(h) => SpawnHandle::Tokio(h.spawn(future)),
            Handle::Lion(h) => SpawnHandle::Lion(h.spawn(future)),
        }
    }
}

pub enum Runtime {
    Steal(tokio::runtime::Runtime),
    NoSteal(NoStealRuntime),
}

impl Runtime {
    pub fn new_steal(threads: usize, name: &str) -> Self {
        Self::Steal(
            TokioBuilder::new_multi_thread()
                .enable_all()
                .worker_threads(threads)
                .thread_name(name)
                .build()
                .unwrap(),
        )
    }

    pub fn new_no_steal(threads: usize, name: &str) -> Self {
        Self::NoSteal(NoStealRuntime::new(threads, name))
    }

    pub fn get_handle(&self) -> Handle {
        match self {
            Self::Steal(r) => Handle::Tokio(r.handle().clone()),
            Self::NoSteal(r) => r.get_runtime().clone(),
        }
    }

    pub fn block_on<F: std::future::Future>(&self, future: F) -> F::Output {
        match self {
            Self::Steal(r) => r.block_on(future),
            Self::NoSteal(_) => {
                let rt = LionRuntime::new().expect("failed to create Lion runtime for block_on");
                rt.block_on(future)
            }
        }
    }

    pub fn shutdown_timeout(self, timeout: Duration) {
        match self {
            Self::Steal(r) => r.shutdown_timeout(timeout),
            Self::NoSteal(r) => r.shutdown(timeout),
        }
    }
}

static CURRENT_HANDLE: Lazy<ThreadLocal<Pools>> = Lazy::new(ThreadLocal::new);
static CURRENT_LOCAL_HANDLE: Lazy<ThreadLocal<Handle>> = Lazy::new(ThreadLocal::new);

/// Return a handle for spawning tasks.
/// If called from a NoSteal worker thread, returns the LOCAL handle for that thread
/// (ensuring spawned tasks run on the same reactor as the caller's IO resources).
/// If called from outside a NoSteal runtime, falls back to Tokio context.
pub fn current_handle() -> Handle {
    if let Some(h) = CURRENT_LOCAL_HANDLE.get() {
        h.clone()
    } else {
        Handle::Tokio(TokioHandle::current())
    }
}

type Pools = Arc<OnceCell<Box<[Handle]>>>;
type Control = (lion::sync::oneshot::Sender<()>, ThreadJoinHandle<()>);

pub struct NoStealRuntime {
    threads: usize,
    name: String,
    pools: Pools,
    controls: OnceCell<Vec<Control>>,
}

impl NoStealRuntime {
    pub fn new(threads: usize, name: &str) -> Self {
        assert!(threads != 0);
        NoStealRuntime {
            threads,
            name: name.to_string(),
            pools: Arc::new(OnceCell::new()),
            controls: OnceCell::new(),
        }
    }

    fn init_pools(&self) -> (Box<[Handle]>, Vec<Control>) {
        let mut pools = Vec::with_capacity(self.threads);
        let mut controls = Vec::with_capacity(self.threads);
        for _ in 0..self.threads {
            let (handle_tx, handle_rx) = std::sync::mpsc::channel::<LionHandle>();
            // Park-friendly shutdown: the oneshot receiver registers a waker and
            // the idle worker parks in the reactor; a self-waking flag poll here
            // would busy-spin the worker thread at 100% CPU (the tokio twin
            // parks in epoll on a oneshot the same way).
            let (shutdown_tx, shutdown_rx) = lion::sync::oneshot::channel::<()>();
            let pools_ref = self.pools.clone();
            let join = std::thread::Builder::new()
                .name(self.name.clone())
                .spawn(move || {
                    let rt = LionRuntime::new().expect("failed to create Lion runtime");
                    let local_handle = Handle::Lion(rt.handle().clone());
                    handle_tx.send(rt.handle().clone()).unwrap();
                    CURRENT_HANDLE.get_or(|| pools_ref);
                    CURRENT_LOCAL_HANDLE.get_or(|| local_handle);
                    let _ = rt.block_on(shutdown_rx);
                })
                .unwrap();
            let lion_handle = handle_rx.recv().expect("failed to get Lion handle from worker");
            pools.push(Handle::Lion(lion_handle));
            controls.push((shutdown_tx, join));
        }

        (pools.into_boxed_slice(), controls)
    }

    pub fn get_runtime(&self) -> &Handle {
        let mut rng = rand::thread_rng();
        let index = rng.gen_range(0..self.threads);
        self.get_runtime_at(index)
    }

    pub fn threads(&self) -> usize {
        self.threads
    }

    fn get_pools(&self) -> &[Handle] {
        if let Some(p) = self.pools.get() {
            p
        } else {
            let (pools, controls) = self.init_pools();
            match self.pools.try_insert(pools) {
                Ok(p) => {
                    self.controls
                        .set(controls)
                        .map_err(|_| "controls already set")
                        .unwrap();
                    p
                }
                Err((p, _my_pools)) => p,
            }
        }
    }

    pub fn get_runtime_at(&self, index: usize) -> &Handle {
        let pools = self.get_pools();
        &pools[index]
    }

    pub fn shutdown(mut self, _timeout: Duration) {
        if let Some(controls) = self.controls.take() {
            let (txs, joins): (Vec<_>, Vec<_>) = controls.into_iter().unzip();
            for tx in txs {
                let _ = tx.send(());
            }
            for join in joins {
                let _ = join.join();
            }
        }
    }
}

#[test]
fn test_steal_runtime() {
    use lion::time::{sleep, Duration};
    let threads = 2;
    let rt = Runtime::new_steal(threads, "test");
    let handle = rt.get_handle();
    let ret = rt.block_on(async {
        sleep(Duration::from_secs(1)).await;
        let handle = current_handle();
        let join = handle.spawn(async {
            sleep(Duration::from_secs(1)).await;
        });
        join.await.unwrap();
        1
    });

    assert_eq!(ret, 1);
}

#[test]
fn test_no_steal_runtime() {
    use lion::time::{sleep, Duration};

    let rt = Runtime::new_no_steal(2, "test");
    let handle = rt.get_handle();
    let ret = rt.block_on(async {
        sleep(Duration::from_secs(1)).await;
        let handle = current_handle();
        let join = handle.spawn(async {
            sleep(Duration::from_secs(1)).await;
        });
        join.await.unwrap();
        1
    });

    assert_eq!(ret, 1);
}

#[test]
fn test_no_steal_shutdown() {
    use lion::time::{sleep, Duration};

    let rt = Runtime::new_no_steal(2, "test");
    let handle = rt.get_handle();
    let ret = rt.block_on(async {
        sleep(Duration::from_secs(1)).await;
        let handle = current_handle();
        let join = handle.spawn(async {
            sleep(Duration::from_secs(1)).await;
        });
        join.await.unwrap();
        1
    });
    assert_eq!(ret, 1);

    rt.shutdown_timeout(Duration::from_secs(1));
}
