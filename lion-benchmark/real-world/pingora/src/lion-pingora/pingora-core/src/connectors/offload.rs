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

use log::debug;
use once_cell::sync::OnceCell;
use rand::Rng;
use lion::Handle as LionHandle;
use lion::runtime::Runtime as LionRuntime;

pub(crate) struct OffloadRuntime {
    shards: usize,
    thread_per_shard: usize,
    pools: OnceCell<Box<[OffloadThread]>>,
}

struct OffloadThread {
    handle: LionHandle,
    _shutdown: lion::sync::oneshot::Sender<()>,
}

impl OffloadRuntime {
    pub fn new(shards: usize, thread_per_shard: usize) -> Self {
        assert!(shards != 0);
        assert!(thread_per_shard != 0);
        OffloadRuntime {
            shards,
            thread_per_shard,
            pools: OnceCell::new(),
        }
    }

    fn init_pools(&self) -> Box<[OffloadThread]> {
        let threads = self.shards * self.thread_per_shard;
        let mut pools = Vec::with_capacity(threads);
        for _ in 0..threads {
            let (handle_tx, handle_rx) = std::sync::mpsc::channel::<LionHandle>();
            // Park-friendly shutdown: the oneshot receiver registers a waker and
            // the idle offload thread parks in the reactor (a self-waking flag
            // poll would busy-spin it at 100% CPU); dropping the sender wakes it.
            let (shutdown_tx, shutdown_rx) = lion::sync::oneshot::channel::<()>();
            std::thread::Builder::new()
                .name("Offload thread".to_string())
                .spawn(move || {
                    debug!("Offload thread started");
                    let rt = LionRuntime::new().expect("failed to create Lion runtime for offload");
                    handle_tx.send(rt.handle().clone()).unwrap();
                    let _ = rt.block_on(shutdown_rx);
                })
                .unwrap();
            let lion_handle = handle_rx.recv().expect("failed to get Lion handle from offload thread");
            pools.push(OffloadThread { handle: lion_handle, _shutdown: shutdown_tx });
        }

        pools.into_boxed_slice()
    }

    pub fn get_runtime(&self, hash: u64) -> &LionHandle {
        let mut rng = rand::thread_rng();

        let shard = hash as usize % self.shards;
        let thread_in_shard = rng.gen_range(0..self.thread_per_shard);
        let pools = self.pools.get_or_init(|| self.init_pools());
        &pools[shard * self.thread_per_shard + thread_in_shard].handle
    }
}
