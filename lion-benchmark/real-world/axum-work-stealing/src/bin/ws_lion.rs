//! Lion arm: N single-threaded per-core executors (thread-per-core, no stealing).
//!
//! Each core runs its own accept loop on its own `SO_REUSEPORT` listener, so a
//! connection's socket is registered and driven on the SAME core that accepted it
//! (a connection accepted on one core's reactor cannot be driven by another's).
//! Within a connection the hyper executor uses `lion::spawn`, keeping its work on
//! that core. So a heavy request pins its core and blocks the connections queued
//! behind it there — and no other core can steal them.

use axum_work_stealing::{compute, router, router_chunked, router_offload, SpawnBlocking};
use clap::Parser;
use hyper_util::rt::TokioIo;
use std::net::SocketAddr;
use std::sync::Arc;
use tower::Service;

#[derive(Parser)]
#[command(name = "ws-lion")]
struct Args {
    #[arg(long, default_value = "0.0.0.0")]
    host: String,
    #[arg(long, default_value_t = 8080)]
    port: u16,
    /// Number of Lion per-core executor instances (= cores).
    #[arg(long, default_value_t = 8)]
    cores: usize,
    /// Comma-separated CPU ids to pin the executors to, one per executor.
    /// Defaults to 0..cores-1. See `pin_current_thread` for why this matters.
    #[arg(long)]
    cpus: Option<String>,
    /// Move the CPU work off the per-core executors via `lion::spawn_blocking`.
    /// Pool size is set by the LION_BLOCKING_THREADS env var (align with the
    /// Tokio arm's --blocking-threads for a pool-for-pool comparison).
    #[arg(long, default_value_t = false)]
    offload: bool,
    /// If >0, run the CPU work inline but yield to the executor every N iters —
    /// the thread-per-core-idiomatic head-of-line mitigation.
    #[arg(long, default_value_t = 0)]
    chunk: u64,
}

/// Pin the calling thread to exactly one CPU.
///
/// `MultiRuntime` creates its executors with plain `thread::spawn` and sets no
/// affinity, and `taskset` on the process only constrains the whole set. Measured
/// on zoo-002 without this: the 8 executor threads occupied 7 CPUs, with cpu5
/// never scheduled and two executors sharing one core for the entire run. That
/// is not the thread-per-core model this arm is supposed to represent -- it
/// costs a whole core of capacity, adds contention between the two co-resident
/// executors, and shows up in the per-core utilisation metric as an imbalance
/// that belongs to the OS scheduler rather than to the runtime.
fn pin_current_thread(cpu: usize) {
    unsafe {
        let mut set: libc::cpu_set_t = std::mem::zeroed();
        libc::CPU_ZERO(&mut set);
        libc::CPU_SET(cpu, &mut set);
        // pid 0 = the calling thread.
        if libc::sched_setaffinity(0, std::mem::size_of::<libc::cpu_set_t>(), &set) != 0 {
            eprintln!("warning: failed to pin executor thread to cpu{cpu}");
        }
    }
}

/// A hyper executor that keeps a connection's sub-tasks on the *current* core.
#[derive(Clone)]
struct LocalExec;

impl<F> hyper::rt::Executor<F> for LocalExec
where
    F: std::future::Future + Send + 'static,
    F::Output: Send + 'static,
{
    fn execute(&self, fut: F) {
        lion::spawn(fut);
    }
}

/// Lion's `spawn_blocking` wrapped to match the runtime-agnostic SpawnBlocking
/// type. Pool size comes from LION_BLOCKING_THREADS (see lion-executor/blocking).
fn lion_sb() -> SpawnBlocking {
    Arc::new(|n| {
        Box::pin(async move { lion::spawn_blocking(move || compute(n)).await.unwrap() })
    })
}

async fn serve_one_core(addr: SocketAddr, cpu: usize, offload: bool, chunk: u64) {
    // This task runs on exactly one executor (see the round-robin spawn in
    // main), so pinning here pins that executor's thread for the process's life.
    pin_current_thread(cpu);

    // Per-core SO_REUSEPORT listener: created ON this core, so its fd lives on
    // this core's reactor.
    let sock = if addr.is_ipv4() {
        lion::net::TcpSocket::new_v4()
    } else {
        lion::net::TcpSocket::new_v6()
    }
    .expect("create socket");
    sock.set_reuseport(true).expect("set SO_REUSEPORT");
    sock.bind(addr).expect("bind");
    let listener = sock.listen(1024).expect("listen");

    loop {
        let (stream, _) = match listener.accept().await {
            Ok(s) => s,
            Err(e) => {
                eprintln!("accept error: {e}");
                continue;
            }
        };
        let svc = if offload {
            router_offload(lion_sb())
        } else if chunk > 0 {
            router_chunked(chunk)
        } else {
            router()
        };
        // Serve this connection ON THIS core (lion::spawn = current executor).
        lion::spawn(async move {
            let io = TokioIo::new(stream);
            let hyper_service = hyper::service::service_fn(move |req| {
                let mut svc = svc.clone();
                async move { svc.call(req).await }
            });
            if let Err(err) = hyper_util::server::conn::auto::Builder::new(LocalExec)
                .serve_connection(io, hyper_service)
                .await
            {
                eprintln!("connection error: {err}");
            }
        });
    }
}

fn main() {
    let args = Args::parse();

    let rt = lion::runtime::MultiRuntime::new(args.cores).unwrap();
    let handle = rt.handle().clone();
    let addr: SocketAddr = format!("{}:{}", args.host, args.port).parse().unwrap();
    eprintln!("ws-lion: {} per-core executors on {}", args.cores, addr);

    // One CPU per executor. Defaults to 0..cores-1; run.sh passes the same
    // physical-core list it hands to taskset, so the executors land on distinct
    // physical cores rather than SMT siblings.
    let cpus: Vec<usize> = match &args.cpus {
        Some(s) => s
            .split(',')
            .map(|c| c.trim().parse().expect("--cpus: expected comma-separated ids"))
            .collect(),
        None => (0..args.cores).collect(),
    };
    assert_eq!(
        cpus.len(),
        args.cores,
        "--cpus must list exactly one cpu per executor ({} given, {} needed)",
        cpus.len(),
        args.cores
    );
    eprintln!(
        "ws-lion: pinning executors to cpus {cpus:?}{}{}",
        if args.offload { ", offload ON" } else { "" },
        if args.chunk > 0 { format!(", chunk={}", args.chunk) } else { String::new() }
    );
    let offload = args.offload;
    let chunk = args.chunk;

    rt.block_on(async move {
        // One accept loop per core. `handle.spawn` round-robins (multi.rs: an
        // atomic counter modulo the executor count), so the first `cores` spawns
        // land one on each executor in order -- which is what lets task i pin
        // itself to cpus[i].
        let mut tasks = Vec::with_capacity(args.cores);
        for cpu in cpus {
            tasks.push(handle.spawn(serve_one_core(addr, cpu, offload, chunk)));
        }
        for t in tasks {
            let _ = t.await;
        }
    });
}
