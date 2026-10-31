//! Tokio arm: multi-threaded work-stealing runtime with `--cores` worker threads.
//! `axum::serve` spawns each connection onto the shared pool, so idle workers
//! steal queued connections from busy ones.

use axum_work_stealing::{compute, router, router_chunked, router_offload, SpawnBlocking};
use clap::Parser;
use std::net::SocketAddr;
use std::sync::Arc;

#[derive(Parser)]
#[command(name = "ws-tokio")]
struct Args {
    #[arg(long, default_value = "0.0.0.0")]
    host: String,
    #[arg(long, default_value_t = 8080)]
    port: u16,
    /// Number of Tokio worker threads (= cores).
    #[arg(long, default_value_t = 8)]
    cores: usize,
    /// Move the CPU work off the event loop via `spawn_blocking`.
    #[arg(long, default_value_t = false)]
    offload: bool,
    /// Blocking-pool size when --offload is set. Align with the Lion arm's
    /// LION_BLOCKING_THREADS so the comparison is pool-for-pool, not against
    /// tokio's default of 512.
    #[arg(long, default_value_t = 8)]
    blocking_threads: usize,
    /// If >0, run the CPU work inline but yield to the executor every N iters.
    #[arg(long, default_value_t = 0)]
    chunk: u64,
}

fn main() {
    let args = Args::parse();

    let rt = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(args.cores)
        .max_blocking_threads(args.blocking_threads)
        .enable_all()
        .build()
        .unwrap();

    rt.block_on(async move {
        let addr: SocketAddr = format!("{}:{}", args.host, args.port).parse().unwrap();
        let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
        let app = if args.offload {
            eprintln!(
                "ws-tokio: {} workers on {}, offload ON (blocking pool {})",
                args.cores, addr, args.blocking_threads
            );
            let sb: SpawnBlocking = Arc::new(|n| {
                Box::pin(async move { tokio::task::spawn_blocking(move || compute(n)).await.unwrap() })
            });
            router_offload(sb)
        } else if args.chunk > 0 {
            eprintln!("ws-tokio: {} workers on {}, chunk={}", args.cores, addr, args.chunk);
            router_chunked(args.chunk)
        } else {
            eprintln!("ws-tokio: {} workers on {}", args.cores, addr);
            router()
        };
        axum::serve(listener, app).await.unwrap();
    });
}
