//! Tokio arm: multi-threaded work-stealing runtime with `--cores` worker threads.
//! `axum::serve` spawns each connection onto the shared pool, so idle workers
//! steal queued connections from busy ones.

use axum_work_stealing::router;
use clap::Parser;
use std::net::SocketAddr;

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
}

fn main() {
    let args = Args::parse();

    let rt = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(args.cores)
        .enable_all()
        .build()
        .unwrap();

    rt.block_on(async move {
        let addr: SocketAddr = format!("{}:{}", args.host, args.port).parse().unwrap();
        let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
        eprintln!("ws-tokio: {} workers on {}", args.cores, addr);
        axum::serve(listener, router()).await.unwrap();
    });
}
