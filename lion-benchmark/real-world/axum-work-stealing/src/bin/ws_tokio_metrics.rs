//! Tokio arm + runtime-metrics sampler, to test the parking hypothesis directly.
//!
//! The open question: at low utilisation Tokio's p99 is ~2x worse than an ideal
//! M/G/8 under high CV. The surviving explanation is that work stealing is
//! pull-based -- an idle worker only steals while actively searching, and a
//! parked worker does not search -- so at low load, where most workers are
//! parked, queued small requests behind a heavy one are not stolen promptly.
//!
//! That makes a falsifiable prediction: steals-per-request should RISE with
//! utilisation and parks-per-second should FALL. This binary prints cumulative
//! per-worker RuntimeMetrics once a second; the harness diffs the window.
//!
//! Requires: RUSTFLAGS="--cfg tokio_unstable". Identical serving path to
//! ws-tokio otherwise, so the scheduler behaviour is the one under study.

use axum_work_stealing::router;
use clap::Parser;
use std::net::SocketAddr;
use std::time::Duration;

#[derive(Parser)]
#[command(name = "ws-tokio-metrics")]
struct Args {
    #[arg(long, default_value = "0.0.0.0")]
    host: String,
    #[arg(long, default_value_t = 8080)]
    port: u16,
    #[arg(long, default_value_t = 8)]
    cores: usize,
    /// Spawn one busy yield-loop per worker so workers never park. Tests
    /// whether unpark latency (not lack of stealing) drives the low-load tail:
    /// a never-parked worker is always searching and can steal queued work
    /// immediately. Pegs CPU, so pair with external hot-keepers to hold the
    /// clock constant and isolate parking from frequency.
    #[arg(long, default_value_t = false)]
    keepalive: bool,
}

fn main() {
    let args = Args::parse();
    let rt = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(args.cores)
        .enable_all()
        .build()
        .unwrap();

    // Sampler: cumulative totals across workers, once a second, to stderr.
    // Fields are cumulative since process start; the harness takes the delta
    // over the measurement window (and divides steals by requests served).
    let handle = rt.handle().clone();
    rt.spawn(async move {
        let m = handle.metrics();
        let n = m.num_workers();
        let mut ticker = tokio::time::interval(Duration::from_secs(1));
        loop {
            ticker.tick().await;
            let mut steals = 0u64;
            let mut parks = 0u64;
            let mut polls = 0u64;
            let mut busy_us = 0u128;
            for w in 0..n {
                steals += m.worker_steal_count(w);
                parks += m.worker_park_count(w);
                polls += m.worker_poll_count(w);
                busy_us += m.worker_total_busy_duration(w).as_micros();
            }
            // busy_us is summed cumulative CPU-busy across all workers; parked
            // time over a window = workers*window - delta(busy). That is the
            // quantity the parking hypothesis is really about (duration, not
            // count of parks).
            eprintln!("WSMETRIC steals={steals} parks={parks} polls={polls} busy_us={busy_us}");
        }
    });

    if args.keepalive {
        // One per worker: keeps every worker perpetually runnable, so none park.
        // yield_now goes to the back of the run queue, so real work still runs;
        // the point is only that the worker never sleeps and is always able to
        // steal the instant a task is queued elsewhere.
        for _ in 0..args.cores {
            rt.spawn(async {
                loop {
                    tokio::task::yield_now().await;
                }
            });
        }
        eprintln!("ws-tokio-metrics: keepalive ON ({} yield-loops)", args.cores);
    }

    rt.block_on(async move {
        let addr: SocketAddr = format!("{}:{}", args.host, args.port).parse().unwrap();
        let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
        eprintln!("ws-tokio-metrics: {} workers on {}", args.cores, addr);
        axum::serve(listener, router()).await.unwrap();
    });
}
