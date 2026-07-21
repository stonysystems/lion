//! Shared, runtime-agnostic workload for the work-stealing benchmark.
//!
//! One endpoint — `GET /work?n=<iters>` — performs `n` iterations of SHA-256
//! **inline in the async handler** (NOT via `spawn_blocking`). A large `n` therefore
//! occupies its executor thread/core for the whole computation, with no yield
//! point. This is the head-of-line pressure that distinguishes the two runtimes:
//!
//!   * Tokio (multi-thread, work-stealing): a heavy request pins one worker, but
//!     idle workers steal the *queued* light requests, so they don't wait.
//!   * Lion (thread-per-core): a heavy request pins its core; the light requests
//!     queued behind it on that core wait, and other cores cannot steal them.
//!
//! The per-request cost `n` is chosen by the *client* (the wrk lua script), which
//! samples it from a fixed-mean, tunable-variance log-normal distribution — so the
//! benchmark sweeps request-cost variability (CV) at constant total offered load.

use axum::{extract::Query, http::StatusCode, response::IntoResponse, routing::get, Router};
use serde::Deserialize;
use sha2::{Digest, Sha256};

#[derive(Deserialize)]
struct WorkParams {
    /// Number of chained SHA-256 rounds = this request's CPU cost.
    #[serde(default = "default_n")]
    n: u64,
}

fn default_n() -> u64 {
    1
}

/// The actual computation. Pure, so it can run either inline on the event loop
/// or on a blocking-pool thread without any change in result.
pub fn compute(n: u64) -> [u8; 32] {
    let mut acc = [0u8; 32];
    let buf = [0x5au8; 256];
    for _ in 0..n {
        let mut h = Sha256::new();
        h.update(buf);
        h.update(acc);
        acc = h.finalize().into();
    }
    acc
}

/// Inline handler: `n` chained SHA-256 rounds on the executor itself (no offload).
/// A heavy request occupies its executor thread/core for the whole computation.
async fn work_inline(Query(p): Query<WorkParams>) -> impl IntoResponse {
    let acc = compute(p.n);
    // Return part of the digest so the loop cannot be optimised away.
    (StatusCode::OK, format!("{:02x}{:02x}", acc[0], acc[31]))
}

/// Yield control back to the executor exactly once. Runtime-agnostic (poll_fn,
/// not tokio/lion `yield_now`), so both arms chunk with the identical primitive.
async fn yield_once() {
    let mut yielded = false;
    std::future::poll_fn(|cx| {
        if yielded {
            std::task::Poll::Ready(())
        } else {
            yielded = true;
            cx.waker().wake_by_ref();
            std::task::Poll::Pending
        }
    })
    .await
}

/// Chunked handler: the same `n` SHA-256 rounds, but yielding to the executor
/// every `chunk` iterations. This is the thread-per-core-idiomatic mitigation
/// for head-of-line blocking (cf. Seastar's cooperative scheduling): a heavy
/// request no longer monopolises its core, so small requests queued behind it on
/// the SAME core interleave in the gaps. It reorders work on one core — it does
/// NOT move work to other cores, so it cannot recover a per-core capacity deficit
/// the way work stealing does.
async fn work_chunked(p: WorkParams, chunk: u64) -> impl IntoResponse {
    let mut acc = [0u8; 32];
    let buf = [0x5au8; 256];
    let mut done = 0u64;
    while done < p.n {
        let step = chunk.min(p.n - done);
        for _ in 0..step {
            let mut h = Sha256::new();
            h.update(buf);
            h.update(acc);
            acc = h.finalize().into();
        }
        done += step;
        if done < p.n {
            yield_once().await;
        }
    }
    (StatusCode::OK, format!("{:02x}{:02x}", acc[0], acc[31]))
}

/// Offloaded handler: the CPU work is moved off the event loop onto the runtime's
/// blocking pool via `spawn_blocking`. Both runtimes then reduce to "event loop
/// for I/O + a shared blocking pool for the heavy work", so the head-of-line
/// blocking a heavy request causes on its own executor disappears. Injected as a
/// function pointer so the two runtimes supply their own `spawn_blocking`.
async fn work_offload(p: WorkParams, offload: &SpawnBlocking) -> impl IntoResponse {
    let acc = offload(p.n).await;
    (StatusCode::OK, format!("{:02x}{:02x}", acc[0], acc[31]))
}

/// A runtime-supplied `spawn_blocking(compute)` wrapper. Returns a boxed future
/// so `lib.rs` stays runtime-agnostic (tokio and lion provide their own).
pub type SpawnBlocking = std::sync::Arc<
    dyn Fn(u64) -> std::pin::Pin<Box<dyn std::future::Future<Output = [u8; 32]> + Send>>
        + Send
        + Sync,
>;

async fn health() -> impl IntoResponse {
    (StatusCode::OK, "ok")
}

/// Inline router (the default workload): heavy work runs on the executor.
pub fn router() -> Router {
    Router::new()
        .route("/work", get(work_inline))
        .route("/health", get(health))
}

/// Offload router: heavy work runs on `offload` (a runtime's `spawn_blocking`).
pub fn router_offload(offload: SpawnBlocking) -> Router {
    Router::new()
        .route(
            "/work",
            get(move |Query(p): Query<WorkParams>| {
                let offload = offload.clone();
                async move { work_offload(p, &offload).await }
            }),
        )
        .route("/health", get(health))
}

/// Chunked router: heavy work runs inline but yields every `chunk` iterations.
pub fn router_chunked(chunk: u64) -> Router {
    Router::new()
        .route(
            "/work",
            get(move |Query(p): Query<WorkParams>| async move { work_chunked(p, chunk).await }),
        )
        .route("/health", get(health))
}
