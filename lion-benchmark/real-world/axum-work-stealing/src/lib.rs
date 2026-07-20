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

/// CPU-heavy handler: `n` chained SHA-256 rounds, run inline (no `spawn_blocking`).
async fn work(Query(p): Query<WorkParams>) -> impl IntoResponse {
    let mut acc = [0u8; 32];
    let buf = [0x5au8; 256];
    for _ in 0..p.n {
        let mut h = Sha256::new();
        h.update(buf);
        h.update(acc);
        acc = h.finalize().into();
    }
    // Return part of the digest so the loop cannot be optimised away.
    (StatusCode::OK, format!("{:02x}{:02x}", acc[0], acc[31]))
}

async fn health() -> impl IntoResponse {
    (StatusCode::OK, "ok")
}

/// The workload router, shared by both the Tokio and Lion servers.
pub fn router() -> Router {
    Router::new()
        .route("/work", get(work))
        .route("/health", get(health))
}
