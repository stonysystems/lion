# axum-work-stealing

A real-world benchmark isolating the one regime where a **multi-threaded
work-stealing** runtime (Tokio) beats a **thread-per-core** runtime (Lion):
a web service whose per-request CPU cost is **highly variable**.

## What it models

A common web-service pattern: most requests are cheap, but some trigger an
expensive CPU-bound operation (compression, hashing, report generation). We
model this with a single endpoint `GET /work?n=<iters>` that runs `n` chained
SHA-256 rounds **inline in the async handler** (no `spawn_blocking`, so a heavy
request occupies its executor thread/core).

The client (`bench/work_cv.lua`) samples `n` per request from a **log-normal
distribution with a fixed mean and a tunable coefficient of variation (CV)**.
Increasing CV raises request-cost variability while holding total offered CPU
constant — so we sweep *variability*, not *load*.

## Why the runtimes differ

* **Tokio** (`ws-tokio`, `--cores N` worker threads): a heavy request pins one
  worker, but idle workers **steal** the light requests queued behind it, so
  they don't wait.
* **Lion** (`ws-lion`, `MultiRuntime` with N per-core executors): each connection
  is round-robined to a core and **stays there**. A heavy request pins its core;
  the light requests queued behind it wait, and no other core can steal them.
  This is the shared-nothing thread-per-core model — great for *independent*
  requests, but it cannot rescue work queued behind a heavy task.

As CV grows, Lion's tail latency rises and its throughput drops, while Tokio
stays robust. The gap **is** the work-stealing benefit.

## Layout

```
axum-work-stealing/
  src/lib.rs            # shared, runtime-agnostic workload (the /work handler)
  src/bin/ws_tokio.rs   # Tokio arm  (multi-thread work-stealing)
  src/bin/ws_lion.rs    # Lion arm   (thread-per-core, no stealing)
  bench/work_cv.lua     # wrk load: log-normal n, fixed mean, CV knob
  run.sh                # sweep CV at fixed cores, emit CSV
```

## Run

```bash
CORES=8 MEAN=20000 CVS="0.5 1 2 4 8" DURATION=30 CONNS=64 RUNS=3 ./run.sh
```

Output CSV columns: `system,runtime,cores,mean,cv,run,rps,p50,p99`.
Plot two panels vs CV: **left = p99 latency**, **right = throughput**.

### Notes for a clean result

* Run `wrk` on a **separate machine** (or reserved cores) — the load generator
  must not steal the server's CPU.
* Calibrate `MEAN`/`CONNS` so the server sits at **~60–70% utilisation**
  (queuing, but not saturated: work-stealing helps in the middle regime, not
  when every core is already pegged).
* The server is pinned with `taskset` to `CORES` cores; Tokio worker count and
  Lion instance count both equal `CORES` (same hardware budget on both sides).
* Unlike the other real-world benchmarks (which run **both** runtimes
  single-threaded to compare per-core efficiency), this one is inherently
  **multi-core** — work-stealing only exists across cores.
