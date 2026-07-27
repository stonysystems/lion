# Real-World Benchmark

## Porting Approach

For each application, we replaced the core async runtime path — TCP accept, read/write, timer management, task spawn/poll, and (where applicable) async file I/O — with Lion's verified runtime. These are the operations that execute on every request and determine throughput and latency. Each port consists almost entirely of import path changes (`tokio::net` → `lion::net`, `tokio::time` → `lion::time`, `tokio::spawn` → `lion::spawn`). Application-level business logic was unchanged.

A small number of secondary paths were not replaced in each application, including `tokio::io` (AsyncRead/Write traits), `tokio::select!`, and OS-specific features (signal handling, Unix domain sockets). `tokio::sync` remains in place in the rumqtt arm (a runtime-independent utility there), while the Pingora port does swap its uses (broadcast/watch/Mutex/oneshot/mpsc) to `lion::sync`. The unreplaced paths are either runtime-independent utilities or depend on OS interfaces for which Lion has not yet provided async wrappers. None are on the request processing hot path.

## Applications

We evaluate Lion on three real-world applications covering distinct async runtime usage patterns:

| | rumqtt | Pingora | Axum File Server |
|---|---|---|---|
| **Application** | MQTT message broker | HTTP reverse proxy | HTTP static file server |
| **GitHub stars** | ~3.5K | ~23K | ~22K (Axum framework) |
| **Codebase** | 30K lines | 75K lines | ~20 lines app + Axum/Hyper/Tower stack |
| **I/O pattern** | TCP long-lived + pub/sub dispatch | TCP short/long-lived + HTTP forwarding | TCP + HTTP + async file read |
| **Runtime usage** | Network I/O + timer (heartbeat/timeout) | Network I/O + timer + connection pooling | Network I/O + `fs::read` per request |
| **What it tests** | Pub/sub multi-path message dispatch | High-concurrency connection management | Network I/O + async filesystem combined |
| **Lines changed** | 85 across 12 files (0.28%) | 353 across 31 files (0.47%) | 54 across 2 files (manual serve loop replaces `axum::serve`, which requires a tokio listener) |

Counting rule for the "lines changed" row: `git diff --no-index --numstat` between
the tokio arm and the lion arm, added plus removed lines, over `.rs` sources and
`Cargo.toml` manifests; lockfiles and docs/examples present in only one arm are
excluded. Recompute with that rule against the current tree; the numbers drift
slightly when either arm takes a repair (e.g. the pingora park-friendly shutdown).

## Benchmark Setup

- **Server**: zoo-002 (AMD EPYC 7702P, 64-core Linux) — the host recorded in
  the reference batch's PROVENANCE.txt (`ref-result/`);
  an earlier draft ran on zoo-001, superseded by the regenerated batches
- **Client**: zoo-004 for rumqtt (`hosts.env`); Pingora runs in the local
  (single-host) topology — its canonical protocol; Axum additionally
  in its localhost deployment on the server host (dual-deployment protocol)
- **Runtime**: Single-threaded (`new_current_thread`) for both Tokio and Lion
- **Runs**: 10 per configuration, 30 seconds per run, interleaved A-B
- **Metrics**: Throughput (ops/s or req/s), trim-2 mean ± stddev.
  For rumqtt this is the **delivered** rate (`sub_mps`, messages reaching
  subscribers), not the publish rate: `AsyncClient::publish().await` returns
  once the message enters a 1000-slot local channel, so `pub_mps` measures
  client-side enqueue and counts messages the broker never dispatched. Both
  columns are retained in the raw CSVs; `tools/export_paper_table.py` selects
  `sub_mps` per row.

---
