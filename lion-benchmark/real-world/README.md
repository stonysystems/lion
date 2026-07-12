# Real-World Application Benchmarks

Regularized real-world benchmarks (paper section "Real-World Applications"),
mirroring the `../micro/` layout. Three applications, each comparing the **Tokio**
runtime against **Lion's formally verified runtime** (`lion::{net,time,sync,fs}`,
the verified `lion-utility` kernels):

| app | what it is | what it stresses | paper metric |
|---|---|---|---|
| `pingora/` | HTTP reverse proxy | high-concurrency connection management | throughput (req/s) |
| `rumqtt/`  | MQTT message broker | pub/sub multi-path dispatch | throughput (msg/s) |
| `axum/`    | HTTP static file server | network I/O + async file read | throughput (req/s) |

## Layout (per app, mirroring `micro/`)

```
<app>/
  run.sh         # one-click; per-run raw CSV (no averaging-away — repo policy);
                 # methodology in the header; quick smoke via DURATION/RUNS
  ref_result/    # the paper's reference data (exp1 *_raw.csv + *_summary.csv)
  results/       # this run's output
```

Each app's sources are self-contained under `<app>/src/` (the Tokio and Lion
ports); `run.sh` builds and drives them. The Lion ports route through the
**verified** crate (`lion::{net,time,sync,fs}` → `lion-utility`). Suite setup
(cmake, plotting venv) is `../setup.sh`.

Residual Tokio in the Lion ports (disclosed): functionality deeply coupled to
Tokio and OFF the measured hot path keeps a Tokio runtime for compile/feature
support — pingora's orchestration runtime (`tokio::signal` + shutdown
broadcast in `run_forever`) and rumqttd's HTTP console thread (port 3030,
`axum::serve` over `tokio::net`). Both exist identically in the Tokio arms
(symmetric background load); every measured request path (accept,
per-connection tasks, read/write, timers) runs on `lion::*`. Anyone
thread-inspecting the Lion binaries should expect these declared runtimes.

## Methodology (from the paper, `ref_paper_setup.md`)

- **Server** zoo-001, **client** zoo-004 (Axum: zoo-001 localhost).
- Single-threaded (`new_current_thread`) for both runtimes; 10 runs × 30 s;
  throughput reported as mean ± stddev.
- Cross-machine (server + client on separate hosts) is where real-world behaviour
  over a real link is the actual goal — contrast the micro suite, which is
  intentionally localhost to isolate runtime overhead.

## Acceptance (critical)

Quick-test numbers vs the paper's `ref_result/`: the **verified** Lion build must
**not regress** beyond the paper's already-measured Lion-vs-Tokio gap. A
regression indicates a verified-version design flaw (hot path / data structures —
e.g. `Vec<Waker>` instead of an intrusive list, per-message heap allocation) and
must be fixed in the **implementation** (never by weakening the proofs).

## Results

Each app's measured Lion-vs-Tokio numbers are in `<app>/results/COMPARISON.md`,
alongside the paper's reference data in `<app>/ref_result/`.
