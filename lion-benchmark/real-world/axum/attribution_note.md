# Axum localhost delta — attribution note

The paper's Axum-localhost rows show Lion ahead of Tokio (up to 119% on the
API workload in the reference topology). The two arms differ in more than the
runtime, which raises an attribution question this note settles experimentally:

1. **Serve-path shape**: the tokio arm uses `axum::serve`; the lion arm uses a
   manual accept loop + `hyper_util::server::conn::auto` with a `lion::spawn`
   executor shim (axum::serve requires a tokio listener type).
2. **fs/blocking path**: both arms call their runtime's native `fs::read`
   (spawn_blocking asyncify in both), but the pools differ — Tokio's blocking
   pool spawns threads on demand (default cap 512, 10 s idle reap, shared
   injection queue); Lion's (`lion-executor/src/blocking.rs`) pre-spawns a
   fixed pool of `available_parallelism()` threads at first use
   (`LION_BLOCKING_THREADS` overrides) with round-robin per-worker queues and
   park/unpark dispatch. Every request of every Axum workload passes through
   `fs::read`, so this is hot-path.

## Experiment

Five configs isolate the two factors (sources in `src/attribution/`;
`drive.sh` builds and runs all five with the harness's wrk protocol,
`wrk -t2 -c50` + `small.lua`, interleaved A-B, server restart per cell,
localhost):

| config | serve path | file read |
|---|---|---|
| tokio-serve-fs | `axum::serve` (repo tokio arm, unmodified) | `tokio::fs::read` |
| tokio-manual-fs | manual loop, identical to lion arm's | `tokio::fs::read` |
| tokio-manual-nofs | manual loop | preloaded in-memory map |
| lion-manual-fs | manual loop (repo lion arm, unmodified) | `lion::fs::read` |
| lion-manual-nofs | manual loop | preloaded in-memory map |

The `--nofs` flag serves file bytes from a `HashMap` preloaded at startup,
removing the fs/blocking path entirely while keeping routing, response
construction, and payload sizes identical.

## Reference result (12-core desktop, wrk on the same host, 10 s x 3 runs)

Raw per-run data: `src/attribution/ref-results.csv`. Medians:

| config | median req/s | reading |
|---|---|---|
| tokio-serve-fs | 108,073 | baseline tokio arm |
| tokio-manual-fs | 108,181 | serve-path effect: **+0.1% (none)** |
| tokio-manual-nofs | 134,532 | fs path costs tokio ~24% |
| lion-manual-fs | 113,577 | baseline delta here: **+5.0%** |
| lion-manual-nofs | 136,777 | equalized residual: **+1.7%** |

Run-to-run spread is within ±1% for every config; the baseline delta is far
outside noise, the equalized residual is at its edge.

## Conclusions

- **Serve-path shape has no measurable performance effect** (0.1%). The
  asymmetry is cosmetic for performance purposes; the arms' twin status is
  unaffected on this axis.
- **The fs/blocking-pool path is the dominant component of Lion's lead** on
  this box: of the +5.0 pp baseline delta, ~3.3 pp vanish when both arms skip
  `fs::read`, leaving ~1.7 pp attributable to the remaining runtime stack
  (accept/net/timers/scheduler). Lion's pre-spawned fixed-pool spawn_blocking
  is genuinely cheaper per call than Tokio's on-demand pool under this
  workload.
- **Interpretation guard**: both arms use their runtime's native fs API, so
  the comparison is a fair drop-in comparison and the paper's headline claim
  (drop-in replacement, negligible performance cost) is unaffected. But the
  localhost lead should not be read as evidence that the *verified scheduler
  core* outperforms Tokio's — the equalized residual is ~2%, near noise. The
  lead lives mostly in the (unverified, trusted) blocking-pool implementation.
- **Scale caveat**: proportions are machine-dependent. The reference batches
  for the paper were collected on the EPYC anchor topology, where the overall
  delta is larger (119% API); the decomposition ratio there has not been
  measured. The direction of both findings (serve path nil, pool dominant) is
  expected to transfer; the exact split is not.

## Reproducing

```
cd src/attribution && ./drive.sh          # 10 s x 3, ~4 minutes
DURATION=30 RUNS=10 ./drive.sh            # paper-grade
```
