# Evaluation Audit Report

Executed against EVALUATION_AUDIT_CHECKLIST.md over all of `lion-benchmark/`
(real-world axum/pingora/rumqtt, micro, ironfleet, correctness-stress) plus the
`lion` facade. Method: §0 mechanical sweeps; live runtime experiments (thread
canary, idle-CPU measurement, echo smoke, stress-suite and micro-timer runs);
per-experiment source-level deep reads by three independent reviewers;
statistics recomputed from raw CSVs; regime claims checked against the paper
source.

**Bottom line: the substitution is genuine and the comparisons are fair.
Every measured request path in every "Lion" arm runs on `lion::*` (accept,
per-connection tasks, read/write, timers, fs, channels); no silent-fallback
path exists that could mislabel a baseline run as Lion; the benchmarked Lion
is the verified Lion by path dependency at green-verified commits; idle
behavior is parking (not spinning) on both sides everywhere except where the
busy-wait IS the baseline under test (IronFleet, the paper-disclosed
treatment); statistics are recomputable from retained raw rows and the two
reference batches agree per-cell. Open items are confined to the external
paper regeneration (R1–R5) and one pending re-collection decision.**

---

## §0. Mechanical gate

| Check | Result |
|---|---|
| `tokio::` in lion-arm sources | Trait/macro-level only on every measured path (facade: single `pub use tokio::io::*`; ironfleet lion-io: `AsyncReadExt/WriteExt` with `default-features=false, features=["io-util"]` — a hidden tokio runtime is impossible there). The two vendored forks' residual tokio is inventoried in §1.1 — all of it off the measured path and README-disclosed |
| `#[tokio::main]` in lion arms | none in any measured binary |
| Tokio-feature accounting | lion-axum declares **no direct tokio dependency** (zero `tokio::` calls; tokio enters only transitively via axum/hyper-util trait plumbing — rationale comment in its Cargo.toml); ironfleet lion-io is trait-only by feature set; the pingora/rumqtt forks' tokio features are each consumed by the disclosed off-path components |
| Facade shape | `lion/Cargo.toml` → lion-executor/lion-reactor/lion-utility by path; `net/time/sync/fs` from the verified crates, executor from lion-executor; single tokio trait re-export |
| `[patch]` redirections | none |
| Per-run raw data | raw CSVs / results.jsonl everywhere; summaries recomputed post-hoc (verified by recomputation, §5) |
| PROVENANCE | present for every reference batch: micro, ironfleet, real-world (commit/host/CPU/kernel/governor/protocol), and correctness-stress (`ref-result-2` records its clean-clone commit; `ref-result/PROVENANCE.txt` states its multi-session assembly honestly, with verdict-uniformity across sessions noted) |
| ci.sh at benchmarked commits | all reference-batch commits (c6736367, ede47094, 4638d704, d9c23bb6) postdate the scan_wheel_min fix (b5f57708) and verify green |

**Runtime canary (live).** axum lion arm under load: all threads carry the
binary's name, zero tokio-named threads; the tokio twin shows its
`tokio-rt-worker` blocking-pool thread — the canary discriminates, positive
control included. Canary reading for the other apps: pingora's lion arm
legitimately shows one tokio orchestration-runtime thread and rumqttd's lion
arm a tokio console thread — both are the README-declared off-path runtimes
(§1.1); a current-thread tokio runtime creates no specially-named thread, so
the declaration, not the canary, is the audit trail there.

**Idle-behavior measurement (live).** The pingora lion server idles at
**0.1% CPU** (8 s idle, echo smoke passing) — worker threads park in the
reactor via a `lion::sync::oneshot` shutdown receiver (verified-kernel-backed,
waker-registering), the same `block_on(rx)` shape as the tokio twin. The same
parking pattern serves pingora's offload threads and the `lion` facade's
`MultiRuntime` workers.

---

## §1.1 Real-world substitution — PASS

**Axum.** Single-file lion arm driven entirely by lion:
`lion::runtime::Builder::new_current_thread`, `lion::net::TcpListener`,
`lion::spawn` per connection, hyper over `TokioIo`-wrapped lion streams with a
local executor shim whose `execute` is `lion::spawn`, `lion::fs::read`
(spawn_blocking asyncify, same shape as tokio's). Twins symmetric (routes,
file sets, ports, wrk args); tokio arm source-confirmed `new_current_thread`;
build profiles identical (`opt-level 3, lto, codegen-units 1` both arms).

**Pingora.** Under the bench config (`threads: 1, work_stealing: false`) the
service worker is a Lion runtime: `lion::net` accept, per-connection
`lion::spawn`, lion-backed `pingora_timeout`, `lion::sync::*` throughout; the
full twin diff reduces to the runtime swap (plus a tokio-arm-only idle UDS
listener off the measured port). The orchestration main loop (signal handling
+ shutdown broadcast) runs on a tokio runtime in both arms — functionality
deeply coupled to `tokio::signal`, off the request path, symmetric, and
declared in `real-world/README.md`. Idle workers park (see §0 measurement).
`current_handle()`'s tokio fallback branch remains for the fork's
`#[tokio::test]` tests; every measured-path caller runs on the NoSteal Lion
workers.

**Rumqtt.** All five broker runtime builders are Lion current-thread
(v4/v5/ws/timer/bridge); accept, per-connection spawn, and
timeout/keepalive/interval are `lion::*`; the router is a std thread + flume,
identical in both arms; `rumqttd.toml` byte-identical. The HTTP admin console
(port 3030) runs on a tokio current-thread runtime in both arms — untouched
by the benchmark, symmetric background load, declared in
`real-world/README.md`.

**Protocol.** Interleaved A-B confirmed real in all three run.sh (run-outer,
runtime-inner, server restart per cell); config/CLI/port/file-set parity
byte-verified; per-app build profiles identical between arms.

## §1.2 IronFleet — PASS

- **Arm identity is fail-loud and archived.** No code path falls back to the
  C# `IoScheduler` under `lion=true`; a missing/unloadable cdylib kills the
  replica before `[[READY]]`. `run.sh` aborts the run (exit 1) if any replica
  fails to become ready, and archives a per-run `.arm` file recording the
  Lion marker line from each replica log ("Using Lion async IO scheduler",
  printed before `[[READY]]`; its absence identifies the C# arm) with a
  hard failure if `RUNTIME=lion` lacks the marker — the results directory
  carries direct evidence of which arm produced each row.
- **The cdylib is genuinely Lion**: a Lion current-thread runtime on a
  dedicated OS thread drives accept/dial/reader/writer tasks (`lion::net`,
  `lion::spawn`, `lion::time`); tokio is trait-only by feature set. FFI
  surface matches the README.
- **Protocol-core invariance**: one source tree, one DLL, selection by argv;
  the two scheduling constants are compile-time and shared; TCP_NODELAY is
  set in both arms and the shared client (the disclosed baseline-favoring
  fix). Between-arms invariance holds structurally; fidelity of the initial
  vendoring vs upstream IronFleet was not diffable offline.
- **Treatment scope (by design, paper-disclosed)**: the comparison target is
  IronFleet's original C# I/O subsystem as shipped, whose receive discipline
  is a busy-wait; the Lion I/O layer replaces it with event-driven waiting,
  including an idle-aware `receive(0)` (64 empty polls → bounded 50 ms
  block). The paper's mechanism paragraph states this verbatim and decomposes
  the unpinned-leader 140% CPU as ~100% Paxos loop + ~40% Lion I/O threads,
  consistent with the reference data (139–142%). The benchmark README quotes the reference
  exports: ~3.2–3.3K req/s, ~2.0× (unpinned) / ~5.8–6.1× (1core) over the
  C# `IoScheduler`.
- **Metrics**: client-side throughput/latency; warmup-robust peak CPU (skip
  first 5 lifetime-average samples) in both parsers, both arms; CPU phrased
  as leader-total.

## §1.3 Correctness-stress — PASS

- **Shim identity**: all five per-runtime `src/main.rs` byte-identical
  (5-line shim over `shared/workload.rs`); Cargo.tomls differ only in the
  `rt` rename; tokio versions pinned exactly (=1.21.0/=1.42.0/=1.44.0/
  =1.52.3, the last documented as a fixed-version negative control); lion's
  `rt` is the facade by path.
- **Lion's "multi" cell (by design, README-disclosed)**: Lion is
  thread-per-core; the cell maps the multi-thread API onto thread-per-core
  execution (free-fn `spawn` keeps tasks on the calling thread's runtime —
  the thread-per-core semantics; `MultiHandle::spawn` provides round-robin
  distribution for explicit handles). The tokio rows test a work-stealing
  scheduler's liveness, the Lion row tests this mapping — same load, both
  legitimate hang tests, stated in the suite README.
- **Oracle**: 15 s timeout ≈ 4.7× natural completion (3.0–3.2 s), identical
  across all runtimes including the C harnesses; per-run rows retained in
  results.jsonl; the post-fix full rerun (parked idle workers)
  reproduces the reference matrix EXACTLY — tokio-1.21 current 3/3 HANG
  (#5020), tokio-1.42/1.44 multi 3/3 HANG (#7209), tokio-1.52.3 and Lion 0/3
  everywhere.
- **C ports**: W1–W5 mapping tables in both `summary.md`s, with every
  unported Rust scenario listed (multi-thread/`block_in_place`; the LocalSet
  startup-init pattern); the C combined test's embedded bug-trigger
  subsystem is explicitly contrasted with the neutral Rust mix.

---

## §2. Identity — the benchmarked Lion is the verified Lion: PASS

Every lion arm consumes the verified crates by path through the facade; no
crates.io/git pins, no `[patch]`; reference batches verify green at their
PROVENANCE commits (post scan_wheel_min fix); baseline Tokio pinned by
lockfiles (1.50.0 in both axum arms; exact pins in stress). The facade layers
(`lion/`, `lion-macro/`, utility glue) are outside the verified perimeter —
the honest phrasing used by README/paper ("routes through the verified
kernels via disclosed trusted glue") matches this.

## §3. Workload–purpose alignment — PASS

- **Micro** isolates the named primitives (readiness+wakeup / timer
  register-cancel / blocking-pool fs with symmetric pool sizing; monoio
  disclosed as the no-pool io_uring comparator), loopback only, arms by CLI;
  the workload is byte-unchanged since both reference anchors.
- **Real-world** covers a real link (cross-machine, hosts.env) with axum's
  localhost deployment as its own protocol row. The cross rows are
  link-saturated (lion ≡ tokio within 0.1%) — the dual-deployment protocol
  exists precisely so the runtime-bound evidence (the localhost rows, lion
  8–18% faster in the reference batches) stays separate; the parity-envelope
  constraint (compute over runtime-bound cells only; rumqtt's 10k-capped
  fanout cells likewise excluded) is recorded for the paper regeneration.
- **IronFleet** attributes deltas to the I/O-layer replacement (including
  its receive discipline — the treatment), with CPU claims phrased as
  leader-total in the stated regime.
- **Stress** exercises all seven advertised patterns under a
  timeout-as-hang oracle.

## §4. Comparison fairness — PASS

Build parity per app (identical profiles between arms); config parity
byte-verified; current-thread on both runtimes; TCP_NODELAY symmetric where
relevant; interleaving real; warmup handling symmetric; idle behavior parks
on both sides wherever idling is not itself the baseline under test.
Intended-treatment asymmetry exists exactly once (IronFleet's receive
discipline) and is the paper-disclosed contribution.

## §5. Metric & statistics faithfulness — PASS (2 scope limits)

- Trim-2 mean ± std recomputed from raw rows (micro timer, both batches):
  matches, n=10 per cell, batches agree per-cell within ≤3.8%; axum raw
  exactly 10×3×2 rows, summaries recomputable; ironfleet exports agree
  across batches (3275 vs 3244 req/s, 139 vs 142% CPU).
- Scope limits (recorded for the paper): axum/pingora latency exists only as
  wrk thread-average (no `--latency` percentiles); rumqtt's
  "publish latency" percentiles measure client-side enqueue (a backpressure
  proxy), not broker RTT — percentile-grade latency claims are supportable
  only from ironfleet's client-timestamped data.
- Micro plots: trim-2 with trimmed-set stdev bars, zero-anchored autoscaled
  linear axes, per-panel units; reference figures rendered by the current
  plot.py from the reference raw CSVs.

## §6. Claim ↔ artifact mapping — PASS

The paper table is generated (`tools/export_paper_table.py` →
table.md/tex/csv per results pool; `ironfleet/export_table.py` likewise) — a
real claim→artifact pipeline with PROVENANCE per batch. `ref-result` vs
`ref-result-2` agree per-cell across micro, axum, ironfleet, and the stress
matrix. Setup docs (`ref_paper_setup.md`) name the reference-batch machines
(server zoo-002 / client zoo-004, dual-deployment axum) and the shared
statistic (trim-2, interleaved), with no cluster IPs. Expected run cost and
hosts.env requirements are documented in the top README; the collectors fail
loud on missing hosts and on non-ready replicas.

---

## Open items

1. **Paper regeneration (external)**: regenerate the paper's evaluation
   tables/figures from the reference batches under the constraints recorded
   in this report — latency-claim scope (§5), runtime-bound parity cells
   (§3), ironfleet numbers from the exports (§1.2), zoo-002 setup (§6).
2. ~~Re-collection~~ EXECUTED: `ref-result-3/` exists for every experiment —
   a full fresh-clone cluster batch at commit 72c44640 (post-remediation
   code). Real-world envelope 91.1–122.1% (pingora 101.5%/100.1% — no
   regression from the parked workers, slightly faster than batch #2); micro
   per-cell 97.4–104.4% of batch #2 across all primitives; ironfleet
   3273 req/s / 140% / 1.99× / 6.00× (in line with both batches, `.arm`
   files confirming the Lion arm on every replica); stress matrix exact
   (Lion 0/3 both configs with parked idle workers — the lost-wakeup check);
   C-port matrices identical to the committed summaries. The paper's final
   numbers can regenerate from this batch (or any of the three).

By-design facts a reviewer will encounter (all disclosed in-repo):
IronFleet's idle-aware receive is the treatment, not a confound; Lion's
"multi" is a thread-per-core mapping; the pingora orchestration runtime and
rumqttd console are declared off-path Tokio; `current_handle()`'s tokio
fallback exists for the fork's tests and has no measured-path callers.
