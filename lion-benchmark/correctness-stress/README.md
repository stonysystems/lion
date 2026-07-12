# Correctness Under Stress

A single liveness-stress workload run on Lion and on several Tokio versions (and,
in C, on libevent and libuv) to check whether each runtime keeps **every task
live** under ordinary concurrent usage.

## Layout

- `shared/workload.rs` — the one workload, compiled unchanged against each Rust
  runtime; a per-runtime crate differs only in which runtime its `rt` dependency
  renames. It exercises the patterns a real async server runs (startup task
  spawning, deadline-guarded requests, cooperative compute, fan-out, a heartbeat,
  network I/O, and a blocking offload), and is run in the two standard runtime
  configurations: current-thread and multi-thread. Lion is thread-per-core by
  design, so its "multi" cell maps the multi-thread API onto thread-per-core
  execution (the free-fn `spawn` keeps tasks on the calling thread's runtime);
  the tokio rows test a work-stealing scheduler, the Lion row tests this
  mapping — same load, both legitimate hang tests.
- `lion/`, `tokio-1.21/`, `tokio-1.42/`, `tokio-1.44/`, `tokio-latest/` (fixed-version negative control) — the per-runtime crates.
- `libevent-tests/`, `libuv-tests/` — the same test design ported to C (build with
  `build_deps.sh`, run with `run.sh`; see each `summary.md`).
- `run.sh` — builds every Rust runtime and reports a **hang rate** per
  (config, runtime) over N repetitions; per-run results are recorded in
  `results.jsonl`.
- `plot.py` — renders the runtime-activity heatmap (`stress_heatmap.pdf`).

## Oracle

A run that does not terminate within the timeout is recorded as a hang (the
liveness failures are permanent stalls — a task left unscheduled forever — whereas
the workload's critical path is bounded to a few seconds).

## Why this is fair

Three separable facts keep the finding honest: (1) every pattern in the
workload is *idiomatic* — LocalSet startup for `!Send` init and
`block_in_place` + `Handle::block_on` bridging are the documented, recommended
ways to write those operations; the workload contains no call sequence that
exists only to tickle a bug. (2) The Tokio versions under test were *selected
for their documented liveness bugs* (issue numbers in the table) — that is the
point of the experiment, not a hidden bias. (3) A **negative control** runs
alongside: `tokio-latest/` pins a release with both bugs fixed and is expected
to pass 0/REPS, exactly like the fixed libevent 2.1.12 / libuv 1.44.2 controls
on the C side — demonstrating the workload detects version-specific bugs
rather than being adversarial to Tokio as such.

## Finding

Every bug-carrying Tokio version hangs on its confirmed liveness bug —
current-thread on the spawn-wakeup path (issue #5020), multi-thread on the
cooperative-yield-under-`block_in_place` path (issue #7209) — while the
fixed-version control (`tokio-latest`) and Lion pass in both configurations.
The C libevent/libuv tests hang on their own confirmed bugs in the same way,
with their fixed versions passing (see their `summary.md`).
