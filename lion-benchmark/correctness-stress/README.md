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
- `lion/`, `tokio-1.21/`, `tokio-1.42/`, `tokio-1.44/`, `tokio-latest/` (fixed-version
  negative control for the two neutral configurations) — the per-runtime crates.
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

(1) Every pattern in the workload is *idiomatic* — LocalSet startup for `!Send`
init and `block_in_place` + `Handle::block_on` bridging are the documented,
recommended ways to write those operations. (2) The Tokio versions under test
were *selected for their documented liveness bugs* (issue numbers in the table)
— that is the point of the experiment, not a hidden bias.

(3) **Every configuration has a control.** For the two neutral mixes it is
`tokio-latest/`, which pins a release with both of their bugs fixed and passes
0/REPS in each — exactly like the fixed libevent 2.1.12 / libuv 1.44.2 controls
on the C side, demonstrating those mixes detect version-specific bugs rather than
being adversarial to Tokio as such. The `localset` cell targets a defect that is
unfixed upstream, so no released Tokio can play that role; `tokio-patched/`
supplies it instead — the *same* 1.52.3 release with one repair applied and
nothing else changed. It passes `localset` 0/REPS where `tokio-latest/` hangs
3/3, which is what makes the hang attributable to that defect rather than to the
way the cell uses the API. Run `tokio-patched/prepare.sh` to materialize it.

**Disclosure — the `localset` cell is targeted, and is separated for that
reason.** It carries the two-driver `LocalSet::run_until` shape deliberately: the
defect was already known when the cell was written, not discovered by running the
neutral mixes. It is kept in its own configuration so that (1) and (3) above keep
applying, unqualified, to `current` and `multi`. Read the row accordingly — it
answers "is this defect present in release X", not "does an ordinary workload
find it". Two further caveats:

- The defect is **unreported upstream**, so unlike every other row here it
  carries no issue number and no maintainer confirmation. The weight therefore
  rests on the reproduction and on the `tokio-patched/` causation control.
- Lion's pass in this row is **not** a verification result: Lion is
  thread-per-core and has no `LocalSet` of its own — `lion::task::LocalSet` is a
  compatibility shim (`run_until` is `future.await`, `spawn_local` is `spawn`) —
  so it passes by not having the mechanism.

## Finding

Every tested Tokio version hangs in at least one configuration, and **the current
release hangs in the targeted one**:

| config | hangs | path | control that passes |
|---|---|---|---|
| `current` | Tokio 1.21 | spawn-wakeup (issue #5020) | `tokio-latest` (1.52.3) |
| `multi` | Tokio 1.42, 1.44 | cooperative yield under `block_in_place` (issue #7209/#7210) | `tokio-latest` (1.52.3) |
| `localset` | Tokio 1.21, 1.42, 1.44, **1.52.3** | `LocalSet` never invokes its driver's registered waker (unreported) | `tokio-patched` (1.52.3 + the repair) |

Lion passes all three. The C libevent/libuv tests hang on their own confirmed
bugs, with their fixed versions passing (see their `summary.md`).

Note what the Lion column does and does not carry here: Lion is thread-per-core
and has no `LocalSet` of its own — `lion::task::LocalSet` is a compatibility
shim (`run_until` is `future.await`, `spawn_local` is `spawn`), so it passes this
phase by not having the mechanism, not by discharging a proof obligation.
