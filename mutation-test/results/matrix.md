# Mutation experiment — adjudicated matrix

Verdict criterion: `verification results:: N verified, E errors` with E > 0, or a
compile error. (An earlier draft of this table mis-scored C1/C3 by substring-matching
"error", which also matches "0 errors"; adjudicated from the saved per-mutant logs.)

| mutant | build | verify | first failing check |
|---|---|---|---|
| M01 elapsed not advanced        | OK | CAUGHT | try_pop_expired coverage: `deadlines[rid] <= elapsed` (wheel.rs:2827) |
| M02 cascade re-insert dropped   | OK | CAUGHT | cascade pos re-establishment: `pos.level == spec_level_slot(..)` (wheel.rs:2249) |
| M03 cached_min not invalidated  | OK | CAUGHT | cached_min witness: `cached_min_witness != rid` (wheel.rs:771) |
| M04 scan sees L0 only           | OK | CAUGHT | scan assembly: `c1 is Some && c1->0 <= deadlines[rid]` (wheel.rs:3952) |
| M05 cycle exits without polling | OK | CAUGHT | poll_loop ensures: queue nonempty ⟹ ∃ poll (tick.rs:219) |
| M06 next_task lies None         | OK | CAUGHT | ensures: `len > 0 ==> result.is_some()` (next_task.rs:34) |
| M07 drain swallows wakeups      | OK | CAUGHT | enqueue equality: `local_queue == pre.push(t)` (ext.rs:359) |
| M08 injected task not enqueued  | OK | CAUGHT | queue/log coupling: `local_queue == entry.push(tid)` (tick.rs:89) |
| M09 polls non-FIFO-head tid     | OK | CAUGHT | `get_poll_task_id(log[pos]) == task_tid` (tick.rs:373) |
| M10 ledger not marked on pop    | OK | CAUGHT | `ledger_updated_by_pop_some` precondition (ext.rs:237) |
| C1 TLS taker returns empty      | OK | **SURVIVED** (99 verified, 0 errors) | — (inside declared trust boundary) |
| C2 park_begin event unrecorded  | OK | CAUGHT | caller-side event-position pin: `log1 == l0.push(e)` (park.rs:985) |
| C3 mio registration skipped     | OK | **SURVIVED** (206 verified, 0 errors) | — (inside declared trust boundary) |

## Stress column (full, supplemental run)

correctness-stress `current`, 3 reps, 15 s timeout, one mutant at a time via
`../stress-all.sh` (raw per-run: stress-runs.jsonl; script output:
stress-matrix.md). Original validity spot-check covered M04/M05/M07/C1/C3
only; this run extends the column to all 13 mutants plus a baseline, and
reproduces every spot-check verdict.

| mutant | stress | masking mechanism (for passes) |
|---|---|---|
| baseline | 3 pass / 0 hang (median 3.06 s) | — |
| M01 | **3 pass** / 0 hang | runtime redundancy: dueness is re-derived from `deadline <= now` directly (try_pop_expired phases 1/3), and `advance_to` re-walks from the stale `elapsed` every call, so due timers still reach `pending`; pass times match baseline, i.e. fires stay on schedule |
| M02 | **3 pass** / 0 hang | lifecycle shadowing: the severed cascade re-insert runs only when an upper-level slot (delta ≥ 256 ms at 1 ms/tick) is drained; the workload's only ≥ 256 ms timers are the 5 s backstop guards, deregistered ms after creation in a ~3 s run — no live timer ever cascades. Probe-confirmed lethal outside the shadow: see below |
| M03 | **3 pass** / 0 hang | bounded degradation (early): a stale `cached_min` retains a removed, smaller deadline, so `next_deadline` only under-estimates — parks end early (spurious wakeups), never late |
| M04 | **3 pass** / 0 hang | bounded degradation (capped): scan misses upper-level deadlines, but the executor's 100 ms park cap (lion-executor/src/executor/ext.rs:257) bounds the oversleep |
| M05 | 0 pass / **3 hang** | — |
| M06 | 0 pass / **3 hang** | — |
| M07 | 0 pass / **3 hang** | — |
| M08 | 0 pass / **3 hang** | — |
| M09 | 0 pass / **3 hang** | — |
| M10 | 0 pass / **3 hang** | — |
| C1  | 0 pass / **3 hang** | — |
| C2  | **3 pass** / 0 hang | ghost-only mutation: `park_begin_action` is a `reactor_log_action!` ghost-log append with an empty exec body, so the mutated binary is behaviorally identical to baseline |
| C3  | 0 pass / **3 hang** | — |

Reading: the entire timer-fire link (M01–M04) is ACCEPTED by the stress suite
— three distinct masking mechanisms, none shared with the M04 case alone —
while every executor-side mutant (drain/FIFO/poll, M05–M10) hangs 3/3. For
the timer link the verifier's static rejection is the only signal; the
executor link has no runtime redundancy to hide behind.

Provenance: branch main @ 97595a1, REPS=3 TIMEOUT_SECS=15
TEST=current.

## Timer-probe falsification runs (../timer-probe/)

To validate the masking explanations above, a minimal probe (one uncancelled
sleep; placement "root" = the block_on future itself, "spawn" = inside a
spawned, waker-driven task) was run per timer mutant (5 s timeout):

| mutant | root 500 ms | spawn 500 ms | spawn 100 ms |
|---|---|---|---|
| baseline | 500 ms | 501 ms | 100 ms |
| M01 | 501 ms | 501 ms | 100 ms |
| M02 | **600 ms (+1 park cap)** | **HANG** | 100 ms |
| M03 | 500 ms | 500 ms | 100 ms |
| M04 | 500 ms | 500 ms | 100 ms |

Findings (instrumented run: the wheel logged the M02 cascade DROP at t=300 and
never returned the timer):

- **M02 is lethal when its shadow is left**: an uncancelled ≥ 256 ms sleep in a
  spawned task hangs — the timer (and with it the task's only waker path) is
  lost at cascade time. This confirms the workload-shadowing explanation for
  the stress pass rather than any runtime mitigation.
- **A second redundancy layer exists for root futures only**: block_on
  re-polls its root future on every tick (lion-executor/src/lib.rs block_on
  loop) and `Sleep::poll` re-derives dueness from the clock, so a root-level
  sleep survives M02 with exactly one park-cap (~100 ms) of extra latency
  (the lag comes from polling against the reactor's cached now from the
  previous park cycle). M04's stress pass rides the same park-cap bound; the
  stress workload's progress, however, lives in spawned tasks, so this
  root-only redundancy does not explain the M02 stress pass.
- M01's same-layer redundancy holds in both placements (fires on schedule
  root and spawn), and M03's early-wake direction argument likewise.
