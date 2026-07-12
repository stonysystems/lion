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

| mutant | correctness-stress `current` (3 reps, 15s timeout) |
|---|---|
| M04 | 3 pass / 0 hang — late fires are bounded by the executor's 100 ms park cap in the composed runtime; the unbounded form needs a standalone reactor parking on the reported deadline |
| M05 | 0 pass / 3 hang |
| M07 | 0 pass / 3 hang |
| C1  | 0 pass / 3 hang |
| C3  | 0 pass / 3 hang |
