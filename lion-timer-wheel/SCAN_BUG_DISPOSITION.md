# The `scan_wheel_min` late-fire bug, and why the timer numbers went down

This records a deliberate, measured performance regression: fixing a real bug
found during verification made the timer benchmark slower, because the previous
throughput was inflated by the bug itself. It is referenced from
`mutation-test/mutants/M04-scan-skip-upper-levels.md`, which uses the original
form of this bug as a calibration mutant.

## The A/B experiment

Same worktree, same build configuration, `timer_st --threads 1 --load 10000
--duration 3`, per-round raw values in ops/s:

| Build | ops/s |
|---|---|
| Pre-fix baseline (commit `93194423`) | 3,377,356 (archived gate figure, trimmed mean) |
| Original buggy scan restored into the current tree | 3,329,057 / 3,346,985 / 3,354,394 |
| Current correct implementation (`level_band` ring-order scan + `level_counts` empty-level skip) | 2,691,849 / 2,668,081 / 2,673,732 / 2,600,132 / 2,611,456 |

## Conclusion

The old throughput was inflated by the bug. An incorrect early exit let the
reactor park past due timers, so timers fired late and expirations piled up into
batches — which reduced the number of park/wake cycles the benchmark had to
perform. The correct implementation wakes on time for every timer that is
actually due, and the extra wakeups are exactly what punctual delivery costs.
The `level_counts` optimisation (~2%) shows that the cost of the scan itself was
never the dominant term.

Functional gates were green throughout: correctness-stress 60/60 with zero hangs
across four rounds, utility 24/24 across four rounds, `ci.sh` clean over all nine
crates. The tokio and monoio control arms stayed flat within ±2%.

**Effect on the paper:** the regenerated timer figures are lower and honest. The
narrative is stronger for it — formal verification found and fixed a late-fire
bug that had been inflating timer throughput by roughly 25%.

## Supplementary gates

### Memory ledger: PASS (matches the theoretical figure)

10^7 completed tasks (1000 waves x 10k, every task in a wave completing before
the next):

- Baseline commit `93194423`: RSS delta 234,376 KB
- After the campaign: RSS delta 235,644 KB
- **Net campaign delta 1,268 KB, against a bitmap theory figure of 1,220 KB** —
  no unexpected amplification from the TID ledger.

This gate also surfaced something pre-existing: the bulk of that 234 MB is a
dense `task_slab` window, because `lion-slab` is keyed by a monotonic TID and
`remove` leaves a `None` without shrinking — the same shape as the disclosed
`ResourceSlab` no-reuse behaviour. Both belong to the generational-ids plan.
Reproducer: `examples/ledger_mem.rs`.

### Panic behaviour differential: PASS (byte-identical)

`examples/panic_probe.rs` behaves identically on the baseline and post-campaign
builds: a panic inside a task unwinds through `poll` to `main` with no isolation
(a deliberate Lion design choice — there is no per-task `catch_unwind`), with
the same message and the same propagation point. This corroborates the
by-construction argument that the campaign did not change panic semantics.
