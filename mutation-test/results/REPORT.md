# Proof-sensitivity experiment — report

**Headline: 10/10 verified-region liveness mutants are rejected by the verifier;
both trusted-region controls survive verification and hang real workloads,
confirming the declared TCB boundary; the ghost-log call-protocol control is
caught by caller-side proofs.**

## What was run

13 mutants (specs under ../mutants/, list locked before execution), one at a
time: apply → plain `cargo build` (validity) → `./verify.sh` (verdict) →
revert. Runtime hang checks for M04/M05/M07/C1/C3 against correctness-stress.
Raw logs: `<id>-{apply,build,verify}.log`; adjudicated matrix: matrix.md.

Supplemental run (main @ 97595a1): the correctness-stress column
extended from the validity sample to ALL 13 mutants + baseline via
../stress-all.sh (3 reps, 15 s timeout, `current` config; raw per-run in
stress-runs.jsonl). All five spot-check verdicts reproduced.

## Findings

1. **Every verified-region mutant is caught, each by the invariant predicted in
   its spec** — including M04, the calibration mutant reproducing the shape of
   a real bug that had verified green while it lived inside a trusted body.
   The same fault is now impossible to reintroduce silently.
2. **The trust boundary is where the documentation says it is**: C1 (TLS taker
   returns nothing) and C3 (mio registration skipped) verify green — their
   ensures make no claims — and hang the stress suite 3/3. This is the
   boundary-mapping half of the argument: verification cannot see past
   claim-free trusted bodies, exactly as TCB_and_limitations.md declares.
3. **The ghost-log call protocol is partially caller-enforced**: C2 (skipping
   one begin-action call) is CAUGHT because downstream proofs pin the event's
   position in the log. The protocol trust is therefore narrower than "all
   call sites": sites whose events carry no downstream position dependency
   remain trusted.
4. All 13 mutants compile under plain cargo — none of the catches is a type
   error in disguise.
5. Bounded-vs-unbounded nuance (M04): in the composed runtime the executor's
   100 ms park cap converts the late-fire bug into bounded extra latency, so
   stress passes; the static catch is the only line of defense that flags it
   outright.
6. **The whole timer-fire link escapes the stress suite** (supplemental run):
   with the stress column extended to all mutants, M01–M04 ALL pass 3/3 while
   every executor-side mutant (M05–M10, drain/FIFO/poll) hangs 3/3. The four
   timer passes have three distinct masking mechanisms (per-mutant detail in
   matrix.md): runtime redundancy — the fire path re-derives dueness from
   `deadline <= now`, so M01's stale clock never delays a fire; lifecycle
   shadowing — M02's severed cascade re-insert is only reachable by the ≥256 ms
   backstop timers, which the workload cancels ms after creation; and bounded
   degradation — M03 only shortens parks (stale cached_min under-estimates),
   M04's oversleep is clipped by the 100 ms park cap. A falsification probe
   (../timer-probe/, results in matrix.md) confirms M02 is lethal outside its
   shadow: an uncancelled 500 ms sleep in a spawned task hangs under M02,
   while the same sleep as the block_on root future completes 100 ms late —
   block_on re-polls its root every tick and Sleep::poll re-derives dueness
   from the clock, a root-only redundancy layer. Each mutant is a genuine
   invariant violation the verifier rejects, but a test suite ACCEPTS all four:
   for the entire timer link the static catch is the only signal, which is the
   strongest form of the M04 observation. (C2 also passes, trivially: the
   mutation deletes a ghost-log append with an empty exec body, so the binary
   is behaviorally identical to baseline.)

## Caveats

- One mutant per site, designed by a large language model and locked after
  human review; this is a targeted sensitivity probe, not exhaustive mutation
  coverage.
- The first-failure location is where verification stops, not necessarily the
  only invariant violated.
- An earlier automated verdict pass mis-scored C1/C3 as CAUGHT (substring
  "error" matches "0 errors"); adjudication was redone from the saved logs and
  run.sh's criterion is fixed.
