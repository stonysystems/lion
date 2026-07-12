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

## Caveats

- One mutant per site, hand-designed; this is a targeted sensitivity probe,
  not exhaustive mutation coverage.
- The first-failure location is where verification stops, not necessarily the
  only invariant violated.
- An earlier automated verdict pass mis-scored C1/C3 as CAUGHT (substring
  "error" matches "0 errors"); adjudication was redone from the saved logs and
  run.sh's criterion is fixed.
