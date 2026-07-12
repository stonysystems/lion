# mutation-test — proof-sensitivity experiment

**Purpose**: measure how tightly the proof structure constrains the
implementation by checking whether the verifier REJECTS liveness-breaking
mutants — answering "could a wrong implementation verify just as well?".
Trusted-region control mutants additionally map the declared TCB boundary
empirically.

**Status**: PREPARED (mutant list locked, not yet executed).

## Protocol (locked before execution; no mid-run changes)

1. **Locked list**: 10 verified-region mutants (M01–M10, laid out along the
   fire→drain→FIFO→poll liveness chain) + 3 trusted-region controls (C1–C3)
   under mutants/. During execution only anchor-text drift may be fixed;
   mutants must not be replaced.
2. **Catch criterion**: run `./verify.sh` for the mutated crate; any error /
   nonzero exit = CAUGHT. Record the FIRST failing invariant/contract (a
   column of the traceability matrix).
3. **Validity (both required)**: each mutant must (a) pass plain
   `cargo build` (otherwise it exercises the type system, not the verifier);
   (b) genuinely break liveness. For M04, M05, M07, C1, C3 additionally run
   correctness-stress and expect a hang ("this bug hangs real workloads, and
   the verifier rejects it statically").
4. **Disposition rules (declared up front)**:
   - A verified-region mutant that SURVIVES (verify stays green) is a major
     finding — an invariant gap. Record it, fix the invariant, keep the
     mutant in the report. Never silently drop it.
   - A control that is CAUGHT is also a finding (the trusted boundary is
     smaller than declared). Record it as such.
5. **One mutant at a time**: apply → build → verify → record → revert
   (git checkout). No stacking.

## Expected output

Traceability matrix:
| mutant | liveness-violation mechanism | result | catching invariant/contract | runtime behavior |
Target headline: 10/10 CAUGHT + 3/3 SURVIVED (controls). Any deviation is a
more valuable finding, handled per rule 4.

## Running

```
./run.sh            # all mutants: apply/verify/revert each, emit RESULTS.md
./run.sh M03        # single mutant
```
Patch files are generated at execution time from the specs in mutants/*.md
(if the source has drifted, the function/semantic anchors in the spec are
authoritative).
