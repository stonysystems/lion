crate: lion-timer-wheel
# M04 — scan looks at L0 only (equivalent of the historical real bug)

**Target**: the `let c1/c2/c3 = ...` assembly in `scan_wheel_min`.
**Mutation**: hardcode c1/c2/c3 to None (equivalent to the old early-exit's
cross-level omission).
**Liveness violation**: when an upper level holds a nearer deadline the park
timeout is overestimated — the reactor parks past a due timer.
**Calibration role**: the original form of this bug verified GREEN inside the
pre-campaign trusted body (see baselines/tcb-reduction/05-final/DISPOSITION.md);
it MUST be caught now, otherwise the scan's ensures chain has a hole.
**Predicted catch**: the assembly proof at the end of scan_wheel_min —
`forall r in self@: best <= self@[r]` fails on the branch where rid lives at
L1..L3 (`cN is Some && cN->0 <= ...`).
**Validity**: compiles; manifests as late fires under timer loads (additional
runtime check listed in the protocol).
