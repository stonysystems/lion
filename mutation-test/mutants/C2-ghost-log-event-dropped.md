crate: lion-reactor
# C2 (control, trusted region) — a ghost-log event goes unrecorded

**Target**: the call protocol the log-action ensures describe — mutate by
skipping one action call at a call site (e.g. the park path omits
park_begin_action).
**Mutation**: delete one begin-action call.
**Liveness violation**: the log stops faithfully reflecting execution (an
omission) — reasoning over the log decouples from the real system.
**Prediction**: depends on the call site. Most sites have downstream proofs
that depend on the event's position (prefix/position assertions), so likely
CAUGHT — itself a finding: part of the call protocol IS pinned by caller-side
proofs. A site with no downstream dependency would SURVIVE. Either outcome is
recorded as-is — this control exists precisely to map how much of the call
protocol the caller-side enforcement covers.
