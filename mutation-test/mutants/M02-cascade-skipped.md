crate: lion-timer-wheel
# M02 — advance_to skips the cascade re-insert

**Target**: the `wheel_insert_inner(rid, deadline, now)` call in advance_to's
j-loop non-expired branch.
**Mutation**: drop the rid instead (no re-insert, no pending push).
**Liveness violation**: cascaded timers vanish — present in neither the wheel
nor pending, they never fire.
**Predicted catch**: the dl_pos_consistent-shaped coverage forall carried by
the j-loop invariants
(`deadlines.contains(rid) ==> positions.contains(rid) || pending.contains(rid)`).
**Validity**: compiles; semantically a registered timer silently lost.
