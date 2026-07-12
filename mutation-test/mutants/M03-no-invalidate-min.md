crate: lion-timer-wheel
# M03 — remove does not invalidate cached_min

**Target**: the `self.invalidate_min(deadline)` call in `remove`.
**Mutation**: delete the call.
**Liveness violation**: after removing the minimal deadline the cache points at
a moment that no longer exists; next_deadline reports a stale value — the
reactor wakes early and scans nothing, or (with subsequent inserts) misses the
true minimum.
**Predicted catch**: `cached_min_valid` (a wf conjunct, opaque + reveal) —
remove's `self.wf()` ensures cannot be re-established.
**Validity**: compiles.
