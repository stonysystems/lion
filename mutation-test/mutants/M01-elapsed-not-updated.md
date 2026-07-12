crate: lion-timer-wheel
# M01 — advance_to forgets to advance the timestamp

**Target**: `lion-timer-wheel/src/wheel.rs`, `advance_to`, the final `self.elapsed = now;`.
**Mutation**: delete the assignment (variant M01b: perform it on only one branch).
**Liveness violation**: time freezes — the wheel never considers timers due, so
expired timers never reach pending; the first link of the timer wake chain
(fire) is severed and `sleep` never returns.
**Predicted catch**: advance_to's own ensures `self.elapsed == now`; if that
ensures is deleted too (stronger variant), the caller-side coverage forall in
try_pop_expired (`deadlines[rid] <= now ==> pending.contains(rid)`) plus
`self.elapsed <= now` catches it.
**Validity**: pure assignment deletion, compiles; at runtime sleep hangs
(optional stress check).
