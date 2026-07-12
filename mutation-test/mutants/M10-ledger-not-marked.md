crate: lion-executor
# M10 — pop without marking the ledger

**Target**: `self.ledger.mark(task_id);` in the fresh branch of
`pop_injection_action` in `ext.rs`.
**Mutation**: delete the call (variant M10b: mark the wrong tid, `TaskId(0)`).
**Liveness violation**: ledger and log fall out of sync — later wakeups of the
same tid are wrongly rejected by the drain filter (lost wakeups), or the
duplicate check stops working.
**Predicted catch**: the requires of `ledger_updated_by_pop_some`
(`new.spec_has(t) <==> old.spec_has(t) || t == tid`) cannot be met, so the
ensures `ledger_matches_log(self.ledger, self.log@)` fails.
**Validity**: compiles.
