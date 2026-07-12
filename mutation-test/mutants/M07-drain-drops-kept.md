crate: lion-executor
# M07 — the drain swallows wakeups

**Target**: the loop body of `filter_and_enqueue` in `ext.rs`.
**Mutation**: delete `self.local_queue.push_back(t);` (keep `kept.push`; the log
still records honestly).
**Liveness violation**: woken tasks are taken out of TLS but never enqueued —
wakeups are lost; the drain→FIFO link is severed.
**Predicted catch**: filter_and_enqueue's ensures
`local_queue@ == old + kept@.map_values(...)` (the loop invariant fails first).
**Validity**: compiles; stress must hang.
