crate: lion-executor
# M05 — a whole cycle exits without polling any task

**Target**: `lion-executor/src/executor/tick.rs`, `poll_loop` entry.
**Mutation**: unconditional `return;` at the top (before the
`if *count >= event_interval` check).
**Liveness violation**: runnable tasks sit in the queue while the tick polls
nothing — scheduling stalls; the FIFO→poll link is severed.
**Predicted catch**: poll_loop's ensures
`old(local_queue).len() > 0 && *old(count) < event_interval ==> exists poll`.
**Validity**: compiles; stress must hang (additional runtime check).
