crate: lion-executor
# M08 — an injected task is accepted but never enrolled

**Target**: the Some branch of the first pop in `tick.rs` `pop_injection`.
**Mutation**: delete `self.local_queue.push_back(task_id);` (variant M08b:
delete the slab insert as well).
**Liveness violation**: a spawned task is popped off the injection queue and
then never queued — it is never polled.
**Predicted catch**: `fifo_queue_matches` (the log's PopInjection{Some} grows
the spec queue while the real queue does not); M08b additionally breaks
`slab_matches_log`.
**Validity**: compiles.
