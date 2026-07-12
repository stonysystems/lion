crate: lion-executor
# M06 — next_task reports no task despite a nonempty queue

**Target**: `next_task` Path 1, `if let Some(task_id) = self.local_queue.pop_front()`.
**Mutation**: discard the popped value and fall through to the None path (or
return None at function entry).
**Liveness violation**: ready tasks are never selected (and the discard variant
makes a task vanish outright).
**Predicted catch**: ensures `old(local_queue).len() > 0 ==> result.is_some()`;
the discard variant additionally breaks `fifo_queue_matches`.
**Validity**: compiles.
