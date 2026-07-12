crate: lion-executor
# M09 — polls something other than the FIFO head

**Target**: the `self.poll_task(task_id)` argument in `poll_loop`.
**Mutation**: poll a fixed/offset tid instead (e.g. `TaskId(task_id.0 + 1)`).
**Liveness violation**: the head task starves — FIFO fairness (which
fifo_task_selection depends on) is broken.
**Predicted catch**: the proof block
`assert(is_fifo_head_at(self.log@, poll_pos, task_tid))` in poll_loop and the
per-poll `is_fifo_head_at` in its ensures.
**Validity**: compiles.
