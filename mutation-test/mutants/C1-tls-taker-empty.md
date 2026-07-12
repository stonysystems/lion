crate: lion-executor
# C1 (control, trusted region) — TLS taker always returns empty

**Target**: the body of `take_task_ready_from_tls` in `ext.rs`
(inside #[verifier::external_body]).
**Mutation**: replace the body with `Vec::new()` (never touch TLS).
**Liveness violation**: all cross-task wakeups are lost — a real and fatal
liveness bug.
**Prediction**: **SURVIVED** (verify stays green) — the function's ensures make
zero claims; the mutation sits inside the declared trust boundary. On the model
side the taskwake_arrival_within assumption covers delivery, and that
assumption is now false of the real system. Stress must hang (additional
runtime check that closes the boundary-mapping argument).
