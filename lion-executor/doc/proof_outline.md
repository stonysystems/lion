# lion-executor Proof Outline

> A concise statement of **what lion-executor proves**, and **how those properties correspond,
> one by one, to the executor invariants consumed by lion-liveness**. It does not cover the
> concrete proof steps.

## In one sentence

lion-executor uses the **logical event log** approach to prove: the executor's **implementation**
(scheduling loop / park / draining of the various queues / poll) **preserves `executor_inv`**——a
set of invariants over the event log——after each append of a complete tick cycle. It is an
**inductive invariant**: the events appended by each tick preserve it, and it closes the loop on
the contract of the executable API (`tick`).

## The two templates used in the proofs

`framework/{action_safety,local_liveness}.rs` (isomorphic to the paper's Listing 4, and to
lion-liveness / lion-reactor):

- **`ActionSafety { acceptance, validity }`** —— action-safety: `∀i: acceptance(l,i) ⟹ validity(l,i)` ("wherever X occurs, Y must hold").
- **`LocalLiveness { acceptance, fulfillment, timely }`** —— local-liveness: `∀i: acceptance(l,i) ⟹ ∃j>i: fulfillment(l,i,j) ∧ timely(l,i,j)` ("wherever X occurs, Y must eventually hold at some j, and in a timely manner").

Each property is instantiated as one of the templates above (the `*() -> ActionSafety<Log>` /
`LocalLiveness<Log>` in `proof/invariants.rs`), whose closures reuse the inline predicates `inv_*`
in the same file; the equivalence of the two formulations is given explicitly by the per-property
bridges `eq_*` and `executor_inv_unfold`.

## The properties proved (9 of them)

Aggregated in `proof/invariants.rs`, in two groups (`executor_inv = structural_inv ∧ semantic_inv`):

- **`structural_inv`** = 1 local-liveness + 4 action-safety
- **`semantic_inv`** = 1 local-liveness + 3 action-safety

| No. | Property | Type | Meaning (informal) |
|---|---|---|---|
| E1 | park_drain_reactor_wake | **liveness** | After a park, the reactor-wake queue must be drained within the same tick |
| E2 | tick_polls_if_runnable | **liveness** | If the queue is non-empty at the start of a tick ⟹ a task must be polled within the same tick (if there is work, do it) |
| E3 | poll_within_tick | safety | Before every PollTask there is a tick_begin within the same tick (poll only within a tick) |
| E4 | valid_task_polling | safety | Only poll tasks that were actually injected; `result==Invalid ⟺ the task is already Ready / was never injected` |
| E5 | tick_has_park | safety | Within every tick there is exactly one park |
| E6 | tick_has_pop_injection | safety | Within every tick there is a pop from the injection queue |
| E7 | tick_has_drain_deferred | safety | Within every tick the deferred queue is drained |
| E8 | tick_has_drain_task_wake | safety | Within every tick the task-wake queue is drained |
| E9 | fifo_task_selection | safety | Each PollTask takes the FIFO head of the queue (fair, no cutting in line) |

> The paper does not distinguish safety/liveness, and **collectively calls these 9 properties local liveness properties**.

## Proof structure

- **Inductive invariant preservation**: `preservation.rs::executor_inv_preserved(old, new, …): executor_inv(old) ⟹ executor_inv(new)`,
  where `new` is `old` with a complete tick cycle (`well_formed_tick_segment`) appended at the tail.
  Paired with per-property lemmas (`*_preserved`) + the template/inline bridges (`eq_*`): at its entry
  the aggregator unfolds the template form into the inline `inv_*`, and at its exit folds it back into
  the template form, while all the internal per-property reasoning uses the inline form throughout.
- **Closing the loop on exec**: the public API `tick` (`executor/tick.rs`) **requires & ensures `executor_inv`**,
  and its body witnesses that the appended segment preserves the invariant.
- **0 `assume` / 0 `admit`** (verified by `grep`).
- `verify.sh`: 78 verified, 0 errors; `cargo build` passes.

## Trust base (justified and minimal)

- **The `*_action` log-instrumentation leaves** (`executor/ext.rs`): `external_body`, but with faithful
  contracts (`log@ == old.log@.push(<the precise event>)` + frame)——threads / std containers / the clock
  cannot be verified, so they can only be trusted this way.
- **`vec_deque`** (`collections/vec_deque.rs`): an `external_body` thin wrapper, but carrying faithful `Seq`
  contracts (push_back→`@.push`, pop_front→`@[0]`, len, is_empty).
- **Opaque views**: `Instant` / `Duration` / `BoxedFuture` etc. with `view=unimplemented!()`.
- 54 occurrences of `external_body` in total, 0 `assume`, 0 `admit`.

## Consistency with what lion-liveness consumes (key point)

lion-liveness is the **composition layer**; it consumes `executor_inv` as an **assumption**, and on top
of it self-proves the 5 `bounded_*_poll` contracts (the latter are exported internally within the liveness
crate, and are not on the executor↔liveness interface). To be sound, "what the composition layer assumes ⊆
what the executor proves" must hold. The per-property review concludes:

- **lion-liveness consumes 8, lion-executor proves 9, the latter being a strict superset of the former**:
  the 8 shared properties are consistent one by one, the executor additionally proves `poll_within_tick` (E3),
  which the liveness crate never references anywhere.
  **The direction is sound** (the assumptions are all proved, and more strongly).
- **The event model is already consistent**: across both crates, `ExecutorEvent` (`Inbound(Tick{Option<()>})` / `Outbound`),
  `DrainSource`, `TID=nat`, and all the `is_*` predicates have the same structure.
- **Cross-check of the 8 shared properties**:

| Verdict | Property |
|---|---|
| Fully consistent | park_drain_reactor_wake, tick_polls_if_runnable, fifo_task_selection (`fifo_queue_at` / `remove_first_occurrence` / `is_fifo_head_at` are verbatim identical across the two crates) |
| Equivalent (identical under the premise) | tick_has_park / pop_injection / drain_deferred / drain_task_wake |
| Consistent (only a representation residual) | valid_task_polling |

The remaining differences **none of which break soundness**:

1. **Provably identical endpoint formulations** (affecting E5–E8): the executor's
   `no_tick_begin_between(p,i) = ∀k: p<k≤i ⇒ ¬tick_begin(k)` (**closed end**),
   while liveness inlines it as `∀k: p<k<i` (**open end**). The executor's range is larger ⇒ the form is stronger ⇒
   `executor ⟹ liveness`; and because under the acceptance `is_tick_end_at(i)` the element `l[i]` is `Tick{Some}`,
   which must not be a `tick_begin`, the extra constraint at k=i is vacuously true, so the two sides are **logically equivalent**
   (holding solely by the mutual exclusion of tick_begin/tick_end).
2. **Representation residuals**: `PollResult<()>` (`Ready(())`) vs liveness's non-generic `PollResult` (`Ready`)——
   the three-way classification is the same, and the consumed decision only uses `==Invalid` / `==Ready`; `TaskView` vs `Task`——both only read `.id`.
3. **Two independent copies**: each crate maintains its own event model and spec (not a single source of truth), the same situation as on the reactor side.

**Conclusion**: every executor invariant that lion-liveness assumes/consumes is **actually proved** in lion-executor
(and more strongly); there is no soundness-breaking drift.

**Optional hardening**: have lion-liveness directly `use` this crate's spec (a single source of truth), upgrading
"semantic one-by-one correspondence" to "a mechanical guarantee by the compiler"; the main effort is unifying the
type representation of `PollResult` / `Task` and merging the two copies of the event model, left as future work.

## Location in the code

| Content | Location |
|---|---|
| Invariant templates | `src/framework/{action_safety,local_liveness}.rs` |
| Invariant aggregation (E1–E9) | `src/proof/invariants.rs` (`executor_inv` / `structural_inv` / `semantic_inv`) |
| Per-invariant predicates + template instances + equivalence bridges | `src/proof/invariants.rs` (`inv_*`, `*()`, `eq_*`, `executor_inv_unfold`) |
| FIFO queue predicates | `src/spec/fifo_queue.rs` |
| Event log / events / types | `src/spec/log.rs`, `src/types/` |
| Preservation proof | `src/proof/preservation.rs` |
| Executable API | `src/executor/tick.rs` (and `park` / `poll_task` / `next_task` etc.) |
