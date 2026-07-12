# Invariants and how `tick()` is verified

> What the executor's invariants are, WHERE each is defined, and how they relate to the
> verification of the `tick()` API. The short version: there are **two distinct kinds** of
> invariant, `park`/`poll_task`/… carry only the first kind, and the log-only `executor_inv`
> (the `fifo_task_selection` family) is established one level up — at `tick()` — as a
> **preservation** proof. See also [proof_outline.md](./proof_outline.md).

## Two kinds of invariant — do not conflate them

### (1) Coupling invariants — log ↔ runtime data structures

These tie the ghost `log@` to the concrete executor state (`local_queue@`, `task_slab@`):

| Invariant | Definition | Meaning |
|---|---|---|
| `fifo_queue_matches(l, queue)` | `src/spec/fifo_queue.rs:46` | the ghost FIFO derived from `l` equals the exec `local_queue` |
| `all_queue_tids_injected(l, queue)` | `src/proof/invariants.rs:442` | every tid in the local queue was popped from injection |
| `slab_matches_log(slab, l)` | `src/proof/invariants.rs:449` | the exec `task_slab` matches what the log records |
| `task_slab.wf()` | (slab type) | the slab is internally well-formed |

**Every exec sub-function carries these in its `requires`/`ensures`**: `park`, `poll_task`,
`pop_injection`, `next_task`, `wake_deferred`, `tick`
(`src/executor/{park,poll_task,next_task,wake_deferred,tick}.rs`). They are threaded step by
step so the concrete state and the ghost log never drift apart.

**This is why `park`'s signature shows `fifo_queue_matches` / `slab_matches_log` / `task_slab.wf()`
but NOT `executor_inv` / `fifo_task_selection`** — those are the *other* kind, below.

### (2) `executor_inv` — log-only invariants (the `fifo_task_selection` family)

Pure properties of `l` alone (no reference to `local_queue`/`task_slab`). Defined together in
`src/proof/invariants.rs`, each in **two forms plus a bridge**:

- `inv_X(l)` — the direct predicate (e.g. `inv_fifo_task_selection`, `:82`);
- `X()` — the framework struct (`fifo_task_selection() -> ActionSafety<Log>` `:99`;
  or `tick_polls_if_runnable() -> LocalLiveness<Log>` `:168`);
- `eq_X` — proves `action_safety_satisfied(X(), l) <==> inv_X(l)` (e.g. `eq_fifo_task_selection`).

Aggregated (`src/proof/invariants.rs:195`): `executor_inv(l) = structural_inv(l) && semantic_inv(l)`, **9 conjuncts**:

- `structural_inv` (5): `park_drain_reactor_wake` (local-liveness), `tick_has_park`,
  `tick_has_pop_injection`, `tick_has_drain_deferred`, `tick_has_drain_task_wake` (action-safety);
- `semantic_inv` (4): `tick_polls_if_runnable` (local-liveness), `poll_within_tick`,
  `valid_task_polling`, `fifo_task_selection` (action-safety).

## How `executor_inv` reaches the `tick()` API

`executor_inv` is **not** carried by the sub-functions. It is established one level up:

1. **Per-conjunct preservation lemmas** (`src/proof/preservation.rs`): one proof fn per conjunct —
   `fifo_task_selection_preserved` (`:344`), `tick_has_park_preserved` (`:49`),
   `poll_within_tick_preserved` (`:230`), `valid_task_polling_preserved` (`:267`),
   `tick_polls_if_runnable_preserved` (`:299`), `park_drain_reactor_wake_preserved` (`:193`),
   and the three `tick_has_drain_*`/`pop_injection` ones. Each proves its conjunct holds on
   `new_log` given `executor_inv(old_log)` + the **structural facts** a well-formed tick segment
   provides.

2. **Aggregators** (`preservation.rs`): `structural_inv_preserved` (`:374`),
   `semantic_inv_preserved` (`:408`), and `executor_inv_preserved` (`:454`) —
   `executor_inv(old_log) ==> executor_inv(new_log)` for a well-formed tick segment.

3. **`tick()`** (`src/executor/tick.rs:418`):
   ```
   requires executor_inv(old(self).log@) && <coupling invariants>
   ensures  executor_inv(self.log@)      && <coupling invariants>
   ```
   Its body runs `park` / `pop_injection` / `poll_task` / drains (which establish the log
   STRUCTURE + coupling), then calls `executor_inv_preserved` to turn that structure into
   `executor_inv(self.log@)`.

So `fifo_task_selection` (and the rest of `executor_inv`) **is genuinely proven** — inside
`fifo_task_selection_preserved` / `executor_inv_preserved`, and surfaced as a `tick()`
postcondition. The sub-functions only supply the raw material (structure + coupling).

## Scope / trust boundary (important, honest)

`executor_inv` is verified as a **preservation** (inductive step), NOT as an always-holding
runtime fact:

- **`tick()` PRESERVES it** (`executor_inv(old) ==> executor_inv(new)`) — this inductive step is
  genuinely proven, over single-state (satisfiable) invariants.
- **The base case is NOT established in verified code**: `Reactor`/executor construction —
  `Executor::new` (`src/executor/new.rs`) — does **not** `ensures executor_inv(self.log@)` (it
  just sets `log = empty`). `executor_inv(empty)` is in fact true (the ∀-over-indices are
  vacuous on the empty log), but that is not wired.
- **The driver is trusted**: the real drive loop `block_on` (`src/lib.rs`, the `loop { … exec.tick() }`)
  sits **outside `verus!`**, so `tick()`'s `requires executor_inv(…)` is never discharged by a
  verified caller.

Net: "the executor **maintains** `fifo_task_selection` (and the rest of `executor_inv`)" is a
**proven preservation**; "the **running** executor **always satisfies** it from startup" relies
on the **trusted** base case (`new`) and the **trusted** (un-verified) driver loop. When
`lion-liveness` consumes `executor_inv`, it consumes this preservation guarantee (its own
parallel spec copy of the same invariants), not a fully-grounded runtime theorem.
