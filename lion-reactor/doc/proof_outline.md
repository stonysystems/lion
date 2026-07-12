# lion-reactor Proof Outline

> A concise account of **what** lion-reactor proves, and **how**, property by property, these
> guarantees are **consistent with the reactor invariants consumed by lion-liveness**. It does not
> cover the concrete proof steps.

## In one sentence

lion-reactor uses the **logical event log** approach to prove that the reactor's **implementation**
(park / register / deregister / set_waker) **preserves `reactor_wf`** after any single operation——a
set of invariants over the event log. It is an **inductive invariant**: every event appended by an
operation preserves it, and it closes the loop onto the contracts of the executable API.

## The two templates used in the proof

`framework/{action_safety,local_liveness}.rs` (isomorphic to the paper's Listing 4 and to
lion-liveness):

- **`ActionSafety { acceptance, validity }`** —— action-safety: `∀i: acceptance(l,i) ⟹ validity(l,i)` ("wherever X happens, Y must hold").
- **`LocalLiveness { acceptance, fulfillment, timely }`** —— local-liveness: `∀i: acceptance(l,i) ⟹ ∃j>i: fulfillment(l,i,j) ∧ timely(l,i,j)` ("wherever X happens, Y must later hold at some j, and in a timely manner").

## The properties proved (19 of them)

Aggregated in `invariants/mod.rs`, in three groups (`reactor_wf = reactor_inv ∧ reactor_ext_inv ∧ alloc_inv`):

- **`reactor_inv`** = `reactor_safety_inv` (R5–R9b, R14) ∧ `reactor_liveness_inv` (R16, R17a/b)
- **`reactor_ext_inv`** (R1–R4, R10–R13, R15)

| ID | Property | Type | Meaning (informal) |
|---|---|---|---|
| R1 | timer_deadline_future | safety/ext | when registering a timer, the deadline is in the future |
| R2 | park_has_timestamp | ext | each park cycle takes a timestamp exactly once |
| R3 | park_poll_once | ext | each park cycle performs exactly one poll_events |
| R4 | io_ready_in_park | ext | I/O readiness events are produced only within a park cycle |
| R5 | timer_waker_validity | safety | a timer wakeup carries the waker recorded at registration time |
| R6 | io_waker_validity | safety | an I/O wakeup carries the waker from the most recent SetWaker (the resource still being active) |
| R7/R8 | timer/io_reg_uniqueness | safety | for the same rid, an older registration must retire before it can be re-registered |
| R9a/b | timer_io_disjoint | safety | timer and I/O resources never share an id |
| R10/R11 | register/deregister_io_in_cycle | ext | I/O register/deregister occur within a legal cycle |
| R12/R13 | inbound_register/deregister_io_result | ext | the result returned by register/deregister is consistent with the log |
| R14 | wake_has_registration | safety | before emitting WakeTask, the resource was indeed registered |
| R15 | set_waker_active_io | ext | when setting a waker, the corresponding I/O is still active |
| R16 | wake_on_expired | **liveness** | a timer expiring (and still awaiting a wakeup) ⟹ a WakeTask is emitted within the same park cycle |
| R17a/b | wake_on_io_ready_readable/writable | **liveness** | I/O readiness ⟹ a WakeTask is emitted for the corresponding direction |

## Proof structure

- **Inductive invariant preservation**: `reactor_inv_preserved_by_non_trigger(l,e): reactor_inv(l) ⟹ reactor_inv(l.push(e))`,
  paired with per-property lemmas (`flat_rN_preserved`) plus per-event variants; `reactor_ext_inv_preserved_*` likewise
  (`proof/{preservation,safety_preservation,park_safety,liveness_preservation,preservation_ext}.rs`, ~7500 lines).
- **Closing the loop onto exec**: the contracts of the public API (`park` / `register_timer` / `deregister_timer` / `register_io_resource` /
  `deregister_io_resource` / `set_waker` / `next_deadline`) **require & ensure `reactor_wf`**,
  and the function bodies establish `reactor_inv(log_final)`.
- **0 `assume` / 0 `admit`**.

## Trust base (justified and minimal)

- **`*_action` log-instrumentation leaves** (`reactor/ext.rs`): `external_body`, but with faithful contracts
  (`log@ == old.log@.push(<exact event>)` + frame)——the OS/mio/clock cannot be verified, so this is the only
  way to trust them (as in the paper).
- **Opaque FFI type views**: `Waker`, mio `Source`/`Poll`/`IoEventQueue`, `InterruptHandle`, etc., with `view=unimplemented!()`.
- **`ResourceSlotWrapper`**: per-resource slot storage (holding an opaque `Waker`), with 11 faithful thin methods.

## Consistency with what lion-liveness consumes (key point)

lion-liveness is the **composition layer**; it consumes `reactor_inv` (the 19 properties above) as an **assumption**
and proves end-to-end liveness on top of it. For soundness, "what the composition layer assumes = what the reactor proves"
must hold. This repository corresponds **property by property, semantically** to lion-liveness's 19 properties;
four former drifts have been aligned (see the respective commits):

| Former drift | Current status |
|---|---|
| **R16** wake_on_expired (originally an **unsound direction**) | lion-liveness has been weakened to the (true) version proved in this repository (`timer_awaiting_wake`): a deregistered timer no longer wakes, and the strong version is false for the implementation |
| **R6** io_waker_validity | both sides use `io_active_at` acceptance + an existential validity |
| **B** current_park_start | both sides use the "reset at park_end" form |
| **A** timer_retired_at / event model | this repository's `InboundCall::DeregisterTimer` now carries `result: bool`, and `timer_retired_at` uses `is_succ_deregister` instead——consistent with the lion-liveness event model |

**Conclusion**: every reactor invariant that lion-liveness assumes/consumes has a definition consistent with what is
**actually proved** in this repository (the event model `DeregisterTimer{resource_id, result}` is consistent too).
Only two **equivalent** residuals remain, and they do not affect this conclusion:
1. `has_first_timeout_point` (liveness) ≡ `has_timeout_point` (this repository)——different names, same semantics;
2. invariant phrasing: lion-liveness uses the template form (`action_safety_satisfied(P,l)`), this repository inlines it (`∀i: …`)——equivalent unfoldings of the same predicate.

**Optional hardening**: upgrading "property-by-property semantic correspondence" into "a mechanical guarantee from the
compiler" would require lion-liveness to `use` this repository's spec directly (single source of truth). The event model
is now consistent; what mainly remains is the template-vs-inline structural rearrangement, left as future work.

## Where it lives in the code

| Content | Location |
|---|---|
| Invariant templates | `framework/{action_safety,local_liveness}.rs` |
| Invariant aggregation (R1–R17) | `invariants/mod.rs` (`reactor_inv` / `reactor_ext_inv` / `reactor_wf`) |
| Individual invariant predicates | `invariants/*.rs`, `spec/predicates.rs` |
| Event log / types | `spec/log.rs`, `spec/types.rs` |
| Preservation proofs | `proof/{preservation,safety_preservation,park_safety,liveness_preservation,preservation_ext}.rs` |
| Executable API | `reactor/{park,register,timer,waker,ext}.rs` |
