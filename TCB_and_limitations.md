# Lion — Trusted Computing Base (TCB) & Known Limitations

Every verification claim in this repository is machine-checked **modulo** the trusted
base inventoried here. This file lists, per item, exactly what is trusted and not
verified. Regenerate the raw list with:

```
grep -rn "external_body" lion-reactor/src lion-executor/src lion-timer-wheel/src lion-slab/src lion-utility/src
```

**Count**: 126 trusted `external_body` items — lion-reactor 57, lion-executor 54,
lion-timer-wheel 11, lion-slab 4, lion-utility 0. By trust kind: 30 `semantic`,
26 `ghost-log`, 45 `raw`, 25 `view` (definitions in §3). The ghost-log families
are macro-generated, so a raw grep undercounts (109 attribute lines for 126
items); the §3 tables plus the two macro-invocation lists are the authoritative
inventory. Beyond these: one `#[verifier::external]` item (`lion-slab
Slab::get_mut` — safe bounds-checked code, external only because Verus cannot
express `&mut` returns), and the pinned Verus toolchain (`setup.sh`,
`verus.config`) with its Z3 solver.

**Model↔implementation correspondence.** Event vocabulary and invariant
definitions live in shared spec crates (`lion-framework-spec`,
`lion-executor-spec`, `lion-reactor-spec`, `lion-utility-spec`) consumed by
both the liveness proof and the impl-verified crates, so the two sides cannot
drift silently. The one intentional divergence — io registration anchored on
API success by lion-reactor but on syscall success by lion-liveness — is
closed by a proven bridge (`lion-reactor-spec::bridge::io_anchor_bridge`).
The informal residue: the ghost-log call protocol (each action invoked exactly
once, in order, around its real effect — the verifier enforces this only on
the caller side) and the utilities layer's crate-local invariants. There is no
mechanized refinement proof from the compiled runtime to the model.

---

## 1. Riskiest trust points (read these first)

Ranked by how much a buggy trusted body could silently break the verified
theorems:

1. **The ghost-log action family** — every theorem quantifies over the ghost
   log, so the log faithfully reflecting real execution is the foundational
   guarantee everything above rests on. The trusted surface for log updates is
   kept minimal: each action is an empty body appending exactly one fixed-shape
   event and touching nothing else, and the whole family expands from two
   macros (`reactor_log_action!` / `executor_log_action!`) — the definitions
   occupy a tiny fraction of the code, auditing them reduces to the two macro
   bodies, and shared expansion rules out per-function shape errors. What
   remains trusted is the call protocol (each action invoked once, in order,
   around its real effect); mechanized refinement is out of scope.
2. **mio / OS boundary** — `poll_events_action` (poll effects; tokens returned
   faithfully; readable/writable flags reflect real readiness — the rid<->token
   codec itself is verified), `register/deregister_io_source_action`,
   `Instant::now`, `Reactor::mio_setup` (handle creation, no semantic ensures).
3. **`Executor::poll_future_raw` + the waker vtable** — user future code runs behind
   a free function that cannot touch the executor by construction; the remaining
   trust is that user wake/spawn effects route through the TLS side-channels the
   drain path consumes, and that cloned wakers view-match (`waker-vtable` items).
4. **TLS wake plumbing raw takers** — `take_{task,reactor,deferred}_*_from_tls` /
   `try_recv_raw` hand over a plain Vec/Option with NO claims; fabricated TIDs are
   filtered by the verified ledger layer, lost wakes remain covered by the
   model-side arrival assumptions (`taskwake_arrival_within`, injection schedule).
5. **Trusted data-structure models** — vstd-style ensures on `VecDeque`
   (FIFO-as-sequence semantics that the local-queue liveness derivation rides on),
   the slot-mutation leaves of the timer wheel (including their exact
   `level_counts` deltas), and the four lion-slab leaves.

---

## 2. Known modeling limitations

- **Ids are monotone counters** (internal data management): resource ids and task ids are allocated by
  ever-increasing counters and never reused — the id-indexed structures
  (ResourceSlab, task_slab, TID ledger) therefore grow with the total ids ever
  allocated. The no-reuse liveness theorem is faithful to exactly this
  implementation. Planned: generational ids `(index, gen)` to support id reuse
  and reclamation. In lion-reactor the disabled reuse branches (`free_rids.push`/
  `pop`) are commented out behind `[RID-REUSE DISABLED]` markers while the
  `free_rids_wf` invariant plumbing is retained live (it appears in
  `alloc_resource_id`'s contract and its preservation lemmas are still called);
  the invariant is maintained over a provably-empty free list, so it constrains
  nothing today and is ready for the generational-id restoration.
- **The top theorem is a bounded, filtered (□env ⇒ ◇goal) statement** (theorem statement scope): it quantifies
  over runs that maintain the environment assumptions at every state, and does not
  itself assert such runs exist from every qualifying state. Non-vacuity is
  machine-checked by concrete witness executions on all four wake paths
  (`b/bio/d/t_domain_inhabited`), conditional on mild lower bounds for the model's
  uninterpreted environment constants: every witness requires
  `get_max_queue_length >= 1`, and the timer-path witness additionally
  `get_max_timer_deadline_gap >= 3`. Since the constants are uninterpreted
  (`arbitrary()` spec bodies), no caller can discharge these bounds inside the
  development — the non-vacuity claim holds for every environment whose
  parameters clear them. The response-filter witnesses instantiate the poll
  budget at `cap ∈ {1, 2}`; the theorem itself is proven for all `cap >= 1`.
- **Drain membership is modeled, not derived** (trusted data plumbing): drain *occurrence* per tick is proven
  from executor invariants, but the constraint that a drain takes every queued task
  (fair, complete draining) is a clause of the composed transition relation. The
  TaskWake path's external-arrival assumption (`taskwake_arrival_within`)
  is likewise membership-shaped rather than direct-to-FIFO: the cross-task wake's
  arrival is fused with membership in the FIRST post-window `Drain{TaskWake}` (a
  parked arrival has no observable event of its own, so this fusion is the
  irreducible residue of the unmodeled utility kernel); the drain's *existence* is
  proven (`single_progress_has_drain_task_wake`) and Drain→FIFO→poll is derived.
- **io resource-hold assumption is currency-guarded** (assumption on correct user-code behavior): the
  environment obliges an io registration to remain registered only while some task
  is CURRENTLY awaiting its rid (io-active + waker set in the current poll cycle +
  last poll Pending — `io_rid_current_poll_awaited`; the timer side carries the
  analogous guard). Once the waiter is polled the guard turns off, so normal
  wake→poll(Ready)→drop cleanup traces are in the theorem domain. One class of
  traces remains excluded: a task externally aborted/dropped mid-await whose rid
  is deregistered while the guard is still on — task abort is unmodeled.
- **io readiness obligation is cancellation-guarded and carries its own
  bound** (assumption on the external environment; user cancellation lifts it): `io_ready_forward_here` owes an `IoEventReady`
  only if no successful io deregistration of the rid follows the last SetWaker —
  a cancelled wait (rid deregistered after the waker was set) owes no readiness,
  matching mio, so cancellation traces are in the env domain. Its poll-event bound
  is the dedicated environment constant `get_io_ready_bound` (uninterpreted),
  decoupled from the task-completion bound `cap`; the proof budget is
  chunk = K + B + C + cap + 2 with B the io bound (io wake window B + 1 rounds).

- **The model's clock is idealized to strict monotonicity** (environment
  idealization; identified by audit): the env clause
  `timestamps_strictly_increasing` demands every pair of `GetCurrentTime`
  events observe strictly increasing timestamps, while the implementation
  clock (`get_current_time_action`) is millisecond-granularity and only
  non-strictly clamped (`result >= wheel.elapsed`). A run in which two clock
  reads land in the same millisecond therefore falls outside the theorem's
  □env-filtered domain — the theorem speaks to executions at the time scale
  where each observation sees a fresh timestamp. Strictness is load-bearing
  for the timer bound (the proof counts clock reads as progress toward the
  deadline); weakening it to non-decreasing would require a replacement
  progress source (e.g. a time-advances-across-park clause) and is left as
  future work.
- **One exec loop is exempt from termination checking** (implicit assumption):
  `Executor::pop_injection` (lion-executor `src/executor/tick.rs`) carries
  `#[verifier::exec_allows_no_decreases_clause]` — its drain loop over the
  injection channel is not proven terminating. Termination rests on the
  injection queue being finite at each tick (the same finite-arrival modeling
  the injection schedule makes explicit); a hostile unbounded producer could
  starve the tick. This is the only such exemption in the repository.
- **SMT resource-limit (`rlimit`) debt**: the project policy is
  `#[verifier::rlimit(N)]` with N ≤ 50 for new proofs. A legacy corpus of ~68
  items exceeds 50, concentrated where quantifier density is inherent:
  lion-liveness's inhabitation/witness constructions (concrete multi-event logs
  evaluated under every env clause) and lion-reactor's safety/park preservation
  lemmas. rlimit only raises the solver's resource budget — it has no soundness
  impact; the cost is verification-time fragility across Verus/Z3 versions.
  These are inventoried by `tools/audit_scan.sh`.

**Where the utilities sit.** The liveness proof models two actors: user tasks
(via bounded behavioral assumptions) and the runtime kernel (via the ghost log).
Real user tasks, however, interact with the kernel almost entirely through the
runtime's primitives — TcpStream, sleep, Notify, mpsc — so we extend a
verification method to them in lion-utility. Note that this verification does
NOT mechanically connect to the liveness proof's user-code assumptions: the
utilities are themselves user code, sitting on the far side of that assumption
boundary, and the two sides share no vocabulary or statement (the informal
five-step chain is documented in §4). Because the utilities must present a
Tokio-shaped API, they unavoidably carry substantial trusted glue — the interop
semantics involved (std Waker identity, generic payload moves, Drop/Pin, the
async surface) lie outside Verus's supported subset. The runtime core fares far
better on this axis: its logic is much denser than a primitive like TcpStream,
so its trusted residue is a thin leaf boundary rather than a thick shell. The
strategies are therefore inverted: the core is a verified body with trusted
per-function leaves at the OS edge, while each utility is a verified
decision-kernel state machine invoked by a trusted whole-module shell that
executes its decisions (see the lion-utility section in §4).

---

## 3. Full inventory

For handwritten items, file:line is the
`#[verifier::external_body]` attribute line; for items marked "(macro-generated)",
file:line is the `reactor_log_action!` / `executor_log_action!` invocation site —
the single external_body attribute lives in the macro body (reactor ext.rs:91,
executor ext.rs:32), whose ensures/frame clauses are shared verbatim by every
expansion, so auditing them all reduces to auditing the macro body once. Because
of this, `grep -rn "verifier::external_body"` is auxiliary only (109 attribute
lines stand for the 126 items); the AUTHORITATIVE inventory is these tables plus
the two macro-invocation lists. The "trusted postcondition" column summarizes
what the `ensures` clause claims — this is exactly what verification trusts
without checking. "no ensures" means the item is trusted only not to break
memory safety / type soundness.

Each item carries one of four categories:

- **semantic** — the ensures carries a nontrivial semantic claim (the trusted
  container models, the slot-mutation leaves' exact effects incl. `level_counts`
  increments, view-matching clones);
- **ghost-log** — the ensures says only "the ghost log gains one fixed-shape event;
  every other field unchanged" (the begin/end action and `log_*_action` families;
  rows that also perform a real mio/waker effect say so);
- **raw** — zero or near-zero ensures: a claim-free primitive effect;
- **view** — opaque type wrapper or uninterpreted spec-view declaration.

Tally: 126 items = 30 semantic + 26 ghost-log + 45 raw + 25 view.

A pedantic satisfiability note on the exact-effect (`semantic`) rows: ensures of
the form `count == old(count) + 1` carry no overflow-side `requires`, so at the
`u64::MAX`/`usize::MAX` boundary the trusted postcondition is unsatisfiable while
the real body would wrap or panic. Reaching that state needs ~2^64 live
registrations, so it is physically unreachable; noted here for completeness.

### lion-reactor (57 items)

| file:line | fn name | category | trusted postcondition |
|---|---|---|---|
| src/resource_slot_wrapper.rs:10 | `struct ResourceSlotWrapper` | view | opaque type (wraps waker-holding `ResourceSlot`); no ensures |
| src/resource_slot_wrapper.rs:18 | `ResourceSlotWrapper::view` | view | uninterpreted spec view onto `ResourceSlotView` |
| src/resource_slot_wrapper.rs:25 | `ResourceSlotWrapper::new_timer` | semantic | result views as `Timer { entry@, waker@ }` |
| src/resource_slot_wrapper.rs:37 | `ResourceSlotWrapper::new_io` | semantic | result views as `Io { read_waker: None, write_waker: None }` |
| src/resource_slot_wrapper.rs:49 | `ResourceSlotWrapper::is_timer` | semantic | returned bool equals `self@.is_timer()` |
| src/resource_slot_wrapper.rs:56 | `ResourceSlotWrapper::is_io` | semantic | returned bool equals `self@.is_io()` |
| src/resource_slot_wrapper.rs:63 | `ResourceSlotWrapper::with_read_waker` | semantic | result is `Io` with read_waker = `waker@`, write_waker preserved |
| src/resource_slot_wrapper.rs:79 | `ResourceSlotWrapper::with_write_waker` | semantic | result is `Io` with write_waker = `waker@`, read_waker preserved |
| src/resource_slot_wrapper.rs:95 | `ResourceSlotWrapper::clone_timer_waker` | semantic | cloned waker views equal to the slot's stored timer waker |
| src/resource_slot_wrapper.rs:106 | `ResourceSlotWrapper::clone_read_waker` | semantic | Some-ness matches slot's read_waker; value views equal when Some |
| src/resource_slot_wrapper.rs:119 | `ResourceSlotWrapper::clone_write_waker` | semantic | Some-ness matches slot's write_waker; value views equal when Some |
| src/reactor/ext.rs:105 | `Reactor::park_begin_action` | ghost-log | ghost log gains exactly one `Park{result:None}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:112 | `Reactor::park_end_action` | ghost-log | ghost log gains `Park{result:Some}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:119 | `Reactor::register_io_begin_action` | ghost-log | ghost log gains `RegisterIoResource{result:None}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:126 | `Reactor::register_io_end_action` | ghost-log | ghost log gains `RegisterIoResource{result:Some}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:133 | `Reactor::deregister_io_begin_action` | ghost-log | ghost log gains `DeregisterIoResource{result:None}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:140 | `Reactor::deregister_io_end_action` | ghost-log | ghost log gains `DeregisterIoResource{result:Some}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:147 | `Reactor::set_waker_begin_action` | ghost-log | ghost log gains `SetWaker{result:None}` recording rid/interest/waker; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:154 | `Reactor::set_waker_end_action` | ghost-log | ghost log gains `SetWaker{result:Ok(())}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:162 | `Reactor::register_timer_begin_action` | ghost-log | ghost log gains `RegisterTimer{result:None}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:170 | `Reactor::register_timer_end_action` | ghost-log | ghost log gains `RegisterTimer{result:Some}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:178 | `Reactor::deregister_timer_begin_action` | ghost-log | ghost log gains `DeregisterTimer{result:true}`; exec fields unchanged (macro-generated) |
| src/reactor/ext.rs:189 | `Reactor::log_get_current_time_action` | ghost-log | ghost log gains `GetCurrentTime{t@}`; exec fields unchanged (macro-generated; clock monotonicity is PROVEN in the verified wrapper `get_current_time_action`, which clamps the raw reading to `wheel.elapsed`) |
| src/reactor/ext.rs (publish_cached_now) | `Reactor::publish_cached_now` | raw | no ensures — writes the park-cycle clock observation into the trusted handle layer's thread-local cache (`handle.rs CACHED_NOW`), entirely outside verified state; readers (Sleep::poll) treat it as an optimization hint with a real-clock fallback, and a stale value can only delay a completion decision, never produce an early fire |
| src/reactor/ext.rs:199 | `Reactor::register_io_source_action` | ghost-log | log gains matching `Outbound::RegisterIoResource{result}`; source/fields unchanged (real effect: mio `registry.register` on the verified rid→token codec; mio faithfulness is the residual trust) |
| src/reactor/ext.rs:225 | `Reactor::deregister_io_source_action` | ghost-log | log gains matching `Outbound::DeregisterIoResource{result}`; source/fields unchanged (real effect: mio `registry.deregister`) |
| src/reactor/ext.rs:248 | `Reactor::poll_events_action` | ghost-log | log gains `Outbound::PollEvents` whose logged count equals the returned event vec length; fields unchanged (real effect: mio poll — tokens returned faithfully and readable/writable flags matching real readiness are the residual trust) |
| src/reactor/ext.rs:279 | `Reactor::io_event_ready_action` | ghost-log | ghost log gains `IoEventReady{event@}`; exec fields unchanged |
| src/reactor/ext.rs:319 | `Reactor::wake_task_action` | ghost-log | log gains `WakeTask{waker@, source_rid@}`; fields unchanged (real effect: `wake_by_ref`) |
| src/types/waker.rs:7 | `struct Waker` | view | opaque wrapper of `std::task::Waker` |
| src/types/waker.rs:15 | `Waker::view` | view | uninterpreted spec view onto `WakerView` |
| src/types/waker.rs:22 | `Waker::clone` | semantic | clone views equal to original (`result@ == self@`) |
| src/reactor/new.rs:17 | `Reactor::mio_setup` | raw | no ensures — creates the OS handles (mio Poll / Events / cross-thread Waker); all 8 empty-state invariants are PROVEN downstream in verified `Reactor::new` |
| src/types/io_event_queue.rs:6 | `struct IoEventQueue` | view | opaque wrapper of `mio::Events` |
| src/types/io_event_queue.rs:14 | `IoEventQueue::view` | view | uninterpreted spec view (`int`) |
| src/types/io_event_queue.rs:21 | `IoEventQueue::with_capacity` | raw | no ensures (opaque effect) |
| src/types/source.rs:6 | `struct Source` | view | opaque wrapper of `&mut dyn mio::event::Source` |
| src/types/source.rs:14 | `Source::view` | view | uninterpreted spec view onto `SourceView` |
| src/types/interrupt_handle.rs:34 | `struct InterruptHandle` | view | opaque wrapper (Arc + AtomicBool + mio::Waker) |
| src/types/interrupt_handle.rs:42 | `InterruptHandle::view` | view | uninterpreted spec view (`int`) |
| src/types/interrupt_handle.rs:49 | `InterruptHandle::clone` | raw | no ensures (opaque effect) |
| src/types/interrupt_handle.rs:58 | `InterruptHandle::wake` | raw | no ensures (opaque effect) — cross-thread mio wake, dedup via AtomicBool |
| src/types/interrupt_handle.rs:63 | `InterruptHandle::reset` | raw | no ensures (opaque effect) — clears the notified flag |
| src/reactor/timer.rs:415 | `Reactor::next_deadline` | raw | no ensures (opaque effect) — reads wheel's next deadline |
| src/reactor/timer.rs:424 | `Reactor::flush_pending_deregister` | raw | no ensures (opaque effect) — applies the deferred wheel + slab removal, state havoced |
| src/types/io_result.rs:6 | `struct IoError` | view | opaque wrapper of `std::io::Error` |
| src/types/io_result.rs:14 | `IoError::view` | view | uninterpreted spec view (`int`) |
| src/types/io_result.rs:48 | `IoError::resource_id_overflow` | raw | no ensures (opaque effect) |
| src/types/time.rs:67 | `Duration::from_std` | raw | no ensures (opaque effect) |
| src/types/time.rs:74 | `Instant::now` | raw | no ensures (opaque effect) — millis since process-start baseline |
| src/types/time.rs:82 | `Instant::elapsed` | raw | no ensures (opaque effect) — saturating sub against now() |
| src/types/time.rs:92 | `Instant::add` | raw | no ensures (opaque effect) — saturating add |
| src/types/time.rs:101 | `Instant::sub` | raw | no ensures (opaque effect) — saturating sub |
| src/reactor/park.rs:22 | `mark_io_readable` | raw | no ensures (opaque effect) — sets TLS readiness bit |
| src/reactor/park.rs:27 | `mark_io_writable` | raw | no ensures (opaque effect) — sets TLS readiness bit |
| src/types/poll.rs:5 | `struct Poll` | view | opaque wrapper of `mio::Poll` |
| src/types/poll.rs:13 | `Poll::view` | view | uninterpreted spec view (`int`) |

### lion-executor (54 items)

| file:line | fn name | category | trusted postcondition |
|---|---|---|---|
| src/types/boxed_future.rs:10 | `struct BoxedFuture` | view | opaque wrapper of `Pin<Box<dyn Future>>` |
| src/types/boxed_future.rs:18 | `BoxedFuture::view` | view | view is the constant `0int` (all futures spec-indistinguishable) |
| src/collections/vec_deque.rs:9 | `struct VecDeque<T>` | view | opaque wrapper of `std::collections::VecDeque` |
| src/collections/vec_deque.rs:18 | `VecDeque::view` | view | uninterpreted spec view as `Seq<T::V>` |
| src/collections/vec_deque.rs:25 | `VecDeque::new` | semantic | fresh deque views as the empty sequence |
| src/collections/vec_deque.rs:32 | `VecDeque::push_back` | semantic | view becomes `old@.push(value@)` |
| src/collections/vec_deque.rs:39 | `VecDeque::push_front` | raw | no ensures (opaque effect) |
| src/collections/vec_deque.rs:45 | `VecDeque::pop_front` | semantic | FIFO pop: nonempty ⇒ returns head, view becomes tail; empty ⇒ None, unchanged |
| src/collections/vec_deque.rs:61 | `VecDeque::pop_back` | raw | no ensures (opaque effect) |
| src/collections/vec_deque.rs:67 | `VecDeque::is_empty` | semantic | returned bool equals `self@.len() == 0` |
| src/collections/vec_deque.rs:74 | `VecDeque::len` | semantic | returned usize equals `self@.len()` |
| src/collections/vec_deque.rs:81 | `VecDeque::clear` | semantic | view becomes the empty sequence |
| src/collections/vec_deque.rs:90 | `VecDeque::default` | semantic | default deque views as the empty sequence |
| src/collections/vec_deque.rs:99 | `From<VecDeque<T>> for Vec<T>` | raw | no ensures (opaque effect) |
| src/types/instant.rs:15 | `Instant::view` | view | uninterpreted spec view (`nat`) |
| src/types/instant.rs:22 | `Instant::now` | raw | no ensures (opaque effect) |
| src/types/instant.rs:28 | `Instant::elapsed` | raw | no ensures (opaque effect) |
| src/types/instant.rs:34 | `Instant::less_than` | raw | no ensures (opaque effect) |
| src/types/instant.rs:40 | `Instant::duration_since` | raw | no ensures (opaque effect) — saturating subtraction |
| src/types/instant.rs:48 | `From<ReactorInstant>` | raw | no ensures (opaque effect) |
| src/collections/mpsc_queue.rs:8 | `struct MpscSender<T>` | view | opaque wrapper of `std::sync::mpsc::Sender` |
| src/collections/mpsc_queue.rs:14 | `struct MpscReceiver<T>` | view | opaque wrapper of `std::sync::mpsc::Receiver` |
| src/types/reactor.rs:7 | `struct Reactor` | view | opaque wrapper of lion-reactor `Reactor` |
| src/types/reactor.rs:12 | `struct ReactorGuard` | view | opaque wrapper of `LionReactorGuard` |
| src/types/reactor.rs:18 | `Reactor::new` | raw | no ensures (opaque effect) |
| src/types/duration.rs:14 | `Duration::view` | view | uninterpreted spec view (`nat`) |
| src/types/duration.rs:21 | `Duration::zero` | raw | no ensures (opaque effect) |
| src/types/duration.rs:27 | `Duration::from_millis` | raw | no ensures (opaque effect) |
| src/types/duration.rs:33 | `Duration::from_secs` | raw | no ensures (opaque effect) |
| src/types/duration.rs:39 | `Duration::as_millis` | raw | no ensures (opaque effect) |
| src/types/duration.rs:45 | `Duration::into_reactor` | raw | no ensures (opaque effect) |
| src/types/duration.rs:53 | `From<ReactorDuration>` | raw | no ensures (opaque effect) |
| src/types/duration.rs:61 | `From<Duration> for ReactorDuration` | raw | no ensures (opaque effect) |
| src/executor/ext.rs:46 | `Executor::tick_begin_action` | ghost-log | ghost log gains `Tick{result:None}`; local_queue/task_slab/ledger unchanged (macro-generated) |
| src/executor/ext.rs:51 | `Executor::tick_end_action` | ghost-log | ghost log gains `Tick{result:Some(())}`; local_queue/task_slab/ledger unchanged (macro-generated) |
| src/executor/ext.rs:58 | `Executor::log_poll_task_action` | ghost-log | ghost log gains `PollTask{task_id, task@, result}`; local_queue/task_slab/ledger unchanged (macro-generated) |
| src/executor/ext.rs:69 | `Executor::log_pop_injection_action` | ghost-log | ghost log gains `PopInjection{task@}` recording exactly what the verified layer decided; state unchanged (macro-generated) |
| src/executor/ext.rs:78 | `Executor::log_drain_task_wake_action` | ghost-log | ghost log gains one `Drain{TaskWake, ids@}` recording exactly the ids the verified layer kept; state unchanged (macro-generated) |
| src/executor/ext.rs:86 | `Executor::log_drain_reactor_wake_action` | ghost-log | ghost log gains one `Drain{ReactorWake, ids@}`; state unchanged (macro-generated) |
| src/executor/ext.rs:94 | `Executor::log_drain_deferred_action` | ghost-log | ghost log gains one `Drain{Deferred, ids@}`; state unchanged (macro-generated) |
| src/executor/ext.rs:110 | `Executor::poll_future_raw` | raw | shape-only ensures (Some task ⇒ task handed back and result Ready/Pending; None ⇒ Pending) — free function with NO executor access runs the user future; residual trust: user wake/spawn effects route through TLS. The old `poll_task_action` contract is reassembled in verified code |
| src/executor/ext.rs:158 | `Executor::poll_task_invalid_action` | ghost-log | ghost log gains `PollTask{result: Invalid}`; state unchanged |
| src/executor/ext.rs:176 | `Executor::try_recv_raw` | raw | no ensures — plain mpsc `try_recv`, no executor access, no claims about what comes out; TID freshness is enforced by a verified ledger check in `pop_injection_action` |
| src/executor/ext.rs:245 | `Executor::park_action` | ghost-log | log gains `Park`; local_queue/task_slab/ledger unchanged (real effect: reactor flush + park) |
| src/executor/ext.rs:265 | `Executor::reset_and_drain_cross_thread_action` | raw | no ensures (opaque effect) — resets interrupt, drains cross-thread queue into TLS |
| src/executor/ext.rs:272 | `Executor::has_deferred_action` | raw | no ensures (opaque effect) — TLS queue probe |
| src/executor/ext.rs:278 | `Executor::has_reactor_ready_action` | raw | no ensures (opaque effect) — TLS queue probe |
| src/executor/ext.rs:284 | `Executor::has_task_ready_action` | raw | no ensures (opaque effect) — TLS queue probe |
| src/executor/ext.rs:290 | `Executor::take_block_on_yielded_action` | raw | no ensures (opaque effect) — takes TLS yield flag |
| src/executor/ext.rs:300 | `Executor::take_task_ready_from_tls` | raw | no ensures — hands over the TLS task-wake ids as a plain Vec, no claims; fabricated TIDs are filtered by the verified ledger layer (`filter_and_enqueue`), which PROVES the old drain ensures |
| src/executor/ext.rs:307 | `Executor::take_reactor_ready_from_tls` | raw | no ensures — TLS reactor-wake ids as a plain Vec, no claims (verified filter downstream) |
| src/executor/ext.rs:313 | `Executor::take_deferred_from_tls` | raw | no ensures — TLS deferred ids as a plain Vec, no claims (verified filter downstream) |
| src/executor/poll_task.rs:11 | `clear_task_notified` | raw | no ensures (opaque effect) — clears TLS notified flag |
| src/executor/enter.rs:8 | `Executor::enter` | raw | no ensures (opaque effect) — installs reactor TLS context |

### lion-timer-wheel (11 items)

| file:line | fn name | category | trusted postcondition |
|---|---|---|---|
| src/wheel.rs:22 | `WheelPos::view` | view | view is the identity (`*self`) |
| src/wheel.rs:1473 | `TimerWheel::get_deadline` | raw | no ensures (opaque effect) — map lookup |
| src/wheel.rs:2984 | `TimerWheel::slot_push` | semantic | exactly slot `[level][slot]` gains `rid` at the end; all other slots/fields unchanged; structural_wf preserved; `level_counts[level]` exactly +1, other levels unchanged |
| src/wheel.rs:3014 | `TimerWheel::slot_swap_remove` | semantic | returns element at `idx`; slot shrinks by 1 with swap-remove semantics; all other state unchanged; `level_counts[level]` exactly −1 |
| src/wheel.rs:3058 | `TimerWheel::slot_pop` | semantic | slot loses exactly its last element (`drop_last`); all other state unchanged; `level_counts[level]` exactly −1 |
| src/wheel.rs:3087 | `TimerWheel::slot_drain` | semantic | returns exactly the old slot contents; slot becomes empty; all other state unchanged; `level_counts[level]` exactly −len |
| src/helpers.rs:5 | `wrapping_sub_u64` | semantic | if `a >= b` then result equals `a - b` (wrapping case unconstrained) |
| src/vec_map.rs:166 | `VecMap::grow_front` | semantic | offset becomes `key`; None slots prepended; existing slots shifted intact; `count` unchanged |
| src/vec_map.rs:188 | `VecMap::ensure_slot` | semantic | index `rel` in bounds; existing slots preserved; new slots None; `count` unchanged |
| src/vec_map.rs:212 | `VecMap::set_slot` | semantic | `inner@` becomes `old.update(rel, Some(value))`; `count` +1 exactly iff slot was None (the `count_wf` coupling behind the now-VERIFIED O(1) `is_empty`) |
| src/vec_map.rs:231 | `VecMap::take_at` | semantic | returns old slot value; slot becomes None; all else unchanged; `count` −1 exactly iff slot was Some |

(`scan_wheel_min` and `VecMap::is_empty` are verified functions, not trusted
leaves: the min-scan is proven against the `level_band` invariant and the
per-level occupancy counters; `is_empty` is proven via the `count_wf` coupling.)

### lion-slab (4 items)

| file:line | fn name | category | trusted postcondition |
|---|---|---|---|
| src/slab.rs:56 | `Slab::grow_front` | semantic | offset becomes `key`; None slots prepended; existing slots shifted intact |
| src/slab.rs:76 | `Slab::ensure_slot` | semantic | index `rel` in bounds; existing slots preserved; appended slots None |
| src/slab.rs:95 | `Slab::set_slot` | semantic | `inner@` becomes `old.update(rel, Some(value))` |
| src/slab.rs:229 | `Slab::take_at` | semantic | returns old slot value; slot becomes None; all else unchanged |

Also note `Slab::get_mut` (`src/slab.rs:213`) — `#[verifier::external]`, but now
SAFE code: a bounds-checked body mirroring the verified `get` (no unsafe anywhere
in the crate). It stays external only because Verus cannot express `&mut` returns,
so its behavior is still invisible to verification.

### lion-utility (0 items)

No `external_body` attributes — but NOT trust-free: its trust is structured
differently (whole-module trusted glue rather than per-function edges). See the
dedicated "lion-utility (glue layer)" section under §4 below.

---

## 4. Per-crate trust summaries

**lion-reactor (56).** The OS boundary itself: mio epoll registration/polling
and handle creation (`mio_setup`), the raw clock read (`Instant::now` — the
monotonicity the timer proofs use is established by a verified clamp, not
trusted), `std::task::Waker` cloning/waking, plus the macro-generated ghost-log
action family (each trusted to append exactly one history event and touch
nothing else). `Reactor::new` is verified: only the mio handles are opaque.

**lion-executor (54).** Scheduling plumbing: claim-free raw takers for the TLS
wake queues and the mpsc injection channel (`try_recv_raw`,
`take_*_from_tls`), the single point where arbitrary user code runs
(`poll_future_raw`, a free function with no executor access), the
macro-generated log-action family, and a semantic `VecDeque` FIFO model the
local-queue liveness derivation rides on. TID freshness and drain
append/injected facts are verified in the wrapping layer (ledger + filters),
not trusted.

**lion-timer-wheel (11).** A trusted framing layer over `Vec` slot mutations —
each ensures pins the exact single-slot effect plus the exact `level_counts`
delta. The min-scan and emptiness checks on top are verified against these
leaves.

**lion-slab (4).** Four private leaf operations with exact effect-on-view specs; all
public Slab API on top is verified. Plus the `#[verifier::external]` `get_mut` noted
above.

### lion-utility (glue layer)

lion-utility has ZERO `external_body` attributes — that is the point: its trust is
structured differently from the other crates. Each utility is a VERIFIED KERNEL (a
pure Verus state machine; ~2,400 verified lines total) plus WHOLE-MODULE TRUSTED
GLUE (~2,700 lines): every glue file carries
`#![cfg_attr(verus_keep_ghost, verus::trusted)]` and contains no `verus!{}` code at
all — it is plain Rust that Verus never sees. Consequently the kernels' `requires`
clauses (e.g. `signal_step`'s `permit < u64::MAX`, `ChannelKernel::fill`'s
`reserved > 0`) are upheld by convention at glue call sites, not checked statically
or at runtime; regression tests (`tests/cancel.rs`, `tests/decisions.rs`, 24 tests
total) guard the conventions the verifier cannot.

| utility | verified kernel (lines) | trusted glue (lines) |
|---|---|---|
| waiter (shared) | 902 (kernel+coupling+proof+liveness) | — (backs the wakeup side of everything below) |
| oneshot | 129 | 120 |
| mpsc | 186 | ~500 |
| broadcast | 94 | ~250 |
| watch | 77 | ~240 |
| mutex / notify / semaphore | reuse waiter (0 own) | 152 / 135 / 204 |
| sleep | 505 | 86 |
| timeout | 34 | 60 |
| interval | 57 | 63 |
| tcp | 398 | ~512 |
| udp | reuses tcp's IoKernel (0 own) | 163 |
| fs + task + addr | none (unverified) | ~212 |

**What the kernels prove (machine-checked):** the waiter queue/permit coupling
(`queue_view(queue) == waiters(log)`, `permit == init + available_permits(log)` —
no phantom/lost waiters, a signal wakes the true FIFO head, exact permit
accounting, and a verified cancellation step `remove_step` +
`CancelWaker` event); channel FIFO with no holes / no loss / no duplication /
capacity bounds; and decision correctness (tcp's `Arm ⟺ would-block`, timeout's
`Pending ⟺ both sub-futures pending`, broadcast's `Lagged ⟺ cursor < oldest`,
interval's `deadline == first + fires×period`).

**What the glue is trusted for:** the identity binding between the real
`std::task::Waker` and the kernel's `WakerView = int` id; the call protocol (right
kernel step, right order, `requires` upheld); and the delivery loops that map woken
ids to real wakers and move the real `T` values. Note explicitly: the
reactor-mediated kernels (sleep, tcp) discharge the waker-matching invariant with
FABRICATED ghost wakers (`let ghost w: WakerView = arbitrary();`) — that both the
tick waker and the registered waker denote the real `cx.waker()` is pure trust.
The WaiterKernel is stronger here: its ids are glue-supplied and coupled to the
verified queue.

**Honest chain to the composed proof** (there is NO machine-checked link — the
two sides use different vocabularies, `WakerView`/`WakeWaker` vs UID/`Woken`, and
share no statement):

1. a peer task signals (send / unlock / notify) — environmental assumption;
2. the kernel emits `WakeWaker` for the true FIFO-head waiter — MACHINE-CHECKED
   (the crate's real per-primitive content);
3. the glue maps the id to the real `Waker` and calls `wake()` — trusted, now
   regression-tested including the cancellation paths;
4. the wake arrives in the executor's TaskWake drain within a bound —
   lion-liveness's `taskwake_arrival_within` ASSUMPTION (see §2 above);
5. Drain→FIFO→poll — derived in lion-liveness.

**Why the seam carries regression tests:** the liveness hazards this layer must
guard against — a cancelled waiter silently swallowing a granted permit (a mutex
held forever), or phantom permit accumulation leaving a parked sender unwakeable
with a free slot — are invisible to the verifier, since they live in the glue's
conventions rather than in the kernels. Cancellation safety (`Drop` impls on all
waiting futures backed by the verified `CancelWaker`/`remove_step` kernel step),
mechanical consumption of every kernel decision, interval re-arming from its
verified deadline ledger, and sleep failing loud on registration failure are
therefore each pinned by the regression suites (`tests/cancel.rs`,
`tests/decisions.rs`).
