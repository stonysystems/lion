# Lion — Trusted Computing Base (TCB) & Known Limitations

Every verification claim in this repository is machine-checked **modulo** the trusted
base inventoried here. This file lists, per item, exactly what is trusted and not
verified. Regenerate the raw list with:

```
grep -rn "external_body" lion-reactor/src lion-executor/src lion-timer-wheel/src lion-slab/src lion-utility/src
```

**Count**: 119 trusted `external_body` items — lion-reactor 58, lion-executor 54,
lion-timer-wheel 7, lion-slab 0, lion-utility 0. By trust kind: 22 `semantic`,
26 `ghost-log`, 46 `raw`, 25 `view` (definitions in §3). Every item carries its
own attribute line, so the grep above finds exactly the items (the two ghost-log
families used to expand from `macro_rules!`, whose one attribute line stood for
all their items; they are now written out). Beyond these: two `#[verifier::external]` items (`lion-slab
Slab::get_mut` — a std `HashMap::get_mut`, external only because Verus cannot
express `&mut` returns — and `Slab::values`, a std `HashMap::values` iterator
used only by unverified code), and the pinned Verus toolchain (`setup.sh`,
`verus.config`) with its Z3 solver. That toolchain includes vstd's model of std
`HashMap` (`vstd/std_specs/hash.rs`: `assume_specification`s for
`new`/`insert`/`get`/`remove`/`contains_key`/`is_empty`, plus `admit()`ed
axioms that `u64` obeys the key model and `RandomState` builds valid hashers),
which the two id-keyed maps — `lion-slab::Slab` and the timer wheel's `VecMap`
— rest on in place of their former eight trusted slot leaves.

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
   event and touching nothing else. The family sits in two blocks (reactor
   `src/reactor/ext.rs`, executor `src/executor/ext.rs`) whose items share one
   frame-clause block verbatim, so auditing them means checking each item's
   pushed event against its name. They used to expand from two `macro_rules!`
   (`reactor_log_action!` / `executor_log_action!`); they are written out now,
   with identical attributes, signatures, events and frame clauses, so that no
   `verus!` block is macro-generated (a source pre-pass that erases literal
   `verus!` items does not expand macros). What remains trusted is the call
   protocol (each action invoked once, in order, around its real effect);
   mechanized refinement is out of scope.
2. **OS boundary (the `OsBackend` seam)** — `poll_events_action` (the
   backend's wait; tokens returned faithfully; event flags reflect real
   readiness — the rid<->token codec itself is verified),
   `register/deregister_io_source_action`, `Instant::now`,
   `Reactor::mio_setup`/`backend_setup` (handle creation, no semantic ensures),
   and the backend behind them: `lion_reactor::os::OsBackend`, implemented by
   Lion's `MioBackend` (default feature `mio`) or by an embedder. What the
   reactor relies on is the edge-triggered contract written down in
   `lion-reactor/src/os/mod.rs`; a backend that swallows a readiness
   transition or an interrupt signal loses a wakeup, which no proof sees.
3. **`Executor::poll_future_raw` + the task wakers** — user future code runs behind
   a free function that cannot touch the executor by construction; the remaining
   trust is that user wake/spawn effects route through the TLS side-channels the
   drain path consumes (every executor waker is an `Arc<ExecutorWaker>` behind
   std `Wake`; no hand-written `RawWakerVTable` remains), and that cloned reactor
   wakers view-match (lion-reactor `Waker::clone`).
4. **TLS wake plumbing raw takers** — `take_{task,reactor,deferred}_*_from_tls` /
   `try_recv_raw` hand over a plain Vec/Option with NO claims; fabricated TIDs are
   filtered by the verified ledger layer, lost wakes remain covered by the
   model-side arrival assumptions (`taskwake_arrival_within`, injection schedule).
5. **Trusted data-structure models** — vstd-style ensures on `VecDeque`
   (FIFO-as-sequence semantics that the local-queue liveness derivation rides on),
   the slot-mutation leaves of the timer wheel (including their exact
   `level_counts` deltas), and vstd's own std `HashMap` specification, which
   the id-keyed maps (`lion-slab::Slab`, the wheel's `VecMap`) call directly.

---

## 2. Known modeling limitations

- **Ids are monotone counters** (internal data management): resource ids and task ids are allocated by
  ever-increasing u64 counters and never reused, and the no-reuse liveness
  theorem is faithful to exactly this implementation. Memory does NOT grow
  with the ids ever allocated: every container keyed by id holds live entries
  only — the ResourceSlab and the task slab (`lion-slab::Slab`) and the timer
  wheel's `deadlines`/`positions` (`VecMap`) are std `HashMap`s with unchanged
  `Map` views and contracts, and the trusted TLS tables are a
  `HashMap<u64, u8>` of io readiness flags (an entry lives from
  `init_readiness` to deregistration) and a `HashSet<u64>` of notified task ids
  (an entry lives from wake to the next poll of that id). The one remaining
  id-proportional structure is the executor's TID ledger, a history set by
  design (1 bit per task ever spawned, 125 KB per million tasks).
  `lion-utility/tests/bounded_memory.rs` churns ~200k task ids and ~600k
  resource ids and asserts resident memory stays flat after warm-up. The id
  space is u64 per reactor/executor; resource-id exhaustion returns
  `resource_id_overflow`. In lion-reactor the disabled reuse branches (`free_rids.push`/
  `pop`) are commented out behind `[RID-REUSE DISABLED]` markers while the
  `free_rids_wf` invariant plumbing is retained live (it appears in
  `alloc_resource_id`'s contract and its preservation lemmas are still called);
  the invariant is maintained over a provably-empty free list, so it constrains
  nothing today and is ready if id reuse (generational ids) is ever restored.
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
  is deregistered while the guard is still on — task abort is unmodeled. The
  public API reaches that class: `JoinHandle::abort`, a task panic, and dropping
  a runtime with tasks alive all drop a task's future, and so deregister its io,
  without the model's cooperation. Abort and panic are shaped so the executor
  proofs need no new event: the task's wrapper (`TaskCell`, trusted glue) is
  woken, drops the future inside that poll and returns Ready, so the log shows
  an ordinary `PollTask{Ready}` that retires the task. But if the dropped future
  was awaiting io, the deregistration inside that poll falls while the guard
  is on, and the trace leaves the theorem domain from there. Nothing is lost by
  it for the aborted or panicked task itself, whose handle resolves with a
  `JoinError` instead of an output; the theorem says nothing about the rest of
  such a run.
- **io readiness obligation is cancellation-guarded and carries its own
  bound** (assumption on the external environment; user cancellation lifts it): `io_ready_forward_here` owes an `IoEventReady`
  only if no successful io deregistration of the rid follows the last SetWaker —
  a cancelled wait (rid deregistered after the waker was set) owes no readiness,
  matching mio, so cancellation traces are in the env domain. Its poll-event bound
  is the dedicated environment constant `get_io_ready_bound` (uninterpreted),
  decoupled from the task-completion bound `cap`; the proof budget is
  chunk = K + B + C + cap + 2 with B the io bound (io wake window B + 1 rounds).
- **`AsyncFd` waits are outside the modeled io path** (trusted glue; delivery
  unaffected): the composed model ties a task's io wait to the utility io
  kernel's log and routes the reactor's wake for it into the next
  `Drain{ReactorWake}` (`reactor_wake_arrival` / `reactor_wake_drain_step`,
  `lion-liveness/src/composed/spec/wake_queues.rs`), which matches the reactor
  waker that lion-utility's TCP and UDP glue register
  (`create_reactor_waker_for_current`). `AsyncFd` writes no utility log and
  registers the caller's `cx.waker()`: for a task's own waker that is a
  `WakeSource::Task` waker, whose wake lands in the TaskWake queue (as `Sleep`'s
  timer wake already does, a deviation documented in
  `lion-utility/src/time/sleep/future.rs`), and for a combinator's waker it is
  whatever the combinator does. The executor drains both queues at the same
  points (`next_task` and `park`), so the task is polled as promptly, but the
  theorem's io obligation says nothing about an `AsyncFd` wait. The caller's
  waker is needed for correctness: a combinator that polls a sub-future with a
  waker of its own is otherwise never told which sub-future to re-poll.
  Routing a wake by the context that fires it (the reactor's dispatch) instead
  of by the waker's source would align the queue; bringing an `AsyncFd` wait
  into the theorem would also need it to drive the io kernel's log.

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

For every item, file:line is the `#[verifier::external_body]` attribute line
(`grep -rn "verifier::external_body"` lists them one to one). The ghost-log
rows of `src/reactor/ext.rs` and `src/executor/ext.rs` share their frame
clauses verbatim within each crate and differ only in the event they push.
The "trusted postcondition" column summarizes what the `ensures` clause
claims — this is exactly what verification trusts without checking. "no ensures" means the item is trusted only not to break
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

Tally: 119 items = 22 semantic + 26 ghost-log + 46 raw + 25 view.

A pedantic satisfiability note on the exact-effect (`semantic`) rows: ensures of
the form `count == old(count) + 1` carry no overflow-side `requires`, so at the
`u64::MAX`/`usize::MAX` boundary the trusted postcondition is unsatisfiable while
the real body would wrap or panic. Reaching that state needs ~2^64 live
registrations, so it is physically unreachable; noted here for completeness.

### lion-reactor (58 items)

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
| src/reactor/ext.rs:92 | `Reactor::park_begin_action` | ghost-log | ghost log gains exactly one `Park{result:None}`; exec fields unchanged |
| src/reactor/ext.rs:104 | `Reactor::park_end_action` | ghost-log | ghost log gains `Park{result:Some}`; exec fields unchanged |
| src/reactor/ext.rs:116 | `Reactor::register_io_begin_action` | ghost-log | ghost log gains `RegisterIoResource{result:None}`; exec fields unchanged |
| src/reactor/ext.rs:128 | `Reactor::register_io_end_action` | ghost-log | ghost log gains `RegisterIoResource{result:Some}`; exec fields unchanged |
| src/reactor/ext.rs:140 | `Reactor::deregister_io_begin_action` | ghost-log | ghost log gains `DeregisterIoResource{result:None}`; exec fields unchanged |
| src/reactor/ext.rs:152 | `Reactor::deregister_io_end_action` | ghost-log | ghost log gains `DeregisterIoResource{result:Some}`; exec fields unchanged |
| src/reactor/ext.rs:164 | `Reactor::set_waker_begin_action` | ghost-log | ghost log gains `SetWaker{result:None}` recording rid/interest/waker; exec fields unchanged |
| src/reactor/ext.rs:176 | `Reactor::set_waker_end_action` | ghost-log | ghost log gains `SetWaker{result:Ok(())}`; exec fields unchanged |
| src/reactor/ext.rs:190 | `Reactor::register_timer_begin_action` | ghost-log | ghost log gains `RegisterTimer{result:None}`; exec fields unchanged |
| src/reactor/ext.rs:203 | `Reactor::register_timer_end_action` | ghost-log | ghost log gains `RegisterTimer{result:Some}`; exec fields unchanged |
| src/reactor/ext.rs:216 | `Reactor::deregister_timer_begin_action` | ghost-log | ghost log gains `DeregisterTimer{result:true}`; exec fields unchanged |
| src/reactor/ext.rs:231 | `Reactor::log_get_current_time_action` | ghost-log | ghost log gains `GetCurrentTime{t@}`; exec fields unchanged (clock monotonicity is PROVEN in the verified wrapper `get_current_time_action`, which clamps the raw reading to `wheel.elapsed`) |
| src/reactor/ext.rs (publish_cached_now) | `Reactor::publish_cached_now` | raw | no ensures — writes the park-cycle clock observation into the trusted handle layer's thread-local cache (`handle.rs CACHED_NOW`), entirely outside verified state; readers (Sleep::poll) treat it as an optimization hint with a real-clock fallback, and a stale value can only delay a completion decision, never produce an early fire |
| src/reactor/ext.rs:249 | `Reactor::register_io_source_action` | ghost-log | log gains matching `Outbound::RegisterIoResource{result}`; source/fields unchanged (real effect: `OsBackend::register(fd, token, interest)` on the verified rid→token codec; the backend's faithfulness is the residual trust) |
| src/reactor/ext.rs:273 | `Reactor::deregister_io_source_action` | ghost-log | log gains matching `Outbound::DeregisterIoResource{result}`; source/fields unchanged (real effect: `OsBackend::deregister(fd)`) |
| src/reactor/ext.rs:295 | `Reactor::poll_events_action` | ghost-log | log gains `Outbound::PollEvents` whose logged count equals the returned event vec length; fields unchanged (real effect: `OsBackend::wait` into the reused event buffer; each backend event becomes a Readable io event if readable, read-closed or error, and a Writable one if writable, write-closed or error — tokens returned faithfully and flags matching real readiness, per the contract in `src/os/mod.rs`, are the residual trust) |
| src/reactor/ext.rs:327 | `Reactor::io_event_ready_action` | ghost-log | ghost log gains `IoEventReady{event@}`; exec fields unchanged |
| src/reactor/ext.rs:378 | `Reactor::wake_task_action` | ghost-log | log gains `WakeTask{waker@, source_rid@}`; fields unchanged (real effect: `wake_by_ref`) |
| src/types/waker.rs:7 | `struct Waker` | view | opaque wrapper of `std::task::Waker` |
| src/types/waker.rs:15 | `Waker::view` | view | uninterpreted spec view onto `WakerView` |
| src/types/waker.rs:22 | `Waker::clone` | semantic | clone views equal to original (`result@ == self@`) |
| src/reactor/new.rs:34 | `Reactor::mio_setup` | raw | no ensures — (feature `mio`) creates Lion's `MioBackend` (mio Poll, event batch, eventfd waker) and wraps it with the reactor's event buffer and interrupt handle; all 8 empty-state invariants are PROVEN downstream in verified `Reactor::assemble`, which verified `Reactor::new` calls |
| src/reactor/new.rs:46 | `Reactor::backend_setup` | raw | no ensures — wraps an embedder's backend (already in the opaque `Poll`) with the event buffer and the interrupt handle over the backend's `OsInterrupt`; verified `Reactor::with_poll` then calls `assemble`, so a reactor over any backend carries the same proven invariants (`Reactor::with_backend` is the plain-Rust wrapper that boxes the backend into a `Poll`, since Verus does not support `dyn` types in verified signatures) |
| src/types/io_event_queue.rs:9 | `struct IoEventQueue` | view | opaque wrapper of the `Vec<OsEvent>` a backend's wait fills |
| src/types/io_event_queue.rs:17 | `IoEventQueue::view` | view | uninterpreted spec view (`int`) |
| src/types/io_event_queue.rs:24 | `IoEventQueue::with_capacity` | raw | no ensures (opaque effect) |
| src/types/source.rs:9 | `struct Source` | view | opaque wrapper of a raw fd |
| src/types/source.rs:17 | `Source::view` | view | uninterpreted spec view onto `SourceView` |
| src/types/interrupt_handle.rs:40 | `struct InterruptHandle` | view | opaque wrapper (Arc + AtomicBool + the backend's `Arc<dyn OsInterrupt>`) |
| src/types/interrupt_handle.rs:48 | `InterruptHandle::view` | view | uninterpreted spec view (`int`) |
| src/types/interrupt_handle.rs:55 | `InterruptHandle::clone` | raw | no ensures (opaque effect) |
| src/types/interrupt_handle.rs:64 | `InterruptHandle::wake` | raw | no ensures (opaque effect) — cross-thread `OsInterrupt::signal`, dedup via AtomicBool |
| src/types/interrupt_handle.rs:69 | `InterruptHandle::reset` | raw | no ensures (opaque effect) — clears the notified flag |
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
| src/reactor/park.rs:22 | `mark_io_readable` | raw | no ensures (opaque effect) — sets the rid's TLS readiness flag (no-op if the rid has no entry) |
| src/reactor/park.rs:27 | `mark_io_writable` | raw | no ensures (opaque effect) — sets the rid's TLS readiness flag (no-op if the rid has no entry) |
| src/types/poll.rs:9 | `struct Poll` | view | opaque wrapper of the reactor's `Box<dyn OsBackend>` |
| src/types/poll.rs:17 | `Poll::view` | view | uninterpreted spec view (`int`) |

### lion-executor (54 items)

| file:line | fn name | category | trusted postcondition |
|---|---|---|---|
| src/types/boxed_future.rs:12 | `struct BoxedFuture` | view | opaque wrapper of `Pin<Box<dyn Future>>` (always a `TaskCell`, see the runtime-glue table in §4) |
| src/types/boxed_future.rs:20 | `BoxedFuture::view` | view | view is the constant `0int` (all futures spec-indistinguishable) |
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
| src/types/reactor.rs:7 | `struct Reactor` | view | opaque wrapper of lion-reactor `Reactor`, plus the idle park bound `park_action` reads |
| src/types/reactor.rs:17 | `struct ReactorGuard` | view | opaque wrapper of `LionReactorGuard` |
| src/types/reactor.rs:23 | `Reactor::new` | raw | no ensures (opaque effect) |
| src/types/duration.rs:14 | `Duration::view` | view | uninterpreted spec view (`nat`) |
| src/types/duration.rs:21 | `Duration::zero` | raw | no ensures (opaque effect) |
| src/types/duration.rs:27 | `Duration::from_millis` | raw | no ensures (opaque effect) |
| src/types/duration.rs:33 | `Duration::from_secs` | raw | no ensures (opaque effect) |
| src/types/duration.rs:39 | `Duration::as_millis` | raw | no ensures (opaque effect) |
| src/types/duration.rs:45 | `Duration::into_reactor` | raw | no ensures (opaque effect) |
| src/types/duration.rs:53 | `From<ReactorDuration>` | raw | no ensures (opaque effect) |
| src/types/duration.rs:61 | `From<Duration> for ReactorDuration` | raw | no ensures (opaque effect) |
| src/executor/ext.rs:35 | `Executor::tick_begin_action` | ghost-log | ghost log gains `Tick{result:None}`; local_queue/task_slab/ledger unchanged |
| src/executor/ext.rs:45 | `Executor::tick_end_action` | ghost-log | ghost log gains `Tick{result:Some(())}`; local_queue/task_slab/ledger unchanged |
| src/executor/ext.rs:57 | `Executor::log_poll_task_action` | ghost-log | ghost log gains `PollTask{task_id, task@, result}`; local_queue/task_slab/ledger unchanged |
| src/executor/ext.rs:73 | `Executor::log_pop_injection_action` | ghost-log | ghost log gains `PopInjection{task@}` recording exactly what the verified layer decided; state unchanged |
| src/executor/ext.rs:87 | `Executor::log_drain_task_wake_action` | ghost-log | ghost log gains one `Drain{TaskWake, ids@}` recording exactly the ids the verified layer kept; state unchanged |
| src/executor/ext.rs:100 | `Executor::log_drain_reactor_wake_action` | ghost-log | ghost log gains one `Drain{ReactorWake, ids@}`; state unchanged |
| src/executor/ext.rs:113 | `Executor::log_drain_deferred_action` | ghost-log | ghost log gains one `Drain{Deferred, ids@}`; state unchanged |
| src/executor/ext.rs:157 | `Executor::poll_future_raw` | raw | shape-only ensures (Some task ⇒ task handed back and result Ready/Pending; None ⇒ Pending) — free function with NO executor access runs the user future; residual trust: user wake/spawn effects route through TLS. The body calls the plain-Rust `poll_task_contained`, which installs the task, polls it under `catch_unwind` and reports a poll that unwinds as Ready, so no unwind reaches the verified tick. The old `poll_task_action` contract is reassembled in verified code |
| src/executor/ext.rs:201 | `Executor::poll_task_invalid_action` | ghost-log | ghost log gains `PollTask{result: Invalid}`; state unchanged |
| src/executor/ext.rs:219 | `Executor::try_recv_raw` | raw | no ensures — plain mpsc `try_recv`, no executor access, no claims about what comes out; TID freshness is enforced by a verified ledger check in `pop_injection_action` |
| src/executor/ext.rs:288 | `Executor::park_action` | ghost-log | log gains `Park`; local_queue/task_slab/ledger unchanged (real effect: reactor flush + park; the park bound is 0 when the executor has ready work, else the wrapper's idle bound: 100 ms, or the caller's `Runtime::tick_with_timeout` bound. The verified reactor park accepts any bound and caps it at the next timer deadline) |
| src/executor/ext.rs:308 | `Executor::reset_and_drain_cross_thread_action` | raw | no ensures (opaque effect) — resets interrupt, drains cross-thread queue into TLS |
| src/executor/ext.rs:315 | `Executor::has_deferred_action` | raw | no ensures (opaque effect) — TLS queue probe |
| src/executor/ext.rs:321 | `Executor::has_reactor_ready_action` | raw | no ensures (opaque effect) — TLS queue probe |
| src/executor/ext.rs:327 | `Executor::has_task_ready_action` | raw | no ensures (opaque effect) — TLS queue probe |
| src/executor/ext.rs:333 | `Executor::take_block_on_yielded_action` | raw | no ensures (opaque effect) — takes TLS yield flag |
| src/executor/ext.rs:343 | `Executor::take_task_ready_from_tls` | raw | no ensures — hands over the TLS task-wake ids as a plain Vec, no claims; fabricated TIDs are filtered by the verified ledger layer (`filter_and_enqueue`), which PROVES the old drain ensures |
| src/executor/ext.rs:350 | `Executor::take_reactor_ready_from_tls` | raw | no ensures — TLS reactor-wake ids as a plain Vec, no claims (verified filter downstream) |
| src/executor/ext.rs:356 | `Executor::take_deferred_from_tls` | raw | no ensures — TLS deferred ids as a plain Vec, no claims (verified filter downstream) |
| src/executor/poll_task.rs:11 | `clear_task_notified` | raw | no ensures (opaque effect) — clears TLS notified flag |
| src/executor/enter.rs:8 | `Executor::enter` | raw | no ensures (opaque effect) — installs reactor TLS context |

### lion-timer-wheel (7 items)

| file:line | fn name | category | trusted postcondition |
|---|---|---|---|
| src/wheel.rs:22 | `WheelPos::view` | view | view is the identity (`*self`) |
| src/wheel.rs:1473 | `TimerWheel::get_deadline` | raw | no ensures (opaque effect) — map lookup |
| src/wheel.rs:2984 | `TimerWheel::slot_push` | semantic | exactly slot `[level][slot]` gains `rid` at the end; all other slots/fields unchanged; structural_wf preserved; `level_counts[level]` exactly +1, other levels unchanged |
| src/wheel.rs:3014 | `TimerWheel::slot_swap_remove` | semantic | returns element at `idx`; slot shrinks by 1 with swap-remove semantics; all other state unchanged; `level_counts[level]` exactly −1 |
| src/wheel.rs:3058 | `TimerWheel::slot_pop` | semantic | slot loses exactly its last element (`drop_last`); all other state unchanged; `level_counts[level]` exactly −1 |
| src/wheel.rs:3087 | `TimerWheel::slot_drain` | semantic | returns exactly the old slot contents; slot becomes empty; all other state unchanged; `level_counts[level]` exactly −len |
| src/helpers.rs:5 | `wrapping_sub_u64` | semantic | if `a >= b` then result equals `a - b` (wrapping case unconstrained) |

(`scan_wheel_min` and `VecMap::is_empty` are verified functions, not trusted
leaves: the min-scan is proven against the `level_band` invariant and the
per-level occupancy counters; `is_empty` is proven from vstd's `HashMap::is_empty`
spec. `VecMap` — the wheel's `deadlines`/`positions` — is a std `HashMap` whose
every operation is a direct std call specified by vstd, so its four former slot
leaves are gone; see the Count paragraph for the vstd model it now rests on.)

### lion-slab (0 items)

No `external_body` attributes. `Slab` is a std `HashMap<u64, V>`: `new`,
`insert`, `get` and `remove` are verified against vstd's `HashMap` specification
(see the Count paragraph), with the same `Map<nat, V::V>` view and contracts the
former vector window had.

Also note two `#[verifier::external]` items: `Slab::get_mut` (`src/slab.rs:102`),
a std `HashMap::get_mut` mirroring the verified `get`, external only because
Verus cannot express `&mut` returns; and `Slab::values` (`src/slab.rs:111`), a
std `HashMap::values` iterator whose only caller is unverified
(`ResourceSlab::is_empty_timers`). No unsafe anywhere in the crate; their
behavior is invisible to verification, and no verified code calls them.

### lion-utility (0 items)

No `external_body` attributes — but NOT trust-free: its trust is structured
differently (whole-module trusted glue rather than per-function edges). See the
dedicated "lion-utility (glue layer)" section under §4 below.

---

## 4. Per-crate trust summaries

**lion-reactor (58).** The OS boundary itself: registration and polling through
the `OsBackend` seam and handle creation (`mio_setup`, `backend_setup`), the raw
clock read (`Instant::now` — the monotonicity the timer proofs use is
established by a verified clamp, not trusted), `std::task::Waker`
cloning/waking, plus the ghost-log action family (each trusted to append
exactly one history event and touch nothing else). `Reactor::new` and
`Reactor::with_poll` are verified: only the OS handles are opaque.

### lion-reactor OS seam and io readiness (outside `verus!`)

`src/os/` and `src/async_fd.rs` are plain Rust that Verus never sees; the
verified reactor reaches them only through the
`register/deregister_io_source_action`, `poll_events_action`, `mio_setup` and
`backend_setup` rows above and, for `AsyncFd`, through `ReactorHandle`. They
hold no `unsafe`.

| file | item | what is trusted |
|---|---|---|
| src/os/mod.rs | `OsBackend`, `OsInterrupt`, `OsEvent` | the seam itself, object safe (`Box<dyn OsBackend>` in the reactor's `Poll`, `Arc<dyn OsInterrupt>` in `InterruptHandle`, so one dynamic call per park and per registration). Its doc comment is the contract a backend must meet: edge-triggered reports (every transition to ready reported again, none swallowed), mio's flag meanings, error and hang-up delivered whatever the interest, tokens returned verbatim (the reactor never registers token 0), `wait` timeouts (`None` blocks, zero polls; `EINTR` is an empty wait), and an interrupt callable from any thread that ends the current or next wait and is consumed inside `wait`, never reported as an event |
| src/os/mio_backend.rs | `MioBackend` (feature `mio`, default) | Lion's former direct mio code behind the trait: fds registered through `mio::unix::SourceFd` (the same epoll registration mio's socket types make: edge-triggered, `EPOLLRDHUP`), mio's eventfd `Waker` under token 0 as the interrupt, filtered out of the returned events (it used to reach the reactor as a harmless event for rid 0), and an interrupted wait (`EINTR`) returned as an empty one instead of an error |
| src/os/mock.rs | `MockBackend` / `MockOs` (feature `test-backend`, never in a default build) | an in-process backend for tests: the test injects readiness edges for fake fds, masked by the registered interest, merged per fd while pending, dropped on deregistration; the interrupt ends the current or next wait and is consumed by it |
| src/async_fd.rs | `AsyncFd` / `AsyncFdReadyGuard` | the one general implementation of the edge-triggered readiness protocol over the `IO_READINESS` flags (`src/readiness.rs`). Its module comment states the five invariants: only a park sets a flag; only an operation that returned `WouldBlock` clears one, in the same poll (`AsyncFdReadyGuard::try_io` is the only clearing site, so clearing on a success, the lost wakeup of HANG_FIXING_STORY.md story 1, cannot be expressed); a poll registers `cx.waker()` for the direction, re-reads the flag and only then returns `Pending`; the caller's waker is stored (no allocation per wait; combinators woken correctly), one waiter per direction; both flags start set. Registration is READABLE+WRITABLE once; the fd is never read, written, closed or put in non-blocking mode by `AsyncFd`, and must stay open until it drops. `!Send`. Every operation checks that the thread's current reactor is the one it registered with (see the next row) and fails otherwise; drop deregisters (which also removes the readiness entry) only under that reactor. lion-utility's TCP, UDP and listener glue still carry their own copies of the protocol, driven by the verified `IoKernel` and the reactor waker |
| src/reactor/enter.rs, src/readiness.rs | reactor identity, readiness lifetime | each reactor entered on a thread gets a fresh identity number (`current_reactor_epoch`), so an `AsyncFd` never acts on a successor reactor that reuses the address and, numbering its rids from 1 again, the rid. `ReactorGuard`'s drop now also clears the thread's readiness table (`readiness::clear_all`): its entries belong to the reactor leaving. `readiness::live_entries` counts entries for tests |
| src/types/interrupt_handle.rs | `InterruptHandleInner` | the coalescing wake: `wake` signals the backend only on the first wake since the owner's `reset`, and the executor resets before it drains its cross-thread queue and parks (unchanged; it now holds the backend's `OsInterrupt` instead of a `mio::Waker`) |

The reactor now depends on mio only through the `mio` feature (`default =
["mio"]`), which lion-executor, lion-utility and the `lion` facade forward
(each depends on the crate below with `default-features = false`). With
`--no-default-features`, lion-reactor and lion-executor build with no mio,
socket2 or tokio in their dependency graph, and `Runtime::new` fails with
`ErrorKind::Unsupported` until a backend is given
(`RuntimeBuilder::os_backend`). Regression tests: `lion-reactor/tests/os_backend.rs`
(the reactor alone over the mock: timer, readiness, error-only event,
interrupt) and `lion-executor/tests/os_backend.rs` (a runtime over the mock,
also run without mio); `AsyncFd` is pinned by `lion-utility/tests/async_fd.rs`
(echo over a socketpair and over the mock, the story-1 edge sequence with the
old pattern as a built-in control, concurrent reader and writer on one fd, an
error-only pipe event, drop and reactor-identity cleanup, the caller's waker).

**lion-executor (54).** Scheduling plumbing: claim-free raw takers for the TLS
wake queues and the mpsc injection channel (`try_recv_raw`,
`take_*_from_tls`), the single point where arbitrary user code runs
(`poll_future_raw`, a free function with no executor access), the
ghost-log action family, and a semantic `VecDeque` FIFO model the
local-queue liveness derivation rides on. TID freshness and drain
append/injected facts are verified in the wrapping layer (ledger + filters),
not trusted.

### lion-executor runtime glue (outside `verus!`)

The public runtime surface — `Runtime`, `ExecutorHandle`, the task wrapper,
`JoinHandle`, the wakers and the TLS queues — is plain Rust outside every
`verus!` block. Verus never sees it, so it is trusted as a whole, like
lion-utility's glue; it reaches verified code only through the executor's
`external_body` rows above. Its `unsafe` went from 15 sites at `7d872a9` (the
two raw-waker vtables' nine `unsafe fn`s and two `Waker::from_raw` blocks, and
`unsafe impl`s of `Send`/`Sync` for `ExecutorWaker`, `Send` for `JoinSender`
and `Sync` for `BlockingPool`) to 4: `unsafe impl Send for OwnerThreadOnly`
and three structural pin projections (two in `TaskCell`, one in
`OwnerThreadOnly`). Its trusted items:

| file | item | what is trusted |
|---|---|---|
| src/types/waker.rs | `ExecutorWaker` (`Arc` + std `Wake`) | on the owner thread a wake pushes the task id onto the TLS queue of its source (task, reactor or deferred); on any other thread it pushes onto the runtime's cross-thread queue and interrupts the park. `Send`/`Sync` are derived by the compiler: the former `unsafe impl Send/Sync` are gone |
| src/types/waker.rs | `create_reactor_waker_for_current` | the current task's `ExecutorWaker` with source Reactor. It replaced a `RawWakerVTable` waker that pushed onto the *calling* thread's TLS queue, which lost a wake from any other thread. Removed with it: the unused task vtable waker (`create_raw_task_waker`, `TASK_WAKER_VTABLE`) and the process-global `GLOBAL_CTX` that only that waker read |
| src/lib.rs, src/tls.rs; lion-reactor src/reactor/enter.rs | one runtime per thread (`runtime_is_live_on_this_thread`, `ThreadBinding`, `ReactorGuard`) | `Runtime::new` fails with `AlreadyExists`, before creating or installing anything, if the thread already has a runtime handle, cross-thread context or entered reactor, so a live runtime's thread-locals are never overwritten. On drop, the runtime clears each thread-local only if it is still its own (handle by runtime identity, context by `Arc` identity, reactor by address in `ReactorGuard`, which now records it), after its tasks are dropped, and then resets the thread's wake queues, notified set, current task, yield flag and cached clock, so a later runtime on the thread starts clean (task ids restart at 1 per runtime). The former drop cleared all three unconditionally. Nesting runtimes on one thread is not supported |
| src/lib.rs | `Runtime::tick` / `tick_with_timeout` | one call of the verified `Executor::tick`, the same step `block_on` loops over, after storing the idle park bound in the reactor wrapper (`block_on` and `tick` store 100 ms). Refuses (panics) when called from inside a task or a `block_on` future, so the verified tick is never re-entered |
| src/types/boxed_future.rs | `TaskCell` | the outermost future of every task. Per poll: register the task's waker once (for abort), return Ready without polling if the handle was aborted, else poll the user future under `catch_unwind`. On Ready, panic or abort it drops the future in place (containing a panicking destructor), then resolves the `JoinHandle` with the output, a panic `JoinError` carrying the payload, or a cancelled one (containing a panicking join waker). So its poll never unwinds and the verified core only sees Ready/Pending. Holds the one new `unsafe`: the structural pin projection of `future` (re-pinned by reference, dropped in place, never moved; no hand-written `Drop` or `Unpin`) |
| src/types/boxed_future.rs, src/handle.rs, src/lib.rs | `spawn_local` / `OwnerThreadOnly` | the one `unsafe impl Send` added: the storage wrapper of a task whose future need not be `Send`. The executor stores every task as a `Send` future only because its task type also crosses threads in the injection channel that foreign `spawn` feeds. Invariant: `InnerHandle::spawn_local` asserts it runs on the runtime's owner thread before building the task; the task is then received and polled only by the executor on that thread, and dropped there in every case (after Ready in `poll_task`; with the task slab or the injection channel when the `Runtime` drops, which it can only do on its owner thread because `Runtime` is now `!Send` via a `PhantomData<*const ()>`; std's channel drops queued messages when its receiver disconnects first, and the executor field holding it drops before the Runtime's own sender). A second `unsafe`, the newtype's pin projection, carries no invariant beyond "no Drop, field never moved" |
| src/types/join_handle.rs | `JoinHandle` / `JoinSender` / `JoinError` | the join channel (`Arc` of an atomic cancel flag and a `Mutex` of result, join waker and task waker; locks entered even if poisoned, no user code under a lock). `abort` sets the flag and wakes the task's registered waker; a `JoinSender` dropped unfinished resolves the handle as cancelled, so no await of a handle can hang on a task that is gone. `JoinError` is cancelled or panic (payload kept, tokio-shaped accessors). The former `unsafe impl Send for JoinSender` is gone: it is derived |
| src/blocking.rs | `spawn_blocking` pool | a closure runs under `catch_unwind` (a panic resolves its handle with the payload, the worker survives); a handle aborted before its closure starts cancels it. The round-robin cursor is an `AtomicUsize`: the former `Cell` inside an `unsafe impl Sync` pool was a data race between threads calling `spawn_blocking` |
| src/tls.rs | `CrossThreadQueue` | a std `Mutex<VecDeque<TaskId>>` (formerly a flume channel) that every thread may push to and only the owner drains, one batch per drain: no id pushed is lost or duplicated. lion-executor now depends on std alone outside the Verus crates (flume, futures-task and pin-project-lite are gone; the last two were never used) |

Regression tests pin this glue where the verifier cannot: `lion-utility/tests/`
`reactor_waker.rs`, `foreign_wake.rs`, `panic_abort.rs`, `spawn_local.rs`,
`runtime_nesting.rs` and `tick.rs`, plus `lion/tests/facade.rs` and a
`compile_fail` doctest that keeps `Runtime` `!Send`.

**lion-timer-wheel (7).** A trusted framing layer over `Vec` slot mutations —
each ensures pins the exact single-slot effect plus the exact `level_counts`
delta. The min-scan and emptiness checks on top are verified against these
leaves. The deadline/position maps are std `HashMap`s specified by vstd.

**lion-slab (0).** No trusted leaves: all public Slab API is verified directly
against vstd's std `HashMap` specification. Plus the two `#[verifier::external]`
items (`get_mut`, `values`) noted above.

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
