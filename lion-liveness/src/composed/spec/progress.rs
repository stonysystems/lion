// ============================================================================
// Composing proof: assumption overview
//
// The end-to-end bounded liveness proof composes three verified modules
// (executor, reactor, per-task utilities) with assumptions about how they
// interact and how the external environment behaves. The assumptions fall
// into four categories:
//
// 1. MODULE INVARIANTS — verified, fully trusted
//
//    Each module's implementation has been formally verified against its
//    specification with zero remaining assumptions:
//    - The executor correctly schedules tasks: FIFO selection, tick structure,
//      draining of all wakeup queues, and polling when tasks are runnable.
//    - The reactor correctly manages timers and IO: registration uniqueness,
//      waker validity, timely wakeup on timer expiration or IO readiness.
//    - Each task correctly tracks its own resource lifecycle: ownership of
//      registered timers and IO resources, wakeup guarantee structure.
//
// 2. LOG CONSISTENCY — assumed, needs composed execution framework
//
//    When the executor, reactor, and tasks run together, their event logs
//    must be consistent with each other:
//    - Each task-level operation (register timer, set waker, etc.) corresponds
//      to exactly one reactor-level event, and vice versa.
//    - The ordering of operations within a task's log is consistent with the
//      ordering of corresponding events in the reactor's log.
//    - A task can only deregister a timer that it owns and that is still active
//      in the reactor — propagating Rust's ownership semantics across modules.
//    - These consistency properties are preserved across each execution step.
//
// 3. WAKEUP PIPELINE — assumed, needs composed execution framework
//
//    When a wakeup signal is produced by the reactor, it propagates through
//    the system and results in the target task being placed in the executor's
//    runnable queue:
//    - A timer wakeup (WakeTask) causes the owning task to be queued.
//    - An IO readiness event causes the waiting task to be queued.
//    - Tasks appearing in a drain batch have valid waker registrations.
//
// 4. ENVIRONMENT BEHAVIOR — external, cannot be derived from system internals
//
//    The proof assumes that the external environment cooperates within bounds.
//    Time is modeled as a bounded, strictly increasing integer. The executor's
//    runnable queue has bounded length. Each wakeup source that a task
//    registers will eventually fire:
//    - A registered IO resource becomes ready within a bounded number of
//      polling cycles.
//    - A waker passed to another task (via a synchronization utility) is
//      invoked within a bounded number of drain cycles.
//    - Each task returns Ready (completes) within a bounded number of polls.
//    In practice these are not always guaranteed — a task may await an IO
//    resource that never arrives, or loop indefinitely. But to prove bounded
//    liveness, we must assume these facts hold, and then rely on the verified
//    runtime logic (scheduling, resource management, wakeup propagation) to
//    ensure that task execution makes progress.
//
// ============================================================================
//
// Technical reference (definitions and locations):
//
// 1. Module invariants
//    - executor_inv (E1-E9): lion-executor tick()
//    - reactor_inv (R1-R15, L1-L3): lion-reactor park/register/waker
//    - utilities_inv (per-task): resource_ownership + wakeup_guarantee
//
// 2. Cross-module alignment (alignment.rs) — 3 categories × {state, step}
//    A. Action Mediation: task ops ⟷ reactor task-initiated events form
//       an order-preserving bijection (domain, surjective, injective,
//       order, ownership). 8 conjuncts at state, 4 at step.
//    B. Observation Consistency: executor's poll view of a task = task's
//       own log (polled-has-log, pending agreement at state; poll-driven
//       extension at step). 2 conjuncts at state, 4 at step.
//    C. Wakeup Routing: park sync between executor and reactor
//       (wakeup_routing_step). Queue delivery itself is not an alignment
//       clause: drain OCCURRENCE is derived from executor invariants and
//       drain MEMBERSHIP is modeled by the *_drain_step clauses of
//       composed_progress below.
//
// 3. Environment behavior (assumptions.rs + env_N in assumption_satisfiable.rs)
//    - timestamps_strictly_increasing, timestamps_positive
//    - timer_deadline_gap_bounded, timer_resources_remain_active
//    - queue_length_bounded, tid_unique
//    - injection schedule (pop_follows_schedule, arrival_bridges_hold)
//    - contract_io_assumption_here / io_ready_forward_here (env_N)
//    - bounded_poll_count_here_with_bound (env_N)
//    - taskwake_arrival_within (env_N)
//
// ============================================================================

use vstd::prelude::*;
use crate::composed::spec::state::*;
#[allow(unused_imports)]
use crate::composed::spec::types::*;
use crate::executor::spec::log as executor_log;
#[allow(unused_imports)]
use crate::executor::spec::events::*;
use crate::reactor::spec::log as reactor_log;
#[cfg(verus_keep_ghost)]
use crate::executor::invariants::executor_inv;
#[cfg(verus_keep_ghost)]
use crate::reactor::invariants::reactor_inv;
#[cfg(verus_keep_ghost)]
use crate::utilities::invariants::wakeup_guarantee::utilities_inv;
#[cfg(verus_keep_ghost)]
use crate::framework::module_spec::ModuleSpec;

verus! {

pub open spec fn is_complete_tick_cycle(l: executor_log::Log, start: int, end: int) -> bool {
  start >= 0 && end <= l.len() && start < end &&
  executor_log::is_tick_begin_at(l, start) &&
  executor_log::is_tick_end_at(l, end - 1) &&
  forall |i: int|
    start < i < end - 1 ==>
    !executor_log::is_tick_begin_at(l, i) &&
    !executor_log::is_tick_end_at(l, i)
}


pub open spec fn executor_progress(l: executor_log::Log, l_prime: executor_log::Log) -> bool {
  crate::executor::executor_progress(l, l_prime)
}

pub open spec fn reactor_progress(l: crate::reactor::spec::log::Log, l_prime: crate::reactor::spec::log::Log) -> bool {
  crate::reactor::reactor_progress(l, l_prime)
}

pub open spec fn task_logs_preserve_utilities_inv(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId|
    s_prime.task_logs.contains_key(tid) ==>
    utilities_inv(#[trigger] s_prime.task_logs[tid])
}

#[verifier::opaque]
pub open spec fn composed_progress(s: ComposedState, s_prime: ComposedState) -> bool {
  is_extension_of(s, s_prime) &&
  executor_progress(s.executor_log, s_prime.executor_log) &&
  reactor_progress(s.reactor_log, s_prime.reactor_log) &&
  crate::composed::spec::alignment::cross_module_alignment(s, s_prime) &&
  task_logs_preserve_utilities_inv(s, s_prime) &&
  crate::composed::spec::alignment::monotonic_task_reactor_alignment(s_prime) &&
  crate::executor::spec::injection_schedule::pops_deliver_schedule(
    s_prime.executor_log, s_prime.injection_schedule) &&
  // MODELED Deferred-wake routing (wake-routing Phase A): a deferred task
  // is taken by this step's Drain{Deferred} — replaces the free wake_delivers_here
  // defer disjunct. Vacuous when no task is in the deferred queue at s.
  crate::composed::spec::wake_queues::deferred_drain_step(s, s_prime) &&
  // MODELED ReactorWake routing (wake-routing Phase B): a task whose owned
  // timer/io WakeTask has fired (reactor_wake_pending) is taken by this step's
  // Drain{ReactorWake} — the derived-delivery replacement for the free
  // wake_delivers_here timer/io disjuncts. Vacuous when no fired reactor wake is
  // pending at s.
  crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s_prime) &&
  // MODELED TaskWake routing (wake-routing Phase C): a task whose waker was
  // invoked by another task/utility (taskwake_pending) is taken by this step's
  // Drain{TaskWake} — the derived-delivery replacement for the free wake_delivers_here
  // pass_waker disjunct. Vacuous when no Woken task is pending at s.
  crate::composed::spec::wake_queues::taskwake_drain_step(s, s_prime)
}

pub open spec fn composed_well_formed(s: ComposedState) -> bool {
  crate::executor::invariants::executor_inv(s.executor_log) &&
  crate::reactor::invariants::reactor_inv(s.reactor_log) &&
  // A. Action Mediation (task ops ⟷ reactor events bijection)
  crate::composed::spec::alignment::action_mediation_state(s) &&
  // B. Observation Consistency (executor view = task self log)
  crate::composed::spec::alignment::observation_consistency_state(s) &&
  // C. Wakeup Routing state form retired in Phase D (was content-free `true`)
  (forall |tid: TaskId|
    s.task_logs.contains_key(tid) ==>
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s.task_logs[tid]))
}

pub open spec fn composed_module_spec() -> ModuleSpec<ComposedState> {
  ModuleSpec {
    well_formed: |s: ComposedState| composed_well_formed(s),
    progress: |s: ComposedState, s_prime: ComposedState| composed_progress(s, s_prime),
  }
}

}
