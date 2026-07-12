use vstd::prelude::*;
#[allow(unused_imports)]
use crate::composed::spec::state::*;
#[allow(unused_imports)]
use crate::composed::spec::types::*;
use crate::executor::spec::log as executor_log;
#[allow(unused_imports)]
use crate::executor::spec::events as executor_events;
use crate::reactor::spec::log as reactor_log;

verus! {

// t4b i-keyed delivery trigger (moved here from assumption_satisfiable.rs in Phase B
// to break the spec→proof module cycle): the task registered a timer in its CURRENT
// poll and the reactor fired THAT registration's OWN waker — response_at at a
// CURRENT-poll-owned reactor index i. Reuse-faithful: a stale registration's old fire
// (a different waker) does NOT satisfy it (i must be current-poll-owned and carry rid's
// current registration). rid is derived from i (get_register_timer_rid(reactor[i])), so
// the ∃ is single-variable in i.
pub open spec fn timer_wake_owned(s: ComposedState, tid: TaskId) -> bool {
  s.task_logs.contains_key(tid) && {
    let last = (s.task_logs[tid].len() - 1) as int;
    exists |i: int|
      #![trigger crate::reactor::contracts::bounded_timer_wakeup::response_at(s.reactor_log, i)]
      0 <= i < s.reactor_log.len() &&
      reactor_log::is_succ_register_timer_at(s.reactor_log, i) &&
      crate::composed::spec::assumptions::timer_reg_current_poll_owned(s, i) &&
      crate::utilities::spec::log::has_timer_registered_in_current_poll(
        s.task_logs[tid],
        crate::reactor::spec::events::get_register_timer_rid(s.reactor_log[i]), last) &&
      crate::reactor::contracts::bounded_timer_wakeup::response_at(s.reactor_log, i)
  }
}

// ============================================================================
// Wake-queue DERIVED quantities (wake-routing, Phase A: Deferred)
//
// Each wake queue is modeled as a DERIVED spec function of the logs — pinned to
// the actual wake/drain events, NOT a free ComposedState field or a free env
// assumption. This is the dual of the injection queue's `injection_schedule` +
// `pop_follows_schedule`, but for INTERNAL causes the queue content must be tied
// to the events (here: the task's own `Defer` op and the `Drain{Deferred}`
// events), so it is derived rather than a free schedule.
// ============================================================================

// A Drain{Deferred} event containing tid occurs strictly after `start`.
pub open spec fn deferred_drained_after(l: executor_log::Log, tid: TaskId, start: int) -> bool {
  exists |d: int|
    #![trigger l[d]]
    start < d < l.len() &&
    executor_log::is_drain_deferred_at(l, d) &&
    executor_log::task_id_in_drain_at(l, d, tid)
}

// tid currently sits in the (derived) Deferred queue: its most recent poll ended
// Pending with a `Defer` in that poll, and no `Drain{Deferred}` has taken it
// since. Determined ENTIRELY by the logs (task self-defer + executor drains) —
// no free field, no owner resolution (Deferred is a self-wake).
pub open spec fn in_deferred_queue(s: ComposedState, tid: TaskId) -> bool {
  s.task_logs.contains_key(tid) &&
  executor_log::last_poll_is_pending(s.executor_log, tid) &&
  crate::utilities::spec::log::has_defer_in_current_poll(
    s.task_logs[tid], (s.task_logs[tid].len() - 1) as int) &&
  !deferred_drained_after(
    s.executor_log, tid, executor_log::last_poll_idx_for_id(s.executor_log, tid))
}

// STEP constraint (goes in composed_progress): the MODELED routing for the
// Deferred queue, replacing the free `wake_delivers_here` defer disjunct. A task
// in the deferred queue at `s` is TAKEN by any Drain{Deferred} appended in the
// step s → s_prime (one-shot: the deferred queue is drained entirely each tick).
// Combined with tick_has_drain_deferred (a Drain{Deferred} occurs each tick) and
// in_deferred_queue persistence (a not-yet-re-polled deferred task stays queued),
// this DERIVES delivery: deferred task → next tick's drain → runnable FIFO → poll.
// Pinned to the actual Defer event (via in_deferred_queue), not a free assumption.
// Vacuous for traces with no deferred tasks (antecedent false).
pub open spec fn deferred_drain_step(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId, d: int|
    #![trigger s_prime.executor_log[d], in_deferred_queue(s, tid)]
    in_deferred_queue(s, tid) &&
    s.executor_log.len() as int <= d < s_prime.executor_log.len() &&
    executor_log::is_drain_deferred_at(s_prime.executor_log, d)
    ==>
    executor_log::task_id_in_drain_at(s_prime.executor_log, d, tid)
}

// ============================================================================
// ReactorWake queue DERIVED quantities (wake-routing, Phase B).
//
// The reactor-wake queue is the SET of tasks whose OWN resource (timer/io)
// registration had its `WakeTask` fire in the reactor, not yet taken by a
// `Drain{ReactorWake}`. Its ARRIVAL is INTERNAL (the task registered the
// resource in its own poll and the reactor contract fired THAT registration's
// waker), so — unlike injection's free schedule — the queue content is pinned to
// the actual reactor WakeTask event via the owner-resolving arrival predicate
// (currently the timer disjunct `timer_wake_owned`, which ties response_at(i) to
// tid through current-poll ownership of reg i; the io disjunct is added when the
// io path is migrated). Delivery is then DERIVED (reactor_wake_drain_step), not
// assumed via wake_delivers_here.
// ============================================================================

// io analog of timer_wake_owned (moved here from assumption_satisfiable.rs, io
// increment): tid's io resource rid is active with a waker set in the current poll,
// and the reactor fired a WakeTask for rid AFTER the last SetWaker (re-arm safe —
// find_last_set_waker anchors the CURRENT waiter, so a stale registration's old fire
// does not satisfy it). Pinned to the reactor WakeTask event.
pub open spec fn io_wake_in_current_window(l: reactor_log::Log, rid: crate::reactor::spec::types::ResourceIdView) -> bool {
  let sw = crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(l, rid, l.len() as int);
  sw >= 0 &&
  exists |w: int|
    #![trigger l[w]]
    sw < w < l.len() &&
    reactor_log::is_wake_task_at(l, w) &&
    crate::reactor::spec::events::get_wake_task_source_rid(l[w]) == rid
}

// The reactor-wake ARRIVAL for tid: a WakeTask owned by tid has fired in tid's
// current registration window — timer disjunct (timer_wake_owned: response_at at a
// current-poll-owned reg i) OR io disjunct (an active io-wait whose rid has a WakeTask
// after its last SetWaker). Both are pinned to the reactor WakeTask event.
// Opaque (wake-routing Phase B: closed/opaque to bound SMT — io_trace_facts_at
// is at the rlimit ceiling and open spec additions perturb it).
#[verifier::opaque]
pub open spec fn reactor_wake_arrival(s: ComposedState, tid: TaskId) -> bool {
  s.task_logs.contains_key(tid) && {
    let last = (s.task_logs[tid].len() - 1) as int;
    ||| timer_wake_owned(s, tid)
    ||| (exists |rid: crate::reactor::spec::types::ResourceIdView|
          #![trigger crate::utilities::spec::log::has_waker_set_in_current_poll(s.task_logs[tid], rid, last)]
          crate::utilities::spec::log::is_io_active(s.task_logs[tid], rid, last) &&
          crate::utilities::spec::log::has_waker_set_in_current_poll(s.task_logs[tid], rid, last) &&
          io_wake_in_current_window(s.reactor_log, rid))
  }
}

// A Drain{ReactorWake} event containing tid occurs strictly after `start`.
pub open spec fn reactor_wake_drained_after(l: executor_log::Log, tid: TaskId, start: int) -> bool {
  exists |d: int|
    #![trigger l[d]]
    start < d < l.len() &&
    executor_log::is_drain_reactor_wake_at(l, d) &&
    executor_log::task_id_in_drain_at(l, d, tid)
}

// tid currently sits in the (derived) ReactorWake queue: its most recent poll
// ended Pending, an owned WakeTask fired (reactor_wake_arrival), and no
// Drain{ReactorWake} has taken it since. Determined ENTIRELY by the logs (reactor
// WakeTask + owner resolution + executor drains) — no free field, no free env
// delivery assumption.
#[verifier::opaque]
pub open spec fn reactor_wake_pending(s: ComposedState, tid: TaskId) -> bool {
  s.task_logs.contains_key(tid) &&
  executor_log::last_poll_is_pending(s.executor_log, tid) &&
  reactor_wake_arrival(s, tid) &&
  !reactor_wake_drained_after(
    s.executor_log, tid, executor_log::last_poll_idx_for_id(s.executor_log, tid))
}

// STEP constraint (goes in composed_progress): the MODELED routing for the
// ReactorWake queue, replacing the free wake_delivers_here timer/io disjuncts. A
// task in the reactor-wake queue at `s` is TAKEN by any Drain{ReactorWake}
// appended in the step s → s_prime. Combined with single_progress_has_drain_
// reactor_wake (a Drain{ReactorWake} occurs each tick) and reactor_wake_pending
// persistence, this DERIVES delivery: fired wake → next tick's drain → runnable
// FIFO → poll. Pinned to the actual WakeTask event (via reactor_wake_arrival),
// not a free assumption. Vacuous for traces with no fired reactor wakes.
#[verifier::opaque]
pub open spec fn reactor_wake_drain_step(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId, d: int|
    #![trigger s_prime.executor_log[d], reactor_wake_pending(s, tid)]
    reactor_wake_pending(s, tid) &&
    s.executor_log.len() as int <= d < s_prime.executor_log.len() &&
    executor_log::is_drain_reactor_wake_at(s_prime.executor_log, d)
    ==>
    executor_log::task_id_in_drain_at(s_prime.executor_log, d, tid)
}

// ============================================================================
// TaskWake queue DERIVED quantities (wake-routing, Phase C).
//
// The task-wake queue is the SET of tasks whose waker was invoked by another
// task/utility — a `Woken` event in the task's OWN utility log (self-identifying,
// no owner resolution). Unlike timer/io, the ARRIVAL is EXTERNAL (another entity),
// so "will the Woken fire" is legitimately an ASSUMPTION (like injection's spawn);
// the ROUTING (Woken → drain → FIFO → poll) is DERIVED here the same way as the
// other queues. This models the routing; the real utility-wake arrival assumption
// (replacing pass_waker.assumption_fn ≡ true) is a separate step.
// ============================================================================

// The task-wake ARRIVAL for tid: tid's waker was invoked (a Woken event) in its
// current poll. Self-identifying (in tid's own task log). Pinned to the Woken event.
#[verifier::opaque]
pub open spec fn taskwake_arrival(s: ComposedState, tid: TaskId) -> bool {
  s.task_logs.contains_key(tid) &&
  crate::utilities::spec::log::has_woken_in_current_poll(
    s.task_logs[tid], (s.task_logs[tid].len() - 1) as int)
}

// A Drain{TaskWake} event containing tid occurs strictly after `start`.
pub open spec fn taskwake_drained_after(l: executor_log::Log, tid: TaskId, start: int) -> bool {
  exists |d: int|
    #![trigger l[d]]
    start < d < l.len() &&
    executor_log::is_drain_task_wake_at(l, d) &&
    executor_log::task_id_in_drain_at(l, d, tid)
}

// d-bounded variant: a Drain{TaskWake} containing tid occurs strictly within
// (start, end). Used as the "not yet delivered" guard of the drain-membership
// arrival clause taskwake_arrival_within: only drains BEFORE the considered one
// exempt it (open interval excluding `end`), so the FIRST post-window drain is
// still obliged to carry tid, and every later drain is exempted by the first.
pub open spec fn taskwake_drained_in(l: executor_log::Log, tid: TaskId, start: int, end: int) -> bool {
  exists |d: int|
    #![trigger l[d]]
    start < d < end &&
    executor_log::is_drain_task_wake_at(l, d) &&
    executor_log::task_id_in_drain_at(l, d, tid)
}

// tid currently sits in the (derived) TaskWake queue: its most recent poll ended
// Pending, its waker was invoked (taskwake_arrival), and no Drain{TaskWake} has taken
// it since. Determined ENTIRELY by the logs (Woken op + executor drains).
#[verifier::opaque]
pub open spec fn taskwake_pending(s: ComposedState, tid: TaskId) -> bool {
  s.task_logs.contains_key(tid) &&
  executor_log::last_poll_is_pending(s.executor_log, tid) &&
  taskwake_arrival(s, tid) &&
  !taskwake_drained_after(
    s.executor_log, tid, executor_log::last_poll_idx_for_id(s.executor_log, tid))
}

// STEP constraint (goes in composed_progress): the MODELED routing for the TaskWake
// queue, replacing the free wake_delivers_here pass_waker disjunct. A task whose waker
// was invoked (taskwake_pending) is TAKEN by any Drain{TaskWake} appended in the step.
// Combined with single_progress_has_drain_task_wake + taskwake_pending persistence, this
// DERIVES delivery. Vacuous for traces with no Woken task.
#[verifier::opaque]
pub open spec fn taskwake_drain_step(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId, d: int|
    #![trigger s_prime.executor_log[d], taskwake_pending(s, tid)]
    taskwake_pending(s, tid) &&
    s.executor_log.len() as int <= d < s_prime.executor_log.len() &&
    executor_log::is_drain_task_wake_at(s_prime.executor_log, d)
    ==>
    executor_log::task_id_in_drain_at(s_prime.executor_log, d, tid)
}

}
