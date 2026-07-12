use vstd::prelude::*;
use crate::composed::spec::state::*;
use crate::composed::spec::types::*;
use crate::reactor::spec::log as reactor_log;
use crate::reactor::spec::events::*;
use crate::executor::spec::log as executor_log;
#[cfg(verus_keep_ghost)]
use crate::executor::invariants::fifo_task_selection::fifo_queue_at;

verus! {

// CLOCK-GRANULARITY IDEALIZATION (disclosed in TCB_and_limitations.md §2): the
// model's clock is strictly monotone — every GetCurrentTime observes a FRESH
// timestamp. The implementation clock (get_current_time_action) is millisecond-
// granularity and only non-strictly clamped (result >= wheel.elapsed), so a run
// with two reads in the same millisecond falls outside this env clause and thus
// outside the theorem domain. Strictness is load-bearing: the timer bound
// derivation counts time reads as progress toward the deadline
// (timeout_existence.rs); weakening to non-decreasing would need a new
// time-advance-per-park assumption shape as the progress source.
// The definition lives in lion-reactor-spec (single source; re-exported here so
// the env core and the reactor-side proofs provably use the same spec fn).
pub use crate::reactor::timestamps_strictly_increasing;

pub open spec fn count_polls_for_tid(l: executor_log::Log, tid: TaskId) -> nat
  decreases l.len()
{
  if l.len() == 0 {
    0
  } else if executor_log::is_poll_task_for_id_at(l, (l.len() - 1) as int, tid) {
    1 + count_polls_for_tid(l.subrange(0, l.len() - 1), tid)
  } else {
    count_polls_for_tid(l.subrange(0, l.len() - 1), tid)
  }
}

pub open spec fn task_polled_to_ready(l: executor_log::Log, tid: TaskId) -> bool {
  exists |i: int|
    #![trigger l[i]]
    0 <= i < l.len() &&
    executor_log::is_poll_ready_for_id_at(l, i, tid)
}

pub open spec fn is_task_pending_at(s: ComposedState, tid: TaskId, i: int) -> bool {
  0 <= i < s.executor_log.len() &&
  executor_log::is_poll_pending_for_id_at(s.executor_log, i, tid)
}

#[verifier::opaque]
pub open spec fn timer_deadline_gap_bounded(s: ComposedState, tid: TaskId) -> bool {
  forall |reg_idx: int|
    #![trigger s.reactor_log[reg_idx]]
    0 <= reg_idx < s.reactor_log.len() &&
    reactor_log::is_succ_register_timer_at(s.reactor_log, reg_idx) &&
    crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(
      s.reactor_log, reg_idx, s.reactor_log.len() as int
    )
    ==>
    crate::reactor::proof::round_extension::compute_bound(
      get_register_timer_deadline(s.reactor_log[reg_idx]),
      reactor_log::max_timestamp_up_to(s.reactor_log, (reg_idx + 1) as int)
    ) <= get_max_timer_deadline_gap(s, tid)
}

pub open spec fn get_max_timer_deadline_gap(s: ComposedState, tid: TaskId) -> nat {
  arbitrary()
}

pub open spec fn get_io_ready_bound(s: ComposedState, tid: TaskId) -> nat {
  arbitrary()
}

pub open spec fn get_max_queue_length(s: ComposedState) -> nat {
  arbitrary()
}

// WHY THIS IS AN ASSUMPTION (not derived): the runnable FIFO's length is
// system-maintained, but its growth is driven by arrivals — spawns and wakes —
// which are external inputs the model does not count (total task count is
// unmodeled). Queue length <= tasks ever delivered + wakes ever fired, so
// bounding it is a bounded-workload assumption, the same family as the
// injection schedule. Deriving it would require modeling the workload's task
// population, not more system invariants.
pub open spec fn queue_length_bounded(s: ComposedState) -> bool {
  forall |i: int|
    #![trigger fifo_queue_at(s.executor_log, i)]
    0 <= i <= s.executor_log.len() ==>
    fifo_queue_at(s.executor_log, i).len() <= get_max_queue_length(s)
}

// A4' (Resource Hold): every registered timer/IO resource remains active
// (not deregistered) for the lifetime of the log extension. This is the
// "future does not drop its registration while waiting" property,
// implicit in async runtime semantics (Drop = deregister, and a Pending
// future is not dropped until poll → Ready).

// t4b (reuse-tolerant A4'): a reactor register-timer index is "current-poll-owned"
// if SOME task's CURRENT poll registered a timer matched (action-mediation) by that
// reactor event. Opaque to bound SMT (the ∃ over (tid,t) is revealed only where a
// concrete owner is supplied).
#[verifier::opaque]
pub open spec fn timer_reg_current_poll_owned(s: ComposedState, reg_idx: int) -> bool {
  exists |tid: TaskId, t: int|
    #![trigger s.task_logs[tid][t]]
    s.task_logs.contains_key(tid) &&
    0 <= t < s.task_logs[tid].len() &&
    crate::utilities::spec::events::is_register_timer(s.task_logs[tid][t]) &&
    crate::utilities::spec::log::in_current_poll_cycle(
      s.task_logs[tid], t, (s.task_logs[tid].len() - 1) as int) &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[reg_idx], s.task_logs[tid][t])
}

// t4b: WEAKENED to current-owner. A Pending future does not drop the timer it is
// CURRENTLY waiting on — but a stale registration from an earlier poll (later
// deregistered and its rid reused) is UNconstrained, so rid-reuse traces are now in
// the domain. Only current-poll-owned registrations must remain active. (Was: EVERY
// registration must remain active, which excluded all reuse.)
pub open spec fn timer_resources_remain_active(s: ComposedState) -> bool {
  forall |reg_idx: int|
    #![trigger s.reactor_log[reg_idx]]
    0 <= reg_idx < s.reactor_log.len() &&
    reactor_log::is_succ_register_timer_at(s.reactor_log, reg_idx) &&
    timer_reg_current_poll_owned(s, reg_idx) ==>
    crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(
      s.reactor_log, reg_idx, s.reactor_log.len() as int
    )
}

// t5c: io currency guard (io analog of t4b's timer_reg_current_poll_owned).
// The io resource-hold obligation applies only to a rid some task is CURRENTLY
// awaiting: rid is io-active in tid's log, tid set its waker for rid in the
// current poll cycle, and tid's last poll is Pending. After tid is polled
// (Ready or a new cycle), the guard turns off and cleanup deregistration is
// unconstrained — post-completion drop traces stay in the theorem domain.
// Opaque to bound SMT (the ∃ over tid is revealed only where a concrete
// waiter is supplied).
#[verifier::opaque]
pub open spec fn io_rid_current_poll_awaited(
  s: ComposedState, rid: crate::reactor::spec::types::ResourceIdView,
) -> bool {
  exists |tid: TaskId|
    #![trigger s.task_logs.contains_key(tid)]
    s.task_logs.contains_key(tid) && {
      let last = (s.task_logs[tid].len() - 1) as int;
      crate::utilities::spec::log::is_io_active(s.task_logs[tid], rid, last) &&
      crate::utilities::spec::log::has_waker_set_in_current_poll(s.task_logs[tid], rid, last) &&
      executor_log::last_poll_is_pending(s.executor_log, tid)
    }
}

// L2 (io-symmetry): io_reg_current_poll_owned + io_resources_remain_active REMOVED
// as inert. The io forward-derivation (composed_io_pending_to_poll) establishes the
// io resource-hold from the TASK-LOG side (is_io_active + pending_poll_inv), never
// from this reactor-side assumption; io_reg_current_poll_owned was opaque and never
// revealed, so this assumption's consequent could never be extracted. Dropping it
// shrinks the trusted env surface (see TODO_io_symmetry.md, Phase L2).

// (The old `pass_waker_contract_holds` asserted, as an env clause,
// `bounded_liveness_without_arrival(utility_module_spec(), …)` — a statement
// that is semantically FALSE (the utility progress relation forced no invariant
// and no Woken event, so both its progress_preserves_wf conjunct and its
// forall-extension response conjunct had trivial counterexamples). As an env
// conjunct it therefore entailed ¬task_logs.contains_key(tid) at every trace
// state, i.e. env-good traces never polled the task at all. Removed: cross-task
// wake delivery is assumed once, per-state and satisfiably, in
// `wake_delivers_here` (env_N), matching the paper's compositional design where
// the unmodeled utility kernel's delivery is an environment assumption.)

// (audit: injection_arrival_sched / arrival_bridges_hold removed from
// end_to_end_env — discharged by every witness but consumed by no derivation
// lemma; the theorem's delivery legs use the antecedent end_to_end_arrival and
// composed_progress's pops_deliver_schedule instead. Removal strictly enlarges
// the theorem domain.)

}
