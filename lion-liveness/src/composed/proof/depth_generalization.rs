use vstd::prelude::*;
use crate::composed::spec::state::*;
use crate::composed::spec::types::*;
use crate::composed::spec::assumptions::*;
use crate::executor::spec::log as executor_log;
use crate::composed::proof::assumption_satisfiable::*;

verus! {

// ============================================================================
// Schedule-depth arrival coverage (generalization of the next-tick trigger).
//
// The original arrival trigger `task_delivered_next_tick` covers only the task
// at the HEAD of the committed injection schedule (delivered by the very next
// tick). Here the coverage is extended, with NO new assumptions, to a task at
// ARBITRARY depth k (`task_scheduled_at(s, tid, k)`): the delivery leg is
// DERIVED from two facts already in the model —
//   1. tick_has_pop_injection (executor_inv, on every complete tick cycle of
//      executor_progress): every composed step performs >= 1 PopInjection, so
//      t steps grow the total pop count by >= t (n_ticks_yield_n_pops);
//   2. pops_deliver_schedule (composed_progress, at every successor): once the
//      pop count reaches |schedule|, the ENTIRE schedule is delivered (the
//      threshold clause bounds None-pop starvation by |schedule| - 1 pops).
// So within |schedule| env_N-good steps tid is popped (task_spawned_in), and
// the existing spawn -> FIFO -> poll -> ... -> Ready machinery completes within
// the unchanged per-task budget. The original theorem and its statement are
// untouched; `end_to_end_liveness_from_depth` is a top-level VARIANT.
// ============================================================================

// Deep delivery: from a state where tid sits at undelivered depth k, EVERY
// env_N-good continuation of t >= |schedule| steps has popped tid.
#[verifier::rlimit(50)]
pub proof fn composed_depth_delivers(
  s: ComposedState, s_d: ComposedState, t: nat, cap: nat, tid: TaskId, k: nat,
)
  requires
    crate::composed::spec::contract::task_scheduled_at(s, tid, k),
    ete_reachable_N(s, s_d, t, cap, tid),
    t >= s.injection_schedule.len(),
    t >= 1,
  ensures
    crate::composed::spec::contract::task_spawned_in(s_d.executor_log, tid),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  let q = s.injection_schedule;
  // Whole-trace extension: schedule fixed, executor log prefix.
  ete_reachable_N_implies_env(s, s_d, t, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, s_d, t, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, s_d, t);
  assert(s_d.injection_schedule == q);
  assert(executor_log::is_prefix_of(s.executor_log, s_d.executor_log));
  // The LAST step is a composed_progress step, so pops_deliver_schedule holds
  // at s_d (composed_progress asserts it on the successor state).
  assert(t == (t - 1) as nat + 1);
  ete_reachable_N_split(s, s_d, (t - 1) as nat, 1, cap, tid);
  let s_pre: ComposedState = choose |s_pre: ComposedState|
    #[trigger] ete_reachable_N(s, s_pre, (t - 1) as nat, cap, tid) &&
    ete_reachable_N(s_pre, s_d, 1, cap, tid);
  ete_reachable_N_implies_env(s_pre, s_d, 1, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s_pre, s_d, 1, env, tid);
  assert(crate::composed::spec::progress::composed_progress(s_pre, s_d)) by {
    let tr: Seq<ComposedState> = choose |tr: Seq<ComposedState>|
      #![trigger tr.len()]
      tr.len() == 2 && tr.first() == s_pre && tr.last() == s_d &&
      crate::framework::module_spec::is_valid_trace(progress, tr);
    assert((progress)(tr[0], tr[1]));
    assert(tr[0] == s_pre && tr[1] == s_d);
  };
  assert(crate::executor::spec::injection_schedule::pops_deliver_schedule(
    s_d.executor_log, s_d.injection_schedule)) by {
    reveal(crate::composed::spec::progress::composed_progress);
  };
  // t composed steps = t executor tick cycles ⟹ >= t new pops ⟹ total >= |q|.
  crate::composed::proof::contract_bridges::composed_progress_n_implies_executor_progress_n(
    s, s_d, t);
  crate::executor::proof::bounded_injection_poll::n_ticks_yield_n_pops(
    s.executor_log, s_d.executor_log, t);
  crate::executor::proof::bounded_injection_poll::count_additivity_range(
    s_d.executor_log, 0, s.executor_log.len() as int, s_d.executor_log.len() as int);
  assert(executor_log::count_pop_injection_between(
    s_d.executor_log, 0, s_d.executor_log.len() as int) >= t);
  // Threshold clause fires: the whole schedule is delivered at s_d.
  let inj = crate::executor::spec::injection_schedule::injected_tasks(s_d.executor_log);
  assert(q.len() > 0);
  assert(inj.len() >= q.len());
  assert(crate::executor::spec::injection_schedule::is_task_prefix(inj, q));
  assert(inj.len() == q.len());
  assert(inj =~= q.subrange(0, inj.len() as int));
  // tid's undelivered slot j carries the schedule's content at s_d.
  let j = (crate::executor::spec::injection_schedule::injected_tasks(s.executor_log).len()
    + k) as int;
  assert(0 <= j < inj.len());
  assert(inj[j] == q[j]);
  assert(inj[j].id == tid);
  injected_is_spawned(s_d.executor_log, j);
}

// Depth-k analogue of composed_arrival_to_poll: an env_N-good trace of
// n >= |schedule| + (queue-drain budget) steps polls tid — |schedule| steps
// deliver tid into the runnable FIFO, the remaining steps drain it to a poll.
#[verifier::rlimit(50)]
pub proof fn composed_depth_arrival_to_poll(
  s: ComposedState, l_prime: ComposedState, n: nat, cap: nat, tid: TaskId, k: nat,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    crate::composed::spec::contract::task_scheduled_at(s, tid, k),
    ete_reachable_N(s, l_prime, n, cap, tid),
    n >= s.injection_schedule.len() + 1,
    (n - s.injection_schedule.len()) as nat > get_max_queue_length(s),
  ensures
    executor_log::has_poll_for_id(l_prime.executor_log, tid),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  let d: nat = s.injection_schedule.len();
  let m: nat = (n - d) as nat;
  assert(d >= 1);
  assert(n == d + m);
  ete_reachable_N_split(s, l_prime, d, m, cap, tid);
  let s_d: ComposedState = choose |s_d: ComposedState|
    #[trigger] ete_reachable_N(s, s_d, d, cap, tid) &&
    ete_reachable_N(s_d, l_prime, m, cap, tid);
  composed_depth_delivers(s, s_d, d, cap, tid, k);
  spawned_implies_in_fifo(s_d.executor_log, tid);
  let enter_idx: int = choose |ei: int| 0 < ei <= s_d.executor_log.len()
    && #[trigger] crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
      s_d.executor_log, ei, tid);
  ete_reachable_N_implies_env(s, s_d, d, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, s_d, d, env, tid);
  crate::composed::proof::end_to_end::progress_n_preserves_wf(s, s_d, d);
  crate::composed::proof::end_to_end::tid_survives_or_polled_in_range(
    s_d.executor_log, tid, enter_idx, s_d.executor_log.len() as int);
  if exists |pidx: int| enter_idx <= pidx < s_d.executor_log.len()
    && crate::executor::spec::log::is_poll_task_for_id_at(s_d.executor_log, pidx, tid) {
    // already polled in the delivery segment — persists to l' (prefix)
    let pidx: int = choose |pidx: int| enter_idx <= pidx < s_d.executor_log.len()
      && crate::executor::spec::log::is_poll_task_for_id_at(s_d.executor_log, pidx, tid);
    ete_reachable_N_implies_env(s_d, l_prime, m, cap, tid);
    crate::framework::module_spec::env_progress_n_implies_progress_n(
      progress, s_d, l_prime, m, env, tid);
    crate::composed::proof::end_to_end::progress_n_implies_extension(s_d, l_prime, m);
    assert(executor_log::is_prefix_of(s_d.executor_log, l_prime.executor_log));
    assert(s_d.executor_log[pidx] == l_prime.executor_log[pidx]);
  } else {
    // still in FIFO at s_d's end — the remaining m > C steps drain it
    assert(crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
      s_d.executor_log, s_d.executor_log.len() as int, tid));
    assert(0 < s_d.executor_log.len());
    assert(get_max_queue_length(s_d) == get_max_queue_length(s));
    queue_member_eventually_polled_on_trace(s_d, l_prime, m, cap, tid);
  }
}

// TOP-LEVEL VARIANT (the original end_to_end_liveness_env_N_trace is untouched):
// a task at ARBITRARY schedule depth k reaches Ready on every env_N(cap)-good
// continuation of budget n = |schedule| + chunk + cap·chunk — the delivery leg
// costs |schedule| ticks, then the unchanged per-task machinery completes.
#[verifier::rlimit(50)]
pub proof fn end_to_end_liveness_from_depth(s: ComposedState, tid: TaskId, k: nat, cap: nat)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    end_to_end_env(s, tid),
    crate::composed::spec::contract::task_scheduled_at(s, tid, k),
    cap >= 1,
  ensures
    ete_reaches_goal_for_cap(s, tid, cap),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  let chunk: nat = (get_max_timer_deadline_gap(s, tid) + get_io_ready_bound(s, tid)
    + get_max_queue_length(s) + cap + 2) as nat;
  let d: nat = s.injection_schedule.len();
  let n: nat = (d + chunk + cap * chunk) as nat;
  assert forall |l2: ComposedState| #[trigger] ete_reachable_N(s, l2, n, cap, tid)
    implies crate::composed::spec::contract::end_to_end_response(l2, tid) by {
    assert(n == (d + chunk) + cap * chunk);
    ete_reachable_N_split(s, l2, (d + chunk) as nat, (cap * chunk) as nat, cap, tid);
    let s1: ComposedState = choose |s1: ComposedState|
      #[trigger] ete_reachable_N(s, s1, (d + chunk) as nat, cap, tid) &&
      ete_reachable_N(s1, l2, (cap * chunk) as nat, cap, tid);
    composed_depth_arrival_to_poll(s, s1, (d + chunk) as nat, cap, tid, k);
    ete_reachable_N_implies_env(s, s1, (d + chunk) as nat, cap, tid);
    crate::framework::module_spec::env_progress_n_implies_progress_n(
      progress, s, s1, (d + chunk) as nat, env, tid);
    crate::composed::proof::end_to_end::progress_n_preserves_wf(s, s1, (d + chunk) as nat);
    assert(get_max_timer_deadline_gap(s1, tid) == get_max_timer_deadline_gap(s, tid));
    assert(get_io_ready_bound(s1, tid) == get_io_ready_bound(s, tid));
    assert(get_max_queue_length(s1) == get_max_queue_length(s));
    ete_reaches_goal_N_from_polled(s1, tid, cap, chunk);
  };
  assert(ete_reaches_goal_N(s, tid, cap, n));
}

// ∀-packaged statement mirroring end_to_end_liveness_env_N_trace, with the
// arrival trigger generalized from head-of-schedule to arbitrary depth k.
pub open spec fn end_to_end_liveness_from_depth_trace() -> bool {
  crate::framework::module_spec::progress_preserves_wf(
    crate::composed::spec::progress::composed_module_spec()) &&
  forall |s: ComposedState, tid: TaskId, k: nat, cap: nat|
    #![trigger crate::composed::spec::contract::task_scheduled_at(s, tid, k),
       ete_reaches_goal_for_cap(s, tid, cap)]
    crate::composed::spec::progress::composed_well_formed(s) &&
    end_to_end_env(s, tid) &&
    crate::composed::spec::contract::task_scheduled_at(s, tid, k) &&
    cap >= 1
    ==> ete_reaches_goal_for_cap(s, tid, cap)
}

#[verifier::rlimit(50)]
pub proof fn end_to_end_liveness_from_depth_trace_holds()
  ensures
    end_to_end_liveness_from_depth_trace(),
{
  crate::composed::proof::end_to_end::progress_preserves_wf_helper();
  assert forall |s: ComposedState, tid: TaskId, k: nat, cap: nat|
    crate::composed::spec::progress::composed_well_formed(s) &&
    end_to_end_env(s, tid) &&
    #[trigger] crate::composed::spec::contract::task_scheduled_at(s, tid, k) &&
    cap >= 1
    implies #[trigger] ete_reaches_goal_for_cap(s, tid, cap) by {
    end_to_end_liveness_from_depth(s, tid, k, cap);
  };
}

}
