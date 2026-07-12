use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::composed::spec::state::*;
#[cfg(verus_keep_ghost)]
use crate::composed::spec::types::*;
#[cfg(verus_keep_ghost)]
use crate::composed::spec::progress::*;
#[cfg(verus_keep_ghost)]
use crate::framework::module_spec::{progress_n, is_valid_trace};

verus! {

pub proof fn composed_progress_implies_executor_progress(
  s: ComposedState,
  s_prime: ComposedState,
)
  requires
    composed_progress(s, s_prime),
  ensures
    crate::executor::executor_progress(s.executor_log, s_prime.executor_log),
{
  reveal(composed_progress);
}

// k-step composed_progress projects to k-step executor_progress.
pub proof fn composed_progress_n_implies_executor_progress_n(
  s: ComposedState,
  s_prime: ComposedState,
  k: nat,
)
  requires
    progress_n(composed_module_spec().progress, s, s_prime, k),
  ensures
    progress_n(
      crate::executor::executor_module_spec().progress,
      s.executor_log,
      s_prime.executor_log,
      k,
    ),
  decreases k
{
  let trace: Seq<ComposedState> = choose |trace: Seq<ComposedState>|
    #![trigger trace.len()]
    trace.len() == k + 1 &&
    trace.first() == s &&
    trace.last() == s_prime &&
    is_valid_trace(composed_module_spec().progress, trace);

  // Project trace to executor_log component.
  let exec_trace: Seq<crate::executor::spec::log::Log> =
    Seq::new(trace.len(), |i: int| trace[i].executor_log);
  assert(exec_trace.len() == k + 1);
  assert(exec_trace.first() == s.executor_log) by {
    assert(exec_trace[0] == trace[0].executor_log);
  };
  assert(exec_trace.last() == s_prime.executor_log) by {
    assert(exec_trace[exec_trace.len() - 1] == trace[trace.len() - 1].executor_log);
  };
  assert(is_valid_trace(
    crate::executor::executor_module_spec().progress, exec_trace
  )) by {
    assert forall |i: int| 0 <= i < exec_trace.len() - 1 implies
      (crate::executor::executor_module_spec().progress)(
        #[trigger] exec_trace[i], exec_trace[i + 1]
      )
    by {
      assert(exec_trace[i] == trace[i].executor_log);
      assert(exec_trace[i + 1] == trace[i + 1].executor_log);
      assert((composed_module_spec().progress)(trace[i], trace[i + 1]));
      composed_progress_implies_executor_progress(trace[i], trace[i + 1]);
    };
  };
}

pub proof fn composed_wf_implies_reactor_wf(s: ComposedState)
  requires composed_well_formed(s),
  ensures crate::reactor::invariants::reactor_inv(s.reactor_log),
{
  // Direct from definition.
}


pub proof fn composed_active_io_implies_reactor_trigger(
  s: ComposedState,
  rid: crate::reactor::spec::types::ResourceIdView,
  tid: TaskId,
)
  requires
    composed_well_formed(s),
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int
    ),
    // Strengthened: caller must specify the rid that BOTH is active AND has
    // a waker set. (Old form left ambiguous which rid; tightening here.)
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int
    ),
  ensures
    (crate::reactor::contracts::bounded_io_wakeup::bounded_io_wakeup().acceptance)(
      s.reactor_log, rid
    ),
{
  // From task-side SetWaker(rid) in current poll cycle, action_mediation_state
  // gives a matching reactor SuccSetWaker for the same rid.
  let task_log = s.task_logs[tid];
  let last_idx = (task_log.len() - 1) as int;
  let j_sw: int = choose |j: int|
    crate::utilities::spec::log::in_current_poll_cycle(task_log, j, last_idx) &&
    crate::utilities::spec::events::is_succ_set_waker(task_log[j]) &&
    crate::utilities::spec::events::get_resource_id(task_log[j]) == Some(rid);
  assert(0 <= j_sw < task_log.len());
  assert(crate::composed::spec::alignment::is_reactor_operation(task_log[j_sw]));
  let k_sw: int = choose |k: int|
    0 <= k < s.reactor_log.len() &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[k], task_log[j_sw]);
  assert(crate::reactor::spec::log::is_succ_set_waker_at(s.reactor_log, k_sw));
  assert(crate::reactor::spec::events::get_set_waker_rid(s.reactor_log[k_sw]) == rid);

  // Similarly, is_io_active(task_log, rid, last_idx) implies a RegisterIo(rid)
  // in task_log; action_mediation gives a matching SuccRegisterIo in reactor_log.
  let j_reg: int = choose |j: int|
    0 <= j < task_log.len() &&
    crate::utilities::spec::events::is_register_io(task_log[j]) &&
    crate::utilities::spec::events::get_resource_id(task_log[j]) == Some(rid);
  assert(crate::composed::spec::alignment::is_reactor_operation(task_log[j_reg]));
  let k_reg: int = choose |k: int|
    0 <= k < s.reactor_log.len() &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[k], task_log[j_reg]);
  assert(crate::reactor::spec::log::io_syscall_registered_at(s.reactor_log, k_reg));
  assert(crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[k_reg]) == rid);

  // find_last_set_waker_for_rid >= k_sw >= 0; result is SuccSetWaker(rid).
  crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_exists_if_some(
    s.reactor_log, rid, s.reactor_log.len() as int, k_sw
  );
  let sw_idx = crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
    s.reactor_log, rid, s.reactor_log.len() as int
  );
  assert(sw_idx >= 0);
  assert(crate::reactor::spec::log::is_succ_set_waker_at(s.reactor_log, sw_idx));
  assert(crate::reactor::spec::events::get_set_waker_rid(s.reactor_log[sw_idx]) == rid);

  // reactor_inv (via composed_well_formed) includes set_waker_active_io
  // action-safety: every SuccSetWaker has io_syscall_active_at_set_waker.
  composed_wf_implies_reactor_wf(s);
  assert(crate::reactor::invariants::reactor_inv(s.reactor_log));
  let sw_invariant = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert((sw_invariant.acceptance)(s.reactor_log, sw_idx));
  assert((sw_invariant.validity)(s.reactor_log, sw_idx));
  // (sw_invariant.validity)(l, sw_idx) = io_syscall_active_at_set_waker(l, get_set_waker_rid(l[sw_idx]), sw_idx)
  //                                    = io_syscall_active_at_set_waker(l, rid, sw_idx)
}

}
