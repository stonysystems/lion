use vstd::prelude::*;
#[allow(unused_imports)]
use crate::composed::spec::state::*;
#[allow(unused_imports)]
use crate::composed::spec::types::*;
#[allow(unused_imports)]
use crate::composed::spec::alignment::*;
#[allow(unused_imports)]
use crate::utilities::spec::events as pe;
#[allow(unused_imports)]
use crate::reactor::spec::events as re;
#[allow(unused_imports)]
use crate::reactor::spec::log as reactor_log;
#[allow(unused_imports)]
use crate::utilities::spec::log as task_log;

verus! {

#[verifier::rlimit(50)]
pub proof fn derive_succ_deregister_by_owner(s: ComposedState)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    operation_alignment_inv(s),
    monotonic_task_reactor_alignment(s),
    deregister_matches_own_registration(s),
    forall |tid: TaskId|
      s.task_logs.contains_key(tid) ==>
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(
        #[trigger] s.task_logs[tid]),
  ensures
    succ_deregister_by_owner(s),
{
  reveal(succ_deregister_by_owner);
  assert forall |reactor_reg_idx: int, reactor_dereg_idx: int,
                 tid_reg: TaskId, task_reg_idx: int,
                 tid_dereg: TaskId, task_dereg_idx: int|
    0 <= reactor_reg_idx < reactor_dereg_idx &&
    reactor_dereg_idx < s.reactor_log.len() &&
    re::is_succ_register_timer(s.reactor_log[reactor_reg_idx]) &&
    re::is_succ_deregister_timer(s.reactor_log[reactor_dereg_idx]) &&
    re::get_register_timer_rid(s.reactor_log[reactor_reg_idx]) ==
      re::get_deregister_timer_rid(s.reactor_log[reactor_dereg_idx]) &&
    reactor_log::timer_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx) &&
    s.task_logs.contains_key(tid_reg) &&
    0 <= task_reg_idx < s.task_logs[tid_reg].len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid_reg][task_reg_idx]) &&
    s.task_logs.contains_key(tid_dereg) &&
    0 <= task_dereg_idx < s.task_logs[tid_dereg].len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid_dereg][task_dereg_idx])
    implies tid_reg == tid_dereg
  by {
    derive_step(
      s, reactor_reg_idx, reactor_dereg_idx,
      tid_reg, task_reg_idx, tid_dereg, task_dereg_idx);
  };
}

#[verifier::rlimit(50)]
proof fn derive_step(
  s: ComposedState,
  reactor_reg_idx: int, reactor_dereg_idx: int,
  tid_reg: TaskId, task_reg_idx: int,
  tid_dereg: TaskId, task_dereg_idx: int,
)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    operation_alignment_inv(s),
    monotonic_task_reactor_alignment(s),
    deregister_matches_own_registration(s),
    forall |tid: TaskId|
      s.task_logs.contains_key(tid) ==>
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(
        #[trigger] s.task_logs[tid]),
    0 <= reactor_reg_idx < reactor_dereg_idx,
    reactor_dereg_idx < s.reactor_log.len(),
    re::is_succ_register_timer(s.reactor_log[reactor_reg_idx]),
    re::is_succ_deregister_timer(s.reactor_log[reactor_dereg_idx]),
    re::get_register_timer_rid(s.reactor_log[reactor_reg_idx]) ==
      re::get_deregister_timer_rid(s.reactor_log[reactor_dereg_idx]),
    reactor_log::timer_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx),
    s.task_logs.contains_key(tid_reg),
    0 <= task_reg_idx < s.task_logs[tid_reg].len(),
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid_reg][task_reg_idx]),
    s.task_logs.contains_key(tid_dereg),
    0 <= task_dereg_idx < s.task_logs[tid_dereg].len(),
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid_dereg][task_dereg_idx]),
  ensures tid_reg == tid_dereg,
{
  let l = s.reactor_log;
  let tl = s.task_logs[tid_dereg];
  let rid = re::get_register_timer_rid(l[reactor_reg_idx]);

  re::succ_deregister_timer_is_deregister_timer(l[reactor_dereg_idx]);
  assert(pe::is_deregister_timer(tl[task_dereg_idx]));
  assert(pe::get_resource_id(tl[task_dereg_idx]) == Some(rid));

  // Step 1: resource_ownership gives is_timer_active at task_dereg_idx
  let ro = crate::utilities::invariants::resource_ownership::resource_ownership();
  assert(crate::framework::action_safety::action_safety_satisfied(ro, tl));
  assert(crate::utilities::invariants::resource_ownership::is_resource_operation(tl[task_dereg_idx]));
  assert((ro.acceptance)(tl, task_dereg_idx as int));
  assert((ro.validity)(tl, task_dereg_idx as int));
  assert(task_log::is_timer_active(tl, rid, task_dereg_idx as int));
  assert(task_log::is_timer_registered_before(tl, rid, task_dereg_idx as int));
  assert(!task_log::is_timer_deregistered_before(tl, rid, task_dereg_idx as int));

  // Step 2: find RegisterTimer witness reg_m in tid_dereg's log
  let reg_m: int = choose |j: int|
    0 <= j < task_dereg_idx &&
    pe::is_register_timer(#[trigger] tl[j]) &&
    pe::get_resource_id(tl[j]) == Some(rid);

  // Step 3: operation_to_reactor_exists maps reg_m to reactor position r2
  assert(is_reactor_operation(tl[reg_m]));
  assert(operation_to_reactor_exists(s));
  let r2: int = choose |j: int|
    0 <= j < l.len() &&
    succ_reactor_event_matches_task_operation(#[trigger] l[j], tl[reg_m]);
  assert(re::is_succ_register_timer(l[r2]));
  assert(re::get_register_timer_rid(l[r2]) == rid);

  // Step 4: monotonic alignment gives r2 < reactor_dereg_idx
  assert(is_reactor_operation(tl[task_dereg_idx]));
  monotonic_alignment_use(s, tid_dereg, reg_m, task_dereg_idx, r2, reactor_dereg_idx);
  assert(r2 < reactor_dereg_idx);

  // Step 5: deregister_matches_own_registration gives timer_active_at(l, r2, reactor_dereg_idx)
  deregister_matches_own_registration_use(
    s, tid_dereg, reg_m, task_dereg_idx, r2, reactor_dereg_idx);
  assert(reactor_log::timer_active_at(l, r2, reactor_dereg_idx));

  // Step 6: if r2 == reactor_reg_idx, same reactor event => same task
  if r2 == reactor_reg_idx {
    assert(succ_reactor_event_matches_task_operation(l[reactor_reg_idx], tl[reg_m]));
    assert(succ_reactor_event_matches_task_operation(l[reactor_reg_idx], s.task_logs[tid_reg][task_reg_idx]));
    assert(reactor_to_operation_unique(s));
  } else {
    // r2 != reactor_reg_idx: two active registrations with same RID => contradiction
    two_active_regs_contradiction(
      s, reactor_reg_idx, reactor_dereg_idx, r2, rid);
  }
}

#[verifier::rlimit(50)]
proof fn two_active_regs_contradiction(
  s: ComposedState,
  reactor_reg_idx: int, reactor_dereg_idx: int,
  r2: int, rid: pe::RID,
)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    0 <= reactor_reg_idx < reactor_dereg_idx,
    reactor_dereg_idx < s.reactor_log.len(),
    re::is_succ_register_timer(s.reactor_log[reactor_reg_idx]),
    re::get_register_timer_rid(s.reactor_log[reactor_reg_idx]) == rid,
    0 <= r2 < reactor_dereg_idx,
    r2 < s.reactor_log.len(),
    re::is_succ_register_timer(s.reactor_log[r2]),
    re::get_register_timer_rid(s.reactor_log[r2]) == rid,
    r2 != reactor_reg_idx,
    reactor_log::timer_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx),
    reactor_log::timer_active_at(s.reactor_log, r2, reactor_dereg_idx),
  ensures false,
{
  let l = s.reactor_log;
  use crate::reactor::invariants::timer_reg_uniqueness;

  let tru = timer_reg_uniqueness::timer_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(tru, l));

  let (lo, hi) = if r2 < reactor_reg_idx {
    (r2, reactor_reg_idx)
  } else {
    (reactor_reg_idx, r2)
  };

  assert(reactor_log::is_succ_register_timer_at(l, hi));
  assert(re::get_register_timer_rid(l[hi]) == rid);
  assert((tru.acceptance)(l, hi));
  assert((tru.validity)(l, hi));
  timer_reg_uniqueness::reveal_no_prior_timer_registration(l, rid, hi);

  assert(reactor_log::is_succ_register_timer_at(l, lo));
  assert(re::get_register_timer_rid(l[lo]) == rid);

  let j: int = choose |j: int|
    lo < j < hi && #[trigger] reactor_log::timer_retired_at(l, rid, j);

  assert(lo < j && j < hi && hi <= reactor_dereg_idx);
  assert(lo < j && j < reactor_dereg_idx);
  assert(reactor_log::timer_active_at(l, lo, reactor_dereg_idx));
}

// ============================================================================
// io twin: derive_succ_deregister_io_by_owner (from deregister_io_matches_own_registration)
// ============================================================================

#[verifier::rlimit(50)]
pub proof fn derive_succ_deregister_io_by_owner(s: ComposedState)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    operation_alignment_inv(s),
    monotonic_task_reactor_alignment(s),
    deregister_io_matches_own_registration(s),
    forall |tid: TaskId|
      s.task_logs.contains_key(tid) ==>
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(
        #[trigger] s.task_logs[tid]),
  ensures
    succ_deregister_io_by_owner(s),
{
  reveal(succ_deregister_io_by_owner);
  assert forall |reactor_reg_idx: int, reactor_dereg_idx: int,
                 tid_reg: TaskId, task_reg_idx: int,
                 tid_dereg: TaskId, task_dereg_idx: int|
    0 <= reactor_reg_idx < reactor_dereg_idx &&
    reactor_dereg_idx < s.reactor_log.len() &&
    re::is_succ_io_syscall_register(s.reactor_log[reactor_reg_idx]) &&
    reactor_log::io_syscall_deregistered_at(s.reactor_log, reactor_dereg_idx) &&
    re::get_io_syscall_register_rid(s.reactor_log[reactor_reg_idx]) ==
      re::get_io_syscall_deregister_rid(s.reactor_log[reactor_dereg_idx]) &&
    reactor_log::io_syscall_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx) &&
    s.task_logs.contains_key(tid_reg) &&
    0 <= task_reg_idx < s.task_logs[tid_reg].len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid_reg][task_reg_idx]) &&
    s.task_logs.contains_key(tid_dereg) &&
    0 <= task_dereg_idx < s.task_logs[tid_dereg].len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid_dereg][task_dereg_idx])
    implies tid_reg == tid_dereg
  by {
    derive_step_io(
      s, reactor_reg_idx, reactor_dereg_idx,
      tid_reg, task_reg_idx, tid_dereg, task_dereg_idx);
  };
}

#[verifier::rlimit(50)]
proof fn derive_step_io(
  s: ComposedState,
  reactor_reg_idx: int, reactor_dereg_idx: int,
  tid_reg: TaskId, task_reg_idx: int,
  tid_dereg: TaskId, task_dereg_idx: int,
)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    operation_alignment_inv(s),
    monotonic_task_reactor_alignment(s),
    deregister_io_matches_own_registration(s),
    forall |tid: TaskId|
      s.task_logs.contains_key(tid) ==>
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(
        #[trigger] s.task_logs[tid]),
    0 <= reactor_reg_idx < reactor_dereg_idx,
    reactor_dereg_idx < s.reactor_log.len(),
    re::is_succ_io_syscall_register(s.reactor_log[reactor_reg_idx]),
    reactor_log::io_syscall_deregistered_at(s.reactor_log, reactor_dereg_idx),
    re::get_io_syscall_register_rid(s.reactor_log[reactor_reg_idx]) ==
      re::get_io_syscall_deregister_rid(s.reactor_log[reactor_dereg_idx]),
    reactor_log::io_syscall_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx),
    s.task_logs.contains_key(tid_reg),
    0 <= task_reg_idx < s.task_logs[tid_reg].len(),
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid_reg][task_reg_idx]),
    s.task_logs.contains_key(tid_dereg),
    0 <= task_dereg_idx < s.task_logs[tid_dereg].len(),
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid_dereg][task_dereg_idx]),
  ensures tid_reg == tid_dereg,
{
  let l = s.reactor_log;
  let tl = s.task_logs[tid_dereg];
  let rid = re::get_io_syscall_register_rid(l[reactor_reg_idx]);

  assert(pe::is_deregister_io(tl[task_dereg_idx]));
  assert(pe::get_resource_id(tl[task_dereg_idx]) == Some(rid));

  // Step 1: resource_ownership gives is_io_active at task_dereg_idx
  let ro = crate::utilities::invariants::resource_ownership::resource_ownership();
  assert(crate::framework::action_safety::action_safety_satisfied(ro, tl));
  assert(crate::utilities::invariants::resource_ownership::is_resource_operation(tl[task_dereg_idx]));
  assert((ro.acceptance)(tl, task_dereg_idx as int));
  assert((ro.validity)(tl, task_dereg_idx as int));
  assert(task_log::is_io_active(tl, rid, task_dereg_idx as int));
  assert(task_log::is_io_registered_before(tl, rid, task_dereg_idx as int));
  assert(!task_log::is_io_deregistered_before(tl, rid, task_dereg_idx as int));

  // Step 2: find RegisterIo witness reg_m in tid_dereg's log
  let reg_m: int = choose |j: int|
    0 <= j < task_dereg_idx &&
    pe::is_register_io(#[trigger] tl[j]) &&
    pe::get_resource_id(tl[j]) == Some(rid);

  // Step 3: operation_to_reactor_exists maps reg_m to reactor position r2
  assert(is_reactor_operation(tl[reg_m]));
  assert(operation_to_reactor_exists(s));
  let r2: int = choose |j: int|
    0 <= j < l.len() &&
    succ_reactor_event_matches_task_operation(#[trigger] l[j], tl[reg_m]);
  assert(re::is_succ_io_syscall_register(l[r2]));
  assert(re::get_io_syscall_register_rid(l[r2]) == rid);

  // Step 4: monotonic alignment gives r2 < reactor_dereg_idx
  assert(is_reactor_operation(tl[task_dereg_idx]));
  monotonic_alignment_use(s, tid_dereg, reg_m, task_dereg_idx, r2, reactor_dereg_idx);
  assert(r2 < reactor_dereg_idx);

  // Step 5: deregister_io_matches_own_registration gives io_syscall_active_at(l, r2, reactor_dereg_idx)
  deregister_io_matches_own_registration_use(
    s, tid_dereg, reg_m, task_dereg_idx, r2, reactor_dereg_idx);
  assert(reactor_log::io_syscall_active_at(l, r2, reactor_dereg_idx));

  // Step 6: if r2 == reactor_reg_idx, same reactor event => same task
  if r2 == reactor_reg_idx {
    assert(succ_reactor_event_matches_task_operation(l[reactor_reg_idx], tl[reg_m]));
    assert(succ_reactor_event_matches_task_operation(l[reactor_reg_idx], s.task_logs[tid_reg][task_reg_idx]));
    assert(reactor_to_operation_unique(s));
  } else {
    two_active_io_regs_contradiction(
      s, reactor_reg_idx, reactor_dereg_idx, r2, rid);
  }
}

#[verifier::rlimit(50)]
proof fn two_active_io_regs_contradiction(
  s: ComposedState,
  reactor_reg_idx: int, reactor_dereg_idx: int,
  r2: int, rid: pe::RID,
)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    0 <= reactor_reg_idx < reactor_dereg_idx,
    reactor_dereg_idx < s.reactor_log.len(),
    re::is_succ_io_syscall_register(s.reactor_log[reactor_reg_idx]),
    re::get_io_syscall_register_rid(s.reactor_log[reactor_reg_idx]) == rid,
    0 <= r2 < reactor_dereg_idx,
    r2 < s.reactor_log.len(),
    re::is_succ_io_syscall_register(s.reactor_log[r2]),
    re::get_io_syscall_register_rid(s.reactor_log[r2]) == rid,
    r2 != reactor_reg_idx,
    reactor_log::io_syscall_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx),
    reactor_log::io_syscall_active_at(s.reactor_log, r2, reactor_dereg_idx),
  ensures false,
{
  let l = s.reactor_log;
  use crate::reactor::invariants::io_reg_uniqueness;

  let iru = io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(iru, l));

  let (lo, hi) = if r2 < reactor_reg_idx {
    (r2, reactor_reg_idx)
  } else {
    (reactor_reg_idx, r2)
  };

  assert(reactor_log::io_syscall_registered_at(l, hi));
  assert(re::get_io_syscall_register_rid(l[hi]) == rid);
  assert((iru.acceptance)(l, hi));
  assert((iru.validity)(l, hi));
  io_reg_uniqueness::reveal_no_prior_io_syscall_registration(l, rid, hi);

  assert(reactor_log::io_syscall_registered_at(l, lo));
  assert(re::get_io_syscall_register_rid(l[lo]) == rid);

  let j: int = choose |j: int|
    lo < j < hi && #[trigger] reactor_log::io_syscall_deregistered_at(l, j) &&
    re::get_io_syscall_deregister_rid(l[j]) == rid;

  assert(lo < j && j < hi && hi <= reactor_dereg_idx);
  assert(lo < j && j < reactor_dereg_idx);
  assert(reactor_log::io_syscall_active_at(l, lo, reactor_dereg_idx));
}

}
