use vstd::prelude::*;
#[allow(unused_imports)]
use crate::composed::spec::state::*;
#[allow(unused_imports)]
use crate::composed::spec::types::*;
#[allow(unused_imports)]
use crate::composed::spec::progress::*;
#[allow(unused_imports)]
use crate::composed::spec::alignment::*;
#[allow(unused_imports)]
use crate::utilities::spec::events::RID;
#[allow(unused_imports)]
use crate::utilities::spec::events as utilities_events;
#[allow(unused_imports)]
use crate::reactor::spec::events as reactor_events;
#[allow(unused_imports)]
use crate::reactor::spec::log as reactor_log;

verus! {

pub proof fn rid_uniqueness_from_reactor_safety(s: ComposedState, rid: RID)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    operation_alignment_inv(s),
  ensures
    at_most_one_owner(s, rid),
{
  assert forall |tid1: TaskId, tid2: TaskId|
    composed_active_rid(s, tid1, rid) &&
    composed_active_rid(s, tid2, rid)
    implies tid1 == tid2
  by {
    if composed_active_rid(s, tid1, rid) && composed_active_rid(s, tid2, rid) {
      let (task_idx1, reactor_idx1) = composed_active_rid_witness(s, tid1, rid);
      let (task_idx2, reactor_idx2) = composed_active_rid_witness(s, tid2, rid);

      let pe1 = s.task_logs[tid1][task_idx1];
      let pe2 = s.task_logs[tid2][task_idx2];

      assert(is_reactor_operation(pe1));
      assert(is_reactor_operation(pe2));

      if reactor_idx1 == reactor_idx2 {
        same_reactor_registration_implies_same_task(s, tid1, tid2, task_idx1, task_idx2, reactor_idx1);
      } else {
        if utilities_events::is_register_timer(pe1) && utilities_events::is_register_timer(pe2) {
          timer_uniqueness_from_composed(s, rid, tid1, tid2, task_idx1, task_idx2, reactor_idx1, reactor_idx2);
        } else if utilities_events::is_register_io(pe1) && utilities_events::is_register_io(pe2) {
          io_uniqueness_from_composed(s, rid, tid1, tid2, task_idx1, task_idx2, reactor_idx1, reactor_idx2);
        } else {
          mixed_uniqueness_from_composed(s, rid, tid1, tid2, task_idx1, task_idx2, reactor_idx1, reactor_idx2);
        }
      }
    }
  };
}

#[verifier::rlimit(50)]
proof fn timer_uniqueness_from_composed(
  s: ComposedState, rid: RID,
  tid1: TaskId, tid2: TaskId,
  task_idx1: int, task_idx2: int,
  reactor_idx1: int, reactor_idx2: int,
)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    operation_alignment_inv(s),
    composed_active_rid(s, tid1, rid),
    composed_active_rid(s, tid2, rid),
    0 <= task_idx1 < s.task_logs[tid1].len(),
    0 <= task_idx2 < s.task_logs[tid2].len(),
    utilities_events::is_register_timer(s.task_logs[tid1][task_idx1]),
    utilities_events::is_register_timer(s.task_logs[tid2][task_idx2]),
    utilities_events::get_resource_id(s.task_logs[tid1][task_idx1]) == Some(rid),
    utilities_events::get_resource_id(s.task_logs[tid2][task_idx2]) == Some(rid),
    0 <= reactor_idx1 < s.reactor_log.len(),
    0 <= reactor_idx2 < s.reactor_log.len(),
    reactor_idx1 != reactor_idx2,
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx1], s.task_logs[tid1][task_idx1]),
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx2], s.task_logs[tid2][task_idx2]),
    forall |j: int| reactor_idx1 < j < s.reactor_log.len() ==>
      !reactor_log::timer_retired_at(s.reactor_log, rid, j),
    forall |j: int| reactor_idx2 < j < s.reactor_log.len() ==>
      !reactor_log::timer_retired_at(s.reactor_log, rid, j),
  ensures false,
{
  use crate::reactor::invariants::timer_reg_uniqueness;
  use crate::framework::action_safety::action_safety_satisfied;

  let l = s.reactor_log;
  let tru = timer_reg_uniqueness::timer_reg_uniqueness();
  assert(action_safety_satisfied(tru, l));

  let (lo, hi) = if reactor_idx1 < reactor_idx2 { (reactor_idx1, reactor_idx2) } else { (reactor_idx2, reactor_idx1) };

  assert(reactor_log::is_succ_register_timer_at(l, hi));
  assert(reactor_events::get_register_timer_rid(l[hi]) == rid);
  assert((tru.acceptance)(l, hi));
  assert((tru.validity)(l, hi));
  assert(timer_reg_uniqueness::no_prior_timer_registration(l, rid, hi));

  timer_reg_uniqueness::reveal_no_prior_timer_registration(l, rid, hi);

  assert(reactor_log::is_succ_register_timer_at(l, lo));
  assert(reactor_events::get_register_timer_rid(l[lo]) == rid);
  assert(0 <= lo && lo < hi);

  let j: int = choose |j: int|
    lo < j < hi &&
    #[trigger] reactor_log::timer_retired_at(l, rid, j);

  assert(lo < j < hi);
  assert(reactor_log::timer_retired_at(l, rid, j));
  assert(lo < j);
  assert(j < l.len());
  assert(!reactor_log::timer_retired_at(l, rid, j));
}

#[verifier::rlimit(50)]
proof fn io_uniqueness_from_composed(
  s: ComposedState, rid: RID,
  tid1: TaskId, tid2: TaskId,
  task_idx1: int, task_idx2: int,
  reactor_idx1: int, reactor_idx2: int,
)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    operation_alignment_inv(s),
    composed_active_rid(s, tid1, rid),
    composed_active_rid(s, tid2, rid),
    0 <= task_idx1 < s.task_logs[tid1].len(),
    0 <= task_idx2 < s.task_logs[tid2].len(),
    utilities_events::is_register_io(s.task_logs[tid1][task_idx1]),
    utilities_events::is_register_io(s.task_logs[tid2][task_idx2]),
    utilities_events::get_resource_id(s.task_logs[tid1][task_idx1]) == Some(rid),
    utilities_events::get_resource_id(s.task_logs[tid2][task_idx2]) == Some(rid),
    0 <= reactor_idx1 < s.reactor_log.len(),
    0 <= reactor_idx2 < s.reactor_log.len(),
    reactor_idx1 != reactor_idx2,
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx1], s.task_logs[tid1][task_idx1]),
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx2], s.task_logs[tid2][task_idx2]),
    forall |j: int| reactor_idx1 < j < s.reactor_log.len() ==>
      !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
        reactor_events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid),
    forall |j: int| reactor_idx2 < j < s.reactor_log.len() ==>
      !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
        reactor_events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid),
  ensures false,
{
  use crate::reactor::invariants::io_reg_uniqueness;
  use crate::framework::action_safety::action_safety_satisfied;

  let l = s.reactor_log;
  let iru = io_reg_uniqueness::io_reg_uniqueness();
  assert(action_safety_satisfied(iru, l));

  let (lo, hi) = if reactor_idx1 < reactor_idx2 { (reactor_idx1, reactor_idx2) } else { (reactor_idx2, reactor_idx1) };

  assert(reactor_log::io_syscall_registered_at(l, hi));
  assert(reactor_events::get_io_syscall_register_rid(l[hi]) == rid);
  assert((iru.acceptance)(l, hi));
  assert((iru.validity)(l, hi));
  assert(io_reg_uniqueness::no_prior_io_syscall_registration(l, rid, hi));

  io_reg_uniqueness::reveal_no_prior_io_syscall_registration(l, rid, hi);

  assert(reactor_log::io_syscall_registered_at(l, lo));
  assert(reactor_events::get_io_syscall_register_rid(l[lo]) == rid);
  assert(0 <= lo && lo < hi);

  let j: int = choose |j: int|
    lo < j < hi &&
    #[trigger] reactor_log::io_syscall_deregistered_at(l, j) &&
    reactor_events::get_io_syscall_deregister_rid(l[j]) == rid;

  assert(lo < j < hi);
  assert(reactor_log::io_syscall_deregistered_at(l, j));
  assert(reactor_events::get_io_syscall_deregister_rid(l[j]) == rid);
  assert(lo < j);
  assert(j < l.len());
  assert(!(reactor_log::io_syscall_deregistered_at(l, j) && reactor_events::get_io_syscall_deregister_rid(l[j]) == rid));
}

#[verifier::rlimit(50)]
proof fn mixed_uniqueness_from_composed(
  s: ComposedState, rid: RID,
  tid1: TaskId, tid2: TaskId,
  task_idx1: int, task_idx2: int,
  reactor_idx1: int, reactor_idx2: int,
)
  requires
    crate::reactor::invariants::reactor_inv(s.reactor_log),
    operation_alignment_inv(s),
    composed_active_rid(s, tid1, rid),
    composed_active_rid(s, tid2, rid),
    0 <= task_idx1 < s.task_logs[tid1].len(),
    0 <= task_idx2 < s.task_logs[tid2].len(),
    utilities_events::get_resource_id(s.task_logs[tid1][task_idx1]) == Some(rid),
    utilities_events::get_resource_id(s.task_logs[tid2][task_idx2]) == Some(rid),
    0 <= reactor_idx1 < s.reactor_log.len(),
    0 <= reactor_idx2 < s.reactor_log.len(),
    reactor_idx1 != reactor_idx2,
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx1], s.task_logs[tid1][task_idx1]),
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx2], s.task_logs[tid2][task_idx2]),
    (utilities_events::is_register_timer(s.task_logs[tid1][task_idx1]) &&
     utilities_events::is_register_io(s.task_logs[tid2][task_idx2])) ||
    (utilities_events::is_register_io(s.task_logs[tid1][task_idx1]) &&
     utilities_events::is_register_timer(s.task_logs[tid2][task_idx2])),
    utilities_events::is_register_timer(s.task_logs[tid1][task_idx1]) ==>
      forall |j: int| reactor_idx1 < j < s.reactor_log.len() ==>
        !reactor_log::timer_retired_at(s.reactor_log, rid, j),
    utilities_events::is_register_timer(s.task_logs[tid2][task_idx2]) ==>
      forall |j: int| reactor_idx2 < j < s.reactor_log.len() ==>
        !reactor_log::timer_retired_at(s.reactor_log, rid, j),
    utilities_events::is_register_io(s.task_logs[tid1][task_idx1]) ==>
      forall |j: int| reactor_idx1 < j < s.reactor_log.len() ==>
        !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
          reactor_events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid),
    utilities_events::is_register_io(s.task_logs[tid2][task_idx2]) ==>
      forall |j: int| reactor_idx2 < j < s.reactor_log.len() ==>
        !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
          reactor_events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid),
  ensures false,
{
  use crate::reactor::invariants::timer_io_disjoint;
  use crate::framework::action_safety::action_safety_satisfied;

  let l = s.reactor_log;
  let pe1 = s.task_logs[tid1][task_idx1];
  let pe2 = s.task_logs[tid2][task_idx2];

  if utilities_events::is_register_timer(pe1) && utilities_events::is_register_io(pe2) {
    let (timer_idx, io_idx) = (reactor_idx1, reactor_idx2);

    if timer_idx < io_idx {
      let disjoint = timer_io_disjoint::timer_io_disjoint_at_io();
      assert(action_safety_satisfied(disjoint, l));
      assert(reactor_log::io_syscall_registered_at(l, io_idx));
      assert((disjoint.acceptance)(l, io_idx));
      assert((disjoint.validity)(l, io_idx));
      assert(timer_io_disjoint::no_timer_with_rid_before(l, rid, io_idx));
      timer_io_disjoint::reveal_no_timer_with_rid_before(l, rid, io_idx);
      assert(reactor_log::is_succ_register_timer_at(l, timer_idx));
      assert(reactor_events::get_register_timer_rid(l[timer_idx]) == rid);
      let j: int = choose |j: int|
        timer_idx < j < io_idx &&
        #[trigger] reactor_log::timer_retired_at(l, rid, j);
      assert(timer_idx < j);
      assert(j < l.len());
      assert(!reactor_log::timer_retired_at(l, rid, j));
    } else {
      let disjoint = timer_io_disjoint::timer_io_disjoint_at_timer();
      assert(action_safety_satisfied(disjoint, l));
      assert(reactor_log::is_succ_register_timer_at(l, timer_idx));
      assert((disjoint.acceptance)(l, timer_idx));
      assert((disjoint.validity)(l, timer_idx));
      assert(timer_io_disjoint::no_io_syscall_registration_with_rid(l, rid, timer_idx));
      timer_io_disjoint::reveal_no_io_syscall_registration_with_rid(l, rid, timer_idx);
      assert(reactor_log::io_syscall_registered_at(l, io_idx));
      assert(reactor_events::get_io_syscall_register_rid(l[io_idx]) == rid);
      let j: int = choose |j: int|
        io_idx < j < timer_idx &&
        #[trigger] reactor_log::io_syscall_deregistered_at(l, j) &&
        reactor_events::get_io_syscall_deregister_rid(l[j]) == rid;
      assert(io_idx < j);
      assert(j < l.len());
      assert(!(reactor_log::io_syscall_deregistered_at(l, j) && reactor_events::get_io_syscall_deregister_rid(l[j]) == rid));
    }
  } else {
    assert(utilities_events::is_register_io(pe1) && utilities_events::is_register_timer(pe2));
    let (io_idx, timer_idx) = (reactor_idx1, reactor_idx2);

    if timer_idx < io_idx {
      let disjoint = timer_io_disjoint::timer_io_disjoint_at_io();
      assert(action_safety_satisfied(disjoint, l));
      assert(reactor_log::io_syscall_registered_at(l, io_idx));
      assert((disjoint.acceptance)(l, io_idx));
      assert((disjoint.validity)(l, io_idx));
      assert(timer_io_disjoint::no_timer_with_rid_before(l, rid, io_idx));
      timer_io_disjoint::reveal_no_timer_with_rid_before(l, rid, io_idx);
      assert(reactor_log::is_succ_register_timer_at(l, timer_idx));
      assert(reactor_events::get_register_timer_rid(l[timer_idx]) == rid);
      let j: int = choose |j: int|
        timer_idx < j < io_idx &&
        #[trigger] reactor_log::timer_retired_at(l, rid, j);
      assert(timer_idx < j);
      assert(j < l.len());
      assert(!reactor_log::timer_retired_at(l, rid, j));
    } else {
      let disjoint = timer_io_disjoint::timer_io_disjoint_at_timer();
      assert(action_safety_satisfied(disjoint, l));
      assert(reactor_log::is_succ_register_timer_at(l, timer_idx));
      assert((disjoint.acceptance)(l, timer_idx));
      assert((disjoint.validity)(l, timer_idx));
      assert(timer_io_disjoint::no_io_syscall_registration_with_rid(l, rid, timer_idx));
      timer_io_disjoint::reveal_no_io_syscall_registration_with_rid(l, rid, timer_idx);
      assert(reactor_log::io_syscall_registered_at(l, io_idx));
      assert(reactor_events::get_io_syscall_register_rid(l[io_idx]) == rid);
      let j: int = choose |j: int|
        io_idx < j < timer_idx &&
        #[trigger] reactor_log::io_syscall_deregistered_at(l, j) &&
        reactor_events::get_io_syscall_deregister_rid(l[j]) == rid;
      assert(io_idx < j);
      assert(j < l.len());
      assert(!(reactor_log::io_syscall_deregistered_at(l, j) && reactor_events::get_io_syscall_deregister_rid(l[j]) == rid));
    }
  }
}

proof fn same_reactor_registration_implies_same_task(
  s: ComposedState,
  tid1: TaskId,
  tid2: TaskId,
  task_idx1: int,
  task_idx2: int,
  reactor_idx: int,
)
  requires
    operation_alignment_inv(s),
    s.task_logs.contains_key(tid1),
    s.task_logs.contains_key(tid2),
    0 <= task_idx1 < s.task_logs[tid1].len(),
    0 <= task_idx2 < s.task_logs[tid2].len(),
    is_reactor_operation(s.task_logs[tid1][task_idx1]),
    is_reactor_operation(s.task_logs[tid2][task_idx2]),
    0 <= reactor_idx < s.reactor_log.len(),
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx], s.task_logs[tid1][task_idx1]),
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx], s.task_logs[tid2][task_idx2]),
  ensures
    tid1 == tid2,
{
  assert(operation_alignment_inv(s));
  assert(reactor_to_operation_unique(s));
}

pub open spec fn at_most_one_owner(s: ComposedState, rid: RID) -> bool {
  forall |tid1: TaskId, tid2: TaskId|
    composed_active_rid(s, tid1, rid) &&
    composed_active_rid(s, tid2, rid)
    ==> tid1 == tid2
}

}
