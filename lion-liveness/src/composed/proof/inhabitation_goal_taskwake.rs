use vstd::prelude::*;
#[allow(unused_imports)]
use crate::composed::spec::state::*;
#[allow(unused_imports)]
use crate::composed::spec::types::*;
#[allow(unused_imports)]
use crate::composed::spec::progress::*;
#[allow(unused_imports)]
use crate::composed::spec::alignment::*;
use crate::executor::spec::events as ee;
use crate::executor::spec::types::TID;
use crate::executor::spec::log as el;
use crate::reactor::spec::events as re;
use crate::reactor::spec::log as rl;
use crate::utilities::spec::events as ue;
use crate::utilities::spec::log as ul;
#[cfg(verus_keep_ghost)]
use crate::composed::proof::inhabitation_goal_wake::{bexec1, bsched,
  bexec1_idx, bexec1_flags, bexec1_exec_progress, bexec1_queue, bexec1_queue_len,
  bpoll_count_bexec1, bexec_injected};
#[cfg(verus_keep_ghost)]
use crate::composed::proof::inhabitation_goal_defer::{dreac1, dreac2,
  dreac1_idx, dreac2_idx, dreac1_flags, dreac2_flags, dreac1_reac_progress, dreac2_reac_progress,
  d_reac_env_facts};
#[cfg(verus_keep_ghost)]
use crate::composed::proof::assumption_satisfiable::{env_N, bounded_poll_count_here_with_bound,
  io_ready_forward_here, end_to_end_env, env_holds_at_state_core,
  taskwake_arrival_within};
#[cfg(verus_keep_ghost)]
use crate::composed::spec::assumptions::{
  timer_deadline_gap_bounded, timer_resources_remain_active,
  queue_length_bounded, get_max_timer_deadline_gap,
  get_max_queue_length};

verus! {

// ============================================================================
// TASKWAKE witness: a task registers a cross-task waker (PassWaker), its waker is
// invoked (Woken), it polls Pending, and the executor's TaskWake queue redelivers
// it (Drain{TaskWake}[tid]) to be polled Ready. The reactor does empty park cycles
// (reused dreac). Exercises taskwake_drain_step NON-vacuously (taskwake_pending
// holds via the Woken event); taskwake_arrival_within holds vacuously at both trace
// states (ts1 has no post-poll Drain{TaskWake}, ts2 is Ready) — its NON-vacuous
// discharge is the standalone taskwake_arrival_within_nonvacuous_witness below.
// cap = 2. UID for the waker handle:
// ============================================================================

pub open spec fn UID() -> ue::UID { 5 }

// --- Executor: texec1 = bexec1; texec2 delivers tid via Drain{TaskWake}[tid]@11. ---
pub open spec fn texec2(tid: TID) -> el::Log {
  bexec1(tid) + seq![
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection { task: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: seq![tid],
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: tid, task: None, result: crate::executor::spec::types::PollResult::Ready(()),
    }),
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
  ]
}

pub proof fn texec2_idx(tid: TID)
  ensures
    texec2(tid).len() == 16,
    forall |k: int| 0 <= k < 8 ==> texec2(tid)[k] == bexec1(tid)[k],
    texec2(tid)[8] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    texec2(tid)[11] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: seq![tid] }),
    texec2(tid)[12] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    texec2(tid)[14] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: tid, task: None, result: crate::executor::spec::types::PollResult::Ready(()) }),
    texec2(tid)[15] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
{
  bexec1_idx(tid);
}

pub proof fn texec2_flags(tid: TID, k: int)
  ensures
    (k != 0 && k != 8) ==> !el::is_tick_begin_at(texec2(tid), k),
    (k != 7 && k != 15) ==> !el::is_tick_end_at(texec2(tid), k),
    (k != 4 && k != 12) ==> !el::is_park_at(texec2(tid), k),
    (k != 1 && k != 9) ==> !el::is_pop_injection_at(texec2(tid), k),
    (k != 6 && k != 14) ==> !el::is_poll_task_at(texec2(tid), k),
{
  texec2_idx(tid);
  if 0 <= k < 8 { bexec1_idx(tid); }
}

// Queue: TaskWake[tid]@11 pushes tid; it stays through 12,13; poll@14 removes it.
pub proof fn texec2_queue(tid: TID)
  ensures
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(texec2(tid), 6) =~= seq![tid],
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(texec2(tid), 14) =~= seq![tid],
    forall |i: int| 2 <= i <= 6 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(texec2(tid), i) =~= seq![tid],
    forall |i: int| 7 <= i <= 11 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(texec2(tid), i) =~= Seq::<TID>::empty(),
    forall |i: int| 12 <= i <= 14 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(texec2(tid), i) =~= seq![tid],
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(texec2(tid), 0) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(texec2(tid), 15) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(texec2(tid), 16) =~= Seq::<TID>::empty(),
{
  let l = texec2(tid);
  texec2_idx(tid); bexec1_idx(tid);
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  assert(fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 1) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 2) =~= seq![tid]);
  assert(fifo_queue_at(l, 3) =~= seq![tid]);
  assert(fifo_queue_at(l, 4) =~= seq![tid]);
  assert(fifo_queue_at(l, 5) =~= seq![tid]);
  assert(fifo_queue_at(l, 6) =~= seq![tid]);
  assert(fifo_queue_at(l, 7) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 8) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 9) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 10) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 11) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 12) =~= seq![tid]);
  assert(fifo_queue_at(l, 13) =~= seq![tid]);
  assert(fifo_queue_at(l, 14) =~= seq![tid]);
  assert(fifo_queue_at(l, 15) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 16) =~= Seq::<TID>::empty());
  assert forall |i: int| 2 <= i <= 6 implies #[trigger] fifo_queue_at(l, i) =~= seq![tid] by {
    if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {}
  }
  assert forall |i: int| 7 <= i <= 11 implies #[trigger] fifo_queue_at(l, i) =~= Seq::<TID>::empty() by {
    if i == 7 {} else if i == 8 {} else if i == 9 {} else if i == 10 {} else if i == 11 {}
  }
  assert forall |i: int| 12 <= i <= 14 implies #[trigger] fifo_queue_at(l, i) =~= seq![tid] by {
    if i == 12 {} else if i == 13 {} else if i == 14 {}
  }
}

pub proof fn texec2_queue_len(tid: TID)
  ensures
    forall |i: int| 0 <= i <= texec2(tid).len() ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(texec2(tid), i).len() <= 1,
    forall |i: int| 0 <= i <= texec2(tid).len() ==>
      #[trigger] el::fifo_queue_at_for_persistent(texec2(tid), i).len() <= 1,
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  texec2_idx(tid);
  let l = texec2(tid);
  texec2_queue(tid);
  assert forall |i: int| 0 <= i <= l.len() implies #[trigger] fifo_queue_at(l, i).len() <= 1 by {
    texec2_queue(tid);
    if 2 <= i <= 6 { } else if 7 <= i <= 11 { } else if 12 <= i <= 14 { }
    else if i == 15 || i == 16 { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
  }
  assert forall |i: int| 0 <= i <= l.len() implies #[trigger] el::fifo_queue_at_for_persistent(l, i).len() <= 1 by {
    texec2_queue(tid);
    if 2 <= i <= 6 { } else if 7 <= i <= 11 { } else if 12 <= i <= 14 { }
    else if i == 15 || i == 16 { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
  }
}

proof fn texec2_tick_structure(tid: TID)
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_park::tick_has_park(), texec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection(), texec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred(), texec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake(), texec2(tid)),
{
  let l = texec2(tid);
  texec2_idx(tid);
  let pk = crate::executor::invariants::tick_has_park::tick_has_park();
  assert(crate::framework::action_safety::action_safety_satisfied(pk, l)) by {
    assert forall |i: int| #[trigger] (pk.acceptance)(l, i) implies (pk.validity)(l, i) by {
      texec2_flags(tid, i);
      if i == 7 { assert(el::is_park_at(l, 4)); assert forall |k: int| 4 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { texec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_park_at(l, 12)); assert forall |k: int| 12 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { texec2_flags(tid, k); } }
    } }
  let pp = crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection();
  assert(crate::framework::action_safety::action_safety_satisfied(pp, l)) by {
    assert forall |i: int| #[trigger] (pp.acceptance)(l, i) implies (pp.validity)(l, i) by {
      texec2_flags(tid, i);
      if i == 7 { assert(el::is_pop_injection_at(l, 1)); assert forall |k: int| 1 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { texec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_pop_injection_at(l, 9)); assert forall |k: int| 9 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { texec2_flags(tid, k); } }
    } }
  let dd = crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred();
  assert(crate::framework::action_safety::action_safety_satisfied(dd, l)) by {
    assert forall |i: int| #[trigger] (dd.acceptance)(l, i) implies (dd.validity)(l, i) by {
      texec2_flags(tid, i);
      if i == 7 { assert(el::is_drain_deferred_at(l, 2)); assert forall |k: int| 2 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { texec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_drain_deferred_at(l, 10)); assert forall |k: int| 10 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { texec2_flags(tid, k); } }
    } }
  let dt = crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake();
  assert(crate::framework::action_safety::action_safety_satisfied(dt, l)) by {
    assert forall |i: int| #[trigger] (dt.acceptance)(l, i) implies (dt.validity)(l, i) by {
      texec2_flags(tid, i);
      if i == 7 { assert(el::is_drain_task_wake_at(l, 3)); assert forall |k: int| 3 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { texec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_drain_task_wake_at(l, 11)); assert forall |k: int| 11 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { texec2_flags(tid, k); } }
    } }
}

pub proof fn texec2_exec_inv(tid: TID)
  ensures
    crate::executor::invariants::executor_inv(texec2(tid)),
{
  let l = texec2(tid);
  texec2_idx(tid);
  texec2_queue(tid);
  let p_fifo = crate::executor::invariants::fifo_task_selection::fifo_task_selection();
  assert(crate::framework::action_safety::action_safety_satisfied(p_fifo, l)) by {
    assert forall |i: int| #[trigger] (p_fifo.acceptance)(l, i) implies (p_fifo.validity)(l, i) by {
      texec2_flags(tid, i);
      if i == 6 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 6, tid)); }
      else if i == 14 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 14, tid)); }
    }
  }
  let p_vtp = crate::executor::invariants::valid_task_polling::valid_task_polling();
  assert(crate::framework::action_safety::action_safety_satisfied(p_vtp, l)) by {
    assert forall |i: int| #[trigger] (p_vtp.acceptance)(l, i) implies (p_vtp.validity)(l, i) by {
      texec2_flags(tid, i);
      if i == 6 || i == 14 {
        assert(el::is_pop_injection_at(l, 1) && ee::get_pop_injection_task(l[1]).unwrap().id == tid);
        assert(crate::executor::invariants::valid_task_polling::tid_was_injected_before(l, i, tid));
        assert(!crate::executor::invariants::valid_task_polling::tid_returned_ready_before(l, i, tid)) by {
          assert forall |j: int| 0 <= j < i implies
            !(el::is_poll_task_at(l, j) && ee::get_poll_task_id(l[j]) == tid
              && ee::get_poll_result(l[j]) == crate::executor::spec::types::PollResult::Ready(())) by { texec2_flags(tid, j); }
        }
        assert(!crate::executor::invariants::valid_task_polling::tid_is_invalid(l, i, tid));
      }
    }
  }
  texec2_tick_structure(tid);
  let p_pdrw = crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_pdrw, l)) by {
    assert forall |i: int| #[trigger] (p_pdrw.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_pdrw.fulfillment)(l, i, j)]
        j > i && (p_pdrw.fulfillment)(l, i, j) && (p_pdrw.timely)(l, i, j) by {
      texec2_flags(tid, i);
      if i == 4 {
        assert(el::is_drain_reactor_wake_at(l, 5));
        assert forall |k: int| 4 < k < 5 implies !#[trigger] el::is_tick_end_at(l, k) by { texec2_flags(tid, k); }
        assert(5 > 4 && (p_pdrw.fulfillment)(l, 4, 5) && (p_pdrw.timely)(l, 4, 5));
      } else if i == 12 {
        assert(el::is_drain_reactor_wake_at(l, 13));
        assert forall |k: int| 12 < k < 13 implies !#[trigger] el::is_tick_end_at(l, k) by { texec2_flags(tid, k); }
        assert(13 > 12 && (p_pdrw.fulfillment)(l, 12, 13) && (p_pdrw.timely)(l, 12, 13));
      }
    }
  }
  let p_tpr = crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_tpr, l)) by {
    assert forall |i: int| #[trigger] (p_tpr.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_tpr.fulfillment)(l, i, j)]
        j > i && (p_tpr.fulfillment)(l, i, j) && (p_tpr.timely)(l, i, j) by {
      texec2_flags(tid, i);
      if i == 0 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
      } else if i == 8 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 8) =~= Seq::<TID>::empty());
      }
    }
  }
}

pub proof fn texec2_exec_progress(tid: TID)
  ensures
    crate::executor::executor_progress(bexec1(tid), texec2(tid)),
{
  let l1 = bexec1(tid);
  let l2 = texec2(tid);
  texec2_idx(tid);
  texec2_exec_inv(tid);
  assert(l1 =~= l2.subrange(0, 8));
  assert(crate::executor::is_complete_tick_cycle(l2, 8, 16)) by {
    assert(el::is_tick_begin_at(l2, 8));
    assert(el::is_tick_end_at(l2, 15));
    assert forall |k: int| 8 < k < 15 implies
      !#[trigger] el::is_tick_begin_at(l2, k) && !el::is_tick_end_at(l2, k) by { texec2_flags(tid, k); }
  }
}

pub proof fn texec2_pops(tid: TID)
  ensures
    crate::executor::spec::injection_schedule::pops_deliver_schedule(texec2(tid), bsched(tid)),
{
  use crate::executor::spec::injection_schedule::*;
  texec2_idx(tid); bexec1_idx(tid); bexec_injected(tid);
  let l = texec2(tid);
  assert(l.subrange(0, 8) =~= bexec1(tid));
  assert(injected_tasks(l.subrange(0, 8)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l.subrange(0,9).subrange(0,8) =~= l.subrange(0,8));
  assert(injected_tasks(l.subrange(0, 9)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l.subrange(0,10).subrange(0,9) =~= l.subrange(0,9));
  assert(injected_tasks(l.subrange(0, 10)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l.subrange(0,11).subrange(0,10) =~= l.subrange(0,10));
  assert(injected_tasks(l.subrange(0, 11)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l.subrange(0,12).subrange(0,11) =~= l.subrange(0,11));
  assert(injected_tasks(l.subrange(0, 12)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l.subrange(0,13).subrange(0,12) =~= l.subrange(0,12));
  assert(injected_tasks(l.subrange(0, 13)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l.subrange(0,14).subrange(0,13) =~= l.subrange(0,13));
  assert(injected_tasks(l.subrange(0, 14)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l.subrange(0,15).subrange(0,14) =~= l.subrange(0,14));
  assert(injected_tasks(l.subrange(0, 15)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l.subrange(0,16).subrange(0,15) =~= l.subrange(0,15));
  assert(l.subrange(0,16) =~= l);
  assert(injected_tasks(l) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(injected_tasks(l) =~= bsched(tid).subrange(0, 1));
  assert(is_task_prefix(injected_tasks(l), bsched(tid)));
}

// --- Task log: Poll(begin), PassWaker(uid), Woken(uid), Poll(Pending), [Poll, Ready] ---
pub open spec fn ttask_pending() -> ul::Log {
  seq![
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    ue::UtilityEvent::Outbound(ue::OutboundCall::PassWaker { uid: UID() }),
    ue::UtilityEvent::Outbound(ue::OutboundCall::Woken { uid: UID() }),
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: Some(ue::PollResult::Pending) }),
  ]
}

pub open spec fn ttask_ready() -> ul::Log {
  ttask_pending() + seq![
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: Some(ue::PollResult::Ready) }),
  ]
}

pub proof fn ttask_idx()
  ensures
    ttask_pending().len() == 4,
    ttask_ready().len() == 6,
    forall |i: int| 0 <= i < 4 ==> ttask_ready()[i] == ttask_pending()[i],
    ue::is_poll_begin(ttask_pending()[0]),
    ue::is_pass_waker(ttask_pending()[1]),
    ue::is_woken(ttask_pending()[2]),
    ue::is_poll_end_pending(ttask_pending()[3]),
    ue::is_poll_begin(ttask_ready()[4]),
    ue::is_poll_end(ttask_ready()[5]),
    !ue::is_poll_end_pending(ttask_ready()[5]),
    forall |i: int| #![trigger ttask_ready()[i]] 0 <= i < ttask_ready().len() ==>
      !crate::composed::spec::alignment::is_reactor_operation(ttask_ready()[i]),
    forall |i: int| #![trigger ttask_pending()[i]] 0 <= i < ttask_pending().len() ==>
      !crate::composed::spec::alignment::is_reactor_operation(ttask_pending()[i]),
{
  assert forall |i: int| #![trigger ttask_ready()[i]] 0 <= i < ttask_ready().len() implies
    !crate::composed::spec::alignment::is_reactor_operation(ttask_ready()[i]) by {
    if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {}
  }
  assert forall |i: int| #![trigger ttask_pending()[i]] 0 <= i < ttask_pending().len() implies
    !crate::composed::spec::alignment::is_reactor_operation(ttask_pending()[i]) by {
    if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {}
  }
}

pub proof fn ttask_utilities_inv()
  ensures
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(ttask_pending()),
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(ttask_ready()),
{
  ttask_idx();
  use crate::utilities::invariants::wakeup_guarantee::*;
  let wg = wakeup_guarantee();
  let ro = crate::utilities::invariants::resource_ownership::resource_ownership();
  // wakeup_guarantee @3 (PollEnd Pending): has_pass_waker_in_current_poll (PassWaker@1).
  assert(crate::framework::action_safety::action_safety_satisfied(wg, ttask_pending())) by {
    assert forall |i: int| #[trigger] (wg.acceptance)(ttask_pending(), i) implies (wg.validity)(ttask_pending(), i) by {
      if i == 3 {
        assert(crate::utilities::spec::log::current_poll_start(ttask_pending(), 3) == 0) by {
          assert(ue::is_poll_begin(ttask_pending()[0]));
          assert(crate::utilities::spec::log::find_last_poll_begin(ttask_pending(), 0) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(ttask_pending(), 1) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(ttask_pending(), 2) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(ttask_pending(), 3) == 0);
        }
        assert(crate::utilities::spec::log::has_pass_waker_in_current_poll(ttask_pending(), 3)) by {
          assert(crate::utilities::spec::log::in_current_poll_cycle(ttask_pending(), 1, 3));
          assert(ue::is_pass_waker(ttask_pending()[1]));
        }
        assert(crate::utilities::spec::log::has_active_wakeup_source(ttask_pending(), 3));
      }
    }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(ro, ttask_pending())) by {
    assert forall |i: int| #[trigger] (ro.acceptance)(ttask_pending(), i) implies (ro.validity)(ttask_pending(), i) by { }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(wg, ttask_ready())) by {
    assert forall |i: int| #[trigger] (wg.acceptance)(ttask_ready(), i) implies (wg.validity)(ttask_ready(), i) by {
      if i == 3 {
        assert(crate::utilities::spec::log::current_poll_start(ttask_ready(), 3) == 0) by {
          assert(ue::is_poll_begin(ttask_ready()[0]));
          assert(crate::utilities::spec::log::find_last_poll_begin(ttask_ready(), 0) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(ttask_ready(), 1) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(ttask_ready(), 2) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(ttask_ready(), 3) == 0);
        }
        assert(crate::utilities::spec::log::has_pass_waker_in_current_poll(ttask_ready(), 3)) by {
          assert(crate::utilities::spec::log::in_current_poll_cycle(ttask_ready(), 1, 3));
          assert(ue::is_pass_waker(ttask_ready()[1]));
        }
        assert(crate::utilities::spec::log::has_active_wakeup_source(ttask_ready(), 3));
      }
    }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(ro, ttask_ready())) by {
    assert forall |i: int| #[trigger] (ro.acceptance)(ttask_ready(), i) implies (ro.validity)(ttask_ready(), i) by { }
  }
}

// ============================================================================
// Composed states + alignment + progress + env + domain
// ============================================================================

pub open spec fn ts1(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: bexec1(tid),
    reactor_log: dreac1(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, ttask_pending()),
    injection_schedule: bsched(tid),
  }
}

pub open spec fn ts2(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: texec2(tid),
    reactor_log: dreac2(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, ttask_ready()),
    injection_schedule: bsched(tid),
  }
}

// action_mediation_state: 0 reactor ops + no task-initiated reactor events ⟹ vacuous.
#[verifier::rlimit(50)]
proof fn ts_am_state(s: ComposedState, tid: TID)
  requires
    s.task_logs.contains_key(tid),
    (s.reactor_log == dreac1() && s.task_logs[tid] == ttask_pending()) ||
    (s.reactor_log == dreac2() && s.task_logs[tid] == ttask_ready()),
    forall |t2: TaskId| s.task_logs.contains_key(t2) ==> t2 == tid,
  ensures
    crate::composed::spec::alignment::action_mediation_state(s),
{
  dreac1_idx(); dreac2_idx(); ttask_idx();
  use crate::composed::spec::alignment::*;
  let is1 = s.reactor_log == dreac1();
  assert(operation_to_reactor_exists(s)) by {
    assert forall |t2: TaskId, i: int|
      s.task_logs.contains_key(t2) && 0 <= i < s.task_logs[t2].len() &&
      is_reactor_operation(#[trigger] s.task_logs[t2][i])
      implies exists |j: int| 0 <= j < s.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][i]) by { assert(t2 == tid); }
  }
  assert(reactor_registration_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() &&
      (re::is_succ_register_timer(s.reactor_log[j]) || re::is_succ_io_syscall_register(s.reactor_log[j]))
      implies exists |t2: TaskId, ti: int| s.task_logs.contains_key(t2) &&
        0 <= ti < s.task_logs[t2].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][ti]) by {
      if is1 { dreac1_flags(j); } else { dreac2_flags(j); }
    }
  }
  assert(reactor_outbound_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() && is_task_initiated_reactor_event(s.reactor_log[j])
      implies exists |t2: TaskId, ti: int| s.task_logs.contains_key(t2) &&
        0 <= ti < s.task_logs[t2].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][ti]) by {
      if is1 { dreac1_flags(j); } else { dreac2_flags(j); }
    }
  }
  assert(reactor_to_operation_unique(s)) by {
    assert forall |t1: TaskId, t2: TaskId, ti1: int, ti2: int, ri: int|
      #![trigger s.task_logs[t1][ti1], s.task_logs[t2][ti2], s.reactor_log[ri]]
      s.task_logs.contains_key(t1) && s.task_logs.contains_key(t2) &&
      0 <= ti1 < s.task_logs[t1].len() && 0 <= ti2 < s.task_logs[t2].len() &&
      is_reactor_operation(s.task_logs[t1][ti1]) && is_reactor_operation(s.task_logs[t2][ti2]) &&
      0 <= ri < s.reactor_log.len() &&
      succ_reactor_event_matches_task_operation(s.reactor_log[ri], s.task_logs[t1][ti1]) &&
      succ_reactor_event_matches_task_operation(s.reactor_log[ri], s.task_logs[t2][ti2])
      implies t1 == t2 && ti1 == ti2 by { assert(t1 == tid); }
  }
  assert forall |t2: TaskId, a: int, b: int|
    #![trigger s.task_logs[t2][a], s.task_logs[t2][b]]
    s.task_logs.contains_key(t2) && 0 <= a < b < s.task_logs[t2].len() &&
    is_reactor_operation(s.task_logs[t2][a])
    implies !is_reactor_operation(s.task_logs[t2][b]) by { assert(t2 == tid); }
  monotonic_alignment_holds_no_two_ops(s);
  assert(succ_deregister_by_owner(s)) by { reveal(succ_deregister_by_owner); }
  assert(deregister_matches_own_registration(s)) by { reveal(deregister_matches_own_registration); }
  assert(deregister_io_matches_own_registration(s)) by { reveal(deregister_io_matches_own_registration); }
  assert(succ_deregister_io_by_owner(s)) by { reveal(succ_deregister_io_by_owner); }
}

proof fn ts1_obs_consistency(tid: TID)
  ensures
    crate::composed::spec::alignment::observation_consistency_state(ts1(tid)),
    crate::composed::spec::alignment::observation_consistency_step(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ts1(tid)),
{
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = ts1(tid);
  bexec1_idx(tid); ttask_idx();
  use crate::composed::spec::alignment::*;
  assert(observation_consistency_state(s2)) by {
    assert(polled_task_has_log_inv(s2)) by {
      assert forall |t2: TaskId| el::has_poll_for_id(s2.executor_log, t2) implies s2.task_logs.contains_key(t2) by {
        if !s2.task_logs.contains_key(t2) {
          assert forall |i: int| #![trigger s2.executor_log[i]] 0 <= i < s2.executor_log.len()
            implies !el::is_poll_task_for_id_at(s2.executor_log, i, t2) by { bexec1_flags(tid, i); }
        }
      }
    }
    assert(pending_poll_inv(s2)) by {
      assert forall |t2: TaskId| #![trigger s2.task_logs[t2]]
        s2.task_logs.contains_key(t2) && el::last_poll_is_pending(s2.executor_log, t2)
        implies task_log_ends_with_pending(s2.task_logs[t2]) by {
        assert(t2 == tid);
        assert(ue::is_poll_end_pending(ttask_pending()[3]));
      }
    }
  }
  assert(observation_consistency_step(s, s2)) by {
    assert(poll_alignment(s, s2)) by {
      assert forall |t2: TaskId| #![trigger s2.task_logs[t2]]
        s.task_logs.contains_key(t2) && s2.task_logs.contains_key(t2) &&
        s.task_logs[t2].len() < s2.task_logs[t2].len()
        implies el::has_poll_task_for_id_after(s2.executor_log, t2, s.executor_log.len() as int) by {
        assert(!s.task_logs.contains_key(t2));
      }
    }
    assert(pending_poll_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_pending_for_id_at(s2.executor_log, i, t2) && s2.task_logs.contains_key(t2)
        implies task_log_ends_with_pending(s2.task_logs[t2]) by {
        assert(t2 == tid && i == 6);
        assert(ue::is_poll_end_pending(ttask_pending()[3]));
      }
    }
    assert(new_poll_has_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2)
        implies s2.task_logs.contains_key(t2) by { assert(i == 6 && t2 == tid); }
    }
    assert(new_poll_changes_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2) && s.task_logs.contains_key(t2)
        implies s.task_logs[t2].len() < s2.task_logs[t2].len() by { assert(!s.task_logs.contains_key(t2)); }
    }
  }
}

proof fn ts2_obs_consistency(tid: TID)
  ensures
    crate::composed::spec::alignment::observation_consistency_state(ts2(tid)),
    crate::composed::spec::alignment::observation_consistency_step(ts1(tid), ts2(tid)),
{
  let s = ts1(tid);
  let s2 = ts2(tid);
  texec2_idx(tid); bexec1_idx(tid); ttask_idx();
  use crate::composed::spec::alignment::*;
  assert(observation_consistency_state(s2)) by {
    assert(polled_task_has_log_inv(s2)) by {
      assert forall |t2: TaskId| el::has_poll_for_id(s2.executor_log, t2) implies s2.task_logs.contains_key(t2) by {
        if !s2.task_logs.contains_key(t2) {
          assert forall |i: int| #![trigger s2.executor_log[i]] 0 <= i < s2.executor_log.len()
            implies !el::is_poll_task_for_id_at(s2.executor_log, i, t2) by { texec2_flags(tid, i); }
        }
      }
    }
    assert(pending_poll_inv(s2)) by {
      assert forall |t2: TaskId| #![trigger s2.task_logs[t2]]
        s2.task_logs.contains_key(t2) && el::last_poll_is_pending(s2.executor_log, t2)
        implies task_log_ends_with_pending(s2.task_logs[t2]) by {
        assert(t2 == tid);
        crate::composed::proof::end_to_end::last_poll_idx_properties(s2.executor_log, tid);
        assert(el::is_poll_task_for_id_at(s2.executor_log, 14, tid));
        assert(!el::is_poll_pending_for_id_at(s2.executor_log, 14, tid));
      }
    }
  }
  assert(observation_consistency_step(s, s2)) by {
    assert(poll_alignment(s, s2)) by {
      assert forall |t2: TaskId| #![trigger s2.task_logs[t2]]
        s.task_logs.contains_key(t2) && s2.task_logs.contains_key(t2) &&
        s.task_logs[t2].len() < s2.task_logs[t2].len()
        implies el::has_poll_task_for_id_after(s2.executor_log, t2, s.executor_log.len() as int) by {
        assert(t2 == tid);
        assert(el::is_poll_task_for_id_at(s2.executor_log, 14, tid) && 8 <= 14);
      }
    }
    assert(pending_poll_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_pending_for_id_at(s2.executor_log, i, t2) && s2.task_logs.contains_key(t2)
        implies task_log_ends_with_pending(s2.task_logs[t2]) by { texec2_flags(tid, i); }
    }
    assert(new_poll_has_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2)
        implies s2.task_logs.contains_key(t2) by { assert(i == 14 && t2 == tid); }
    }
    assert(new_poll_changes_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2) && s.task_logs.contains_key(t2)
        implies s.task_logs[t2].len() < s2.task_logs[t2].len() by {
        assert(i == 14 && t2 == tid);
        assert(s.task_logs[tid] == ttask_pending() && s2.task_logs[tid] == ttask_ready());
      }
    }
  }
}

proof fn ts1_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ts1(tid)),
{
  bexec1_idx(tid); dreac1_idx();
  use crate::composed::spec::alignment::*;
  let e = bexec1(tid);
  assert(count_park_events_in(e, 8, 8) == 0);
  assert(count_park_events_in(e, 7, 8) == 0) by { bexec1_flags(tid, 7); }
  assert(count_park_events_in(e, 6, 8) == 0) by { bexec1_flags(tid, 6); }
  assert(count_park_events_in(e, 5, 8) == 0) by { bexec1_flags(tid, 5); }
  assert(count_park_events_in(e, 4, 8) == 1) by { bexec1_flags(tid, 4); }
  assert(count_park_events_in(e, 3, 8) == 1) by { bexec1_flags(tid, 3); }
  assert(count_park_events_in(e, 2, 8) == 1) by { bexec1_flags(tid, 2); }
  assert(count_park_events_in(e, 1, 8) == 1) by { bexec1_flags(tid, 1); }
  assert(count_park_events_in(e, 0, 8) == 1) by { bexec1_flags(tid, 0); }
  let r = dreac1();
  assert(count_park_cycles_in(r, 4, 4) == 0);
  assert(count_park_cycles_in(r, 3, 4) == 1) by { dreac1_flags(3); }
  assert(count_park_cycles_in(r, 2, 4) == 1) by { dreac1_flags(2); }
  assert(count_park_cycles_in(r, 1, 4) == 1) by { dreac1_flags(1); }
  assert(count_park_cycles_in(r, 0, 4) == 1) by { dreac1_flags(0); }
}

proof fn ts2_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(ts1(tid), ts2(tid)),
{
  texec2_idx(tid); dreac2_idx();
  use crate::composed::spec::alignment::*;
  let e = texec2(tid);
  assert(count_park_events_in(e, 16, 16) == 0);
  assert(count_park_events_in(e, 15, 16) == 0) by { texec2_flags(tid, 15); }
  assert(count_park_events_in(e, 14, 16) == 0) by { texec2_flags(tid, 14); }
  assert(count_park_events_in(e, 13, 16) == 0) by { texec2_flags(tid, 13); }
  assert(count_park_events_in(e, 12, 16) == 1) by { texec2_flags(tid, 12); }
  assert(count_park_events_in(e, 11, 16) == 1) by { texec2_flags(tid, 11); }
  assert(count_park_events_in(e, 10, 16) == 1) by { texec2_flags(tid, 10); }
  assert(count_park_events_in(e, 9, 16) == 1) by { texec2_flags(tid, 9); }
  assert(count_park_events_in(e, 8, 16) == 1) by { texec2_flags(tid, 8); }
  let r = dreac2();
  assert(count_park_cycles_in(r, 8, 8) == 0);
  assert(count_park_cycles_in(r, 7, 8) == 1) by { dreac2_flags(7); }
  assert(count_park_cycles_in(r, 6, 8) == 1) by { dreac2_flags(6); }
  assert(count_park_cycles_in(r, 5, 8) == 1) by { dreac2_flags(5); }
  assert(count_park_cycles_in(r, 4, 8) == 1) by { dreac2_flags(4); }
}

pub proof fn ts1_cross(tid: TID)
  ensures
    cross_module_alignment(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ts1(tid)),
{
  reveal(cross_module_alignment);
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = ts1(tid);
  bexec1_idx(tid); dreac1_idx(); ttask_idx();
  use crate::composed::spec::alignment::*;
  ts_am_state(s2, tid);
  assert(action_mediation_step(s, s2)) by {
    assert(new_operation_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int|
        is_new_task_operation(s, s2, t2, i) && is_reactor_operation(#[trigger] s2.task_logs[t2][i])
        implies exists |j: int| s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][i]) by { assert(t2 == tid); }
    }
    assert(new_operation_uniqueness(s, s2)) by {
      assert forall |t1: TaskId, t2: TaskId, a1: int, a2: int, ri: int|
        #![trigger s2.task_logs[t1][a1], s2.task_logs[t2][a2], s2.reactor_log[ri]]
        is_new_task_operation(s, s2, t1, a1) && is_new_task_operation(s, s2, t2, a2) &&
        is_reactor_operation(s2.task_logs[t1][a1]) && is_reactor_operation(s2.task_logs[t2][a2]) &&
        s.reactor_log.len() as int <= ri < s2.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(s2.reactor_log[ri], s2.task_logs[t1][a1]) &&
        succ_reactor_event_matches_task_operation(s2.reactor_log[ri], s2.task_logs[t2][a2])
        implies t1 == t2 && a1 == a2 by { assert(t1 == tid); }
    }
    assert(new_op_matches_only_new_reactor(s, s2)) by {
      assert forall |t2: TaskId, ti: int, ri: int|
        is_new_task_operation(s, s2, t2, ti) && is_reactor_operation(#[trigger] s2.task_logs[t2][ti]) &&
        0 <= ri < s2.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(#[trigger] s2.reactor_log[ri], s2.task_logs[t2][ti])
        implies ri >= s.reactor_log.len() by { assert(t2 == tid); }
    }
    assert(reactor_outbound_has_task_operation(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          0 <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by { dreac1_flags(j); }
    }
    assert(new_reactor_event_has_new_op(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          (if s.task_logs.contains_key(t2) { s.task_logs[t2].len() as int } else { 0int })
            <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by { dreac1_flags(j); }
    }
  }
  ts1_obs_consistency(tid);
  ts1_park_alignment(tid);
}

pub proof fn ts2_cross(tid: TID)
  ensures
    cross_module_alignment(ts1(tid), ts2(tid)),
{
  reveal(cross_module_alignment);
  let s = ts1(tid);
  let s2 = ts2(tid);
  texec2_idx(tid); dreac2_idx(); ttask_idx();
  use crate::composed::spec::alignment::*;
  ts_am_state(s2, tid);
  assert(action_mediation_step(s, s2)) by {
    assert(new_operation_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int|
        is_new_task_operation(s, s2, t2, i) && is_reactor_operation(#[trigger] s2.task_logs[t2][i])
        implies exists |j: int| s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][i]) by { assert(t2 == tid); }
    }
    assert(new_operation_uniqueness(s, s2)) by {
      assert forall |t1: TaskId, t2: TaskId, a1: int, a2: int, ri: int|
        #![trigger s2.task_logs[t1][a1], s2.task_logs[t2][a2], s2.reactor_log[ri]]
        is_new_task_operation(s, s2, t1, a1) && is_new_task_operation(s, s2, t2, a2) &&
        is_reactor_operation(s2.task_logs[t1][a1]) && is_reactor_operation(s2.task_logs[t2][a2]) &&
        s.reactor_log.len() as int <= ri < s2.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(s2.reactor_log[ri], s2.task_logs[t1][a1]) &&
        succ_reactor_event_matches_task_operation(s2.reactor_log[ri], s2.task_logs[t2][a2])
        implies t1 == t2 && a1 == a2 by { assert(t1 == tid); }
    }
    assert(new_op_matches_only_new_reactor(s, s2)) by {
      assert forall |t2: TaskId, ti: int, ri: int|
        is_new_task_operation(s, s2, t2, ti) && is_reactor_operation(#[trigger] s2.task_logs[t2][ti]) &&
        0 <= ri < s2.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(#[trigger] s2.reactor_log[ri], s2.task_logs[t2][ti])
        implies ri >= s.reactor_log.len() by { assert(t2 == tid); }
    }
    assert(reactor_outbound_has_task_operation(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          0 <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by { dreac2_flags(j); }
    }
    assert(new_reactor_event_has_new_op(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          (if s.task_logs.contains_key(t2) { s.task_logs[t2].len() as int } else { 0int })
            <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by { dreac2_flags(j); }
    }
  }
  ts2_obs_consistency(tid);
  ts2_park_alignment(tid);
}

// executor/queue env facts.
proof fn t_common_env_facts(s: ComposedState, tid: TID)
  requires
    (s.reactor_log == dreac1() && s.executor_log == bexec1(tid) &&
     s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, ttask_pending()) &&
     s.injection_schedule == bsched(tid)) ||
    (s.reactor_log == dreac2() && s.executor_log == texec2(tid) &&
     s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, ttask_ready()) &&
     s.injection_schedule == bsched(tid)),
    get_max_queue_length(s) >= 1,
  ensures
    el::tid_unique(s.executor_log, tid),
    queue_length_bounded(s),
{
  let is1 = s.executor_log == bexec1(tid);
  bexec1_idx(tid); texec2_idx(tid); ttask_idx();
  let l = s.executor_log;
  assert(el::tid_unique(l, tid)) by {
    assert forall |a: int, b: int| 0 <= a < b < l.len() &&
      el::is_pop_injection_at(l, a) && ee::get_pop_injection_task(l[a]) == Some(crate::executor::spec::types::TaskView { id: tid }) &&
      el::is_pop_injection_at(l, b) && ee::get_pop_injection_task(l[b]) == Some(crate::executor::spec::types::TaskView { id: tid })
      implies false by {
      if is1 { bexec1_flags(tid, a); bexec1_flags(tid, b); } else { texec2_flags(tid, a); texec2_flags(tid, b); }
    }
  }
  if is1 { bexec1_queue_len(tid); } else { texec2_queue_len(tid); }
  assert(queue_length_bounded(s)) by {
    assert forall |i: int|
      #![trigger crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i)]
      0 <= i <= l.len() implies
      crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i).len() <= get_max_queue_length(s) by {
      if is1 { bexec1_queue_len(tid); } else { texec2_queue_len(tid); }
    }
  }
}

proof fn ts1_env(tid: TID)
  requires
    get_max_queue_length(ts1(tid)) >= 1,
  ensures env_N(ts1(tid), tid, 2nat),
{
  let s = ts1(tid);
  bexec1_idx(tid); dreac1_idx(); ttask_idx();
  d_reac_env_facts(s, tid);
  t_common_env_facts(s, tid);
  assert(bounded_poll_count_here_with_bound(s, tid, 2nat)) by { bpoll_count_bexec1(tid); }
  assert(env_holds_at_state_core(s, tid));
  assert(end_to_end_env(s, tid));
  // taskwake_arrival_within: no Drain{TaskWake} after the last poll (@6) — only the
  // TickEnd @7 follows in the 8-event log ⟹ no qualifying d ⟹ antecedent false.
  assert(taskwake_arrival_within(s, tid, 2nat)) by {
    reveal(taskwake_arrival_within);
    crate::composed::proof::end_to_end::last_poll_idx_properties(s.executor_log, tid);
    assert(el::last_poll_idx_for_id(s.executor_log, tid) == 6);
    assert forall |d: int| #![trigger s.executor_log[d]] 6 < d < s.executor_log.len()
      implies !el::is_drain_task_wake_at(s.executor_log, d) by {
      bexec1_idx(tid);
      assert(d == 7);
    }
  }
}

proof fn ts2_env(tid: TID)
  requires
    get_max_queue_length(ts2(tid)) >= 1,
  ensures env_N(ts2(tid), tid, 2nat),
{
  let s = ts2(tid);
  texec2_idx(tid); dreac2_idx(); ttask_idx();
  d_reac_env_facts(s, tid);
  t_common_env_facts(s, tid);
  assert(bounded_poll_count_here_with_bound(s, tid, 2nat)) by {
    assert(el::is_poll_ready_for_id_at(s.executor_log, 14, tid));
    assert(crate::composed::spec::assumptions::task_polled_to_ready(s.executor_log, tid));
  }
  assert(env_holds_at_state_core(s, tid));
  assert(end_to_end_env(s, tid));
  assert(!el::last_poll_is_pending(s.executor_log, tid)) by {
    crate::composed::proof::end_to_end::last_poll_idx_properties(s.executor_log, tid);
    assert(el::is_poll_task_for_id_at(s.executor_log, 14, tid));
    assert(!el::is_poll_pending_for_id_at(s.executor_log, 14, tid));
  }
  crate::composed::proof::assumption_satisfiable::taskwake_arrival_within_vacuous(s, tid, 2nat);
}

pub proof fn ts1_composed_progress(tid: TID)
  ensures
    composed_progress(crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ts1(tid)),
{
  reveal(composed_progress);
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = ts1(tid);
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 0)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 0)); }
  assert(is_extension_of(s, s2));
  bexec1_exec_progress(tid);
  dreac1_reac_progress();
  ts1_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    ttask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(t2 == tid && s2.task_logs[t2] == ttask_pending());
    }
  }
  crate::composed::spec::alignment::monotonic_alignment_holds_no_two_ops(s2);
  ts_am_state(s2, tid);
  crate::composed::proof::inhabitation_goal_wake::bpops_deliver(tid);
  crate::composed::proof::assumption_satisfiable::no_reactor_wake_pending_no_waketask(s);
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2));
  crate::composed::proof::assumption_satisfiable::no_taskwake_pending_no_woken(s);
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2));
  reveal(crate::composed::spec::wake_queues::deferred_drain_step);
  assert(crate::composed::spec::wake_queues::deferred_drain_step(s, s2)) by {
    assert forall |t2: TaskId, d: int|
      crate::composed::spec::wake_queues::in_deferred_queue(s, t2) &&
      s.executor_log.len() as int <= d < s2.executor_log.len() &&
      el::is_drain_deferred_at(s2.executor_log, d)
      implies el::task_id_in_drain_at(s2.executor_log, d, t2) by {
      assert(!s.task_logs.contains_key(t2));
    }
  }
}

pub proof fn ts2_composed_progress(tid: TID)
  ensures
    composed_progress(ts1(tid), ts2(tid)),
{
  reveal(composed_progress);
  let s = ts1(tid);
  let s2 = ts2(tid);
  texec2_idx(tid); dreac2_idx(); ttask_idx(); bexec1_idx(tid);
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 8)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 4)); }
  assert(is_extension_of(s, s2)) by {
    assert(s.task_logs[tid] == ttask_pending() && s2.task_logs[tid] == ttask_ready());
    assert(crate::composed::spec::state::is_task_log_prefix(ttask_pending(), ttask_ready()));
  }
  texec2_exec_progress(tid);
  dreac2_reac_progress();
  ts2_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    ttask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(t2 == tid && s2.task_logs[t2] == ttask_ready());
    }
  }
  crate::composed::spec::alignment::monotonic_alignment_holds_no_two_ops(s2);
  ts_am_state(s2, tid);
  texec2_pops(tid);
  crate::composed::proof::inhabitation_goal_wake::bpops_deliver(tid);
  // reactor_wake vacuous (dreac1 no waketask), deferred vacuous (ttask no defer).
  crate::composed::proof::assumption_satisfiable::no_reactor_wake_pending_no_waketask(s);
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2));
  reveal(crate::composed::spec::wake_queues::deferred_drain_step);
  assert(crate::composed::spec::wake_queues::deferred_drain_step(s, s2)) by {
    assert forall |t2: TaskId, d: int|
      crate::composed::spec::wake_queues::in_deferred_queue(s, t2) &&
      s.executor_log.len() as int <= d < s2.executor_log.len() &&
      el::is_drain_deferred_at(s2.executor_log, d)
      implies el::task_id_in_drain_at(s2.executor_log, d, t2) by {
      // ttask_pending has no Defer ⟹ in_deferred_queue false ⟹ vacuous.
      assert(t2 == tid);
      assert(!crate::utilities::spec::log::has_defer_in_current_poll(
        s.task_logs[tid], (s.task_logs[tid].len() - 1) as int)) by {
        assert(s.task_logs[tid] == ttask_pending());
        assert forall |j: int| #![trigger ttask_pending()[j]] 0 <= j < ttask_pending().len() implies
          !ue::is_defer(ttask_pending()[j]) by { ttask_idx(); }
      }
    }
  }
  // taskwake_drain_step NON-VACUOUS: tid is in the TaskWake queue at ts1 (pending +
  // Woken@2), and the step's Drain{TaskWake}@11 carries [tid].
  assert(crate::composed::spec::wake_queues::taskwake_pending(s, tid)) by {
    reveal(crate::composed::spec::wake_queues::taskwake_pending);
    assert(el::last_poll_is_pending(s.executor_log, tid)) by {
      crate::composed::proof::end_to_end::last_poll_idx_properties(s.executor_log, tid);
      assert(el::is_poll_task_for_id_at(s.executor_log, 6, tid));
      assert(el::is_poll_pending_for_id_at(s.executor_log, 6, tid));
    }
    assert(crate::composed::spec::wake_queues::taskwake_arrival(s, tid)) by {
      reveal(crate::composed::spec::wake_queues::taskwake_arrival);
      ttask_idx();
      assert(s.task_logs.contains_key(tid));
      assert(s.task_logs[tid] == ttask_pending());
      let tl = s.task_logs[tid];
      assert((tl.len() - 1) as int == 3);
      assert(crate::utilities::spec::log::find_last_poll_begin(tl, 0) == 0);
      assert(crate::utilities::spec::log::find_last_poll_begin(tl, 1) == 0);
      assert(crate::utilities::spec::log::find_last_poll_begin(tl, 2) == 0);
      assert(crate::utilities::spec::log::find_last_poll_begin(tl, 3) == 0);
      assert(crate::utilities::spec::log::current_poll_start(tl, 3) == 0);
      assert(crate::utilities::spec::log::in_current_poll_cycle(tl, 2, 3) && ue::is_woken(tl[2]));
      assert(crate::utilities::spec::log::has_woken_in_current_poll(tl, 3));
    }
    assert(!crate::composed::spec::wake_queues::taskwake_drained_after(
      s.executor_log, tid, el::last_poll_idx_for_id(s.executor_log, tid))) by {
      crate::composed::proof::end_to_end::last_poll_idx_properties(s.executor_log, tid);
      assert(el::last_poll_idx_for_id(s.executor_log, tid) == 6);
      assert forall |d: int| 6 < d < s.executor_log.len() implies
        !(el::is_drain_task_wake_at(s.executor_log, d) && el::task_id_in_drain_at(s.executor_log, d, tid)) by {
        bexec1_flags(tid, d);
      }
    }
  }
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2)) by {
    assert forall |t2: TaskId, d: int|
      crate::composed::spec::wake_queues::taskwake_pending(s, t2) &&
      s.executor_log.len() as int <= d < s2.executor_log.len() &&
      el::is_drain_task_wake_at(s2.executor_log, d)
      implies el::task_id_in_drain_at(s2.executor_log, d, t2) by {
      reveal(crate::composed::spec::wake_queues::taskwake_pending);
      assert(t2 == tid);  // only tid has a task log ⟹ only tid can be taskwake_pending
      texec2_flags(tid, d);
      assert(d == 11);
      assert(el::task_id_in_drain_at(s2.executor_log, 11, tid)) by {
        let ids = ee::get_drain_task_ids(s2.executor_log[11]);
        assert(ids =~= seq![tid]);
        assert(ids[0] == tid);
      }
    }
  }
}

// ============================================================================
// Anti-vacuity of the drain-membership arrival clause : tmid is a
// concrete state — texecmid = bexec1 plus the start of a second tick up to a
// Drain{TaskWake}[tid]@11 — where taskwake_arrival_within(tmid, tid, 1)'s
// antecedent HOLDS at d = 11 (pass-waker'd poll Pending @6, one tick-end @7
// elapsed, no earlier post-poll drain took tid) AND the consequent holds: the
// clause is satisfied NON-vacuously. (The trace witness discharges the clause
// vacuously at ts1/ts2 — ts1 has no post-poll Drain{TaskWake}, ts2 is Ready.)
// ============================================================================

pub open spec fn texecmid(tid: TID) -> el::Log {
  bexec1(tid) + seq![
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection { task: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: seq![tid],
    }),
  ]
}

pub open spec fn tmid(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: texecmid(tid),
    reactor_log: dreac1(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, ttask_pending()),
    injection_schedule: bsched(tid),
  }
}

proof fn texecmid_idx(tid: TID)
  ensures
    texecmid(tid).len() == 12,
    forall |k: int| 0 <= k < 8 ==> texecmid(tid)[k] == bexec1(tid)[k],
    texecmid(tid)[8] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    texecmid(tid)[9] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection { task: None }),
    texecmid(tid)[10] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty() }),
    texecmid(tid)[11] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: seq![tid] }),
{
  bexec1_idx(tid);
}

// texecmid poll/drain shape: last poll of tid is the Pending poll @6; the only
// Drain{TaskWake} after it is @11 (and it carries tid); a tick-end (@7) separates them.
#[verifier::rlimit(50)]
proof fn texecmid_poll_drain_facts(tid: TID)
  ensures
    el::last_poll_idx_for_id(texecmid(tid), tid) == 6,
    el::last_poll_is_pending(texecmid(tid), tid),
    el::is_drain_task_wake_at(texecmid(tid), 11),
    el::task_id_in_drain_at(texecmid(tid), 11, tid),
    forall |d: int| #![trigger texecmid(tid)[d]] 6 < d < 11 ==>
      !el::is_drain_task_wake_at(texecmid(tid), d),
    el::count_tick_ends_between(texecmid(tid), 6, 11) >= 1,
{
  let l = texecmid(tid);
  texecmid_idx(tid); bexec1_idx(tid);
  assert(el::is_poll_pending_for_id_at(l, 6, tid));
  assert(el::has_poll_for_id(l, tid));
  crate::composed::proof::end_to_end::last_poll_idx_properties(l, tid);
  let q = el::last_poll_idx_for_id(l, tid);
  assert(q == 6) by {
    if q > 6 {
      assert(el::is_poll_task_for_id_at(l, q, tid));
      if q == 7 {} else if q == 8 {} else if q == 9 {} else if q == 10 {} else { assert(q == 11); }
    } else if q < 6 {
      assert(el::is_poll_task_for_id_at(l, 6, tid));
    }
  }
  assert(el::task_id_in_drain_at(l, 11, tid)) by {
    let ids = ee::get_drain_task_ids(l[11]);
    assert(ids =~= seq![tid]);
    assert(ids[0] == tid);
  }
  assert forall |d: int| #![trigger texecmid(tid)[d]] 6 < d < 11 implies
    !el::is_drain_task_wake_at(texecmid(tid), d) by {
    if d == 7 {} else if d == 8 {} else if d == 9 {} else { assert(d == 10); }
  }
  assert(el::count_tick_ends_between(l, 6, 11) >= 1) by {
    assert(el::is_tick_end_at(l, 7));
    crate::executor::proof::bounded_drain_poll::count_includes_tick_end_at(l, 6, 11, 7);
  }
}

// The task's PassWaker@1 is in the current poll cycle at the last log index (3).
proof fn ttask_pending_pass_waker()
  ensures
    ul::has_pass_waker_in_current_poll(ttask_pending(), 3),
{
  ttask_idx();
  let tl = ttask_pending();
  assert(ul::find_last_poll_begin(tl, 0) == 0);
  assert(ul::find_last_poll_begin(tl, 1) == 0);
  assert(ul::find_last_poll_begin(tl, 2) == 0);
  assert(ul::find_last_poll_begin(tl, 3) == 0);
  assert(ul::current_poll_start(tl, 3) == 0);
  assert(ul::in_current_poll_cycle(tl, 1, 3));
  assert(ue::is_pass_waker(tl[1]));
}

#[verifier::rlimit(50)]
pub proof fn taskwake_arrival_within_nonvacuous_witness(tid: TID)
  ensures
    taskwake_arrival_within(tmid(tid), tid, 1nat),
    // the antecedent is INHABITED at d = 11 ...
    tmid(tid).task_logs.contains_key(tid),
    ul::has_pass_waker_in_current_poll(
      tmid(tid).task_logs[tid], (tmid(tid).task_logs[tid].len() - 1) as int),
    el::last_poll_is_pending(tmid(tid).executor_log, tid),
    el::last_poll_idx_for_id(tmid(tid).executor_log, tid) == 6,
    tmid(tid).executor_log.len() == 12,
    el::is_drain_task_wake_at(tmid(tid).executor_log, 11),
    !crate::composed::spec::wake_queues::taskwake_drained_in(
      tmid(tid).executor_log, tid, 6, 11),
    el::count_tick_ends_between(tmid(tid).executor_log, 6, 11) >= 1nat,
    // ... and the consequent holds there.
    el::task_id_in_drain_at(tmid(tid).executor_log, 11, tid),
{
  let s = tmid(tid);
  let l = s.executor_log;
  texecmid_idx(tid); ttask_idx();
  texecmid_poll_drain_facts(tid);
  ttask_pending_pass_waker();
  assert(s.task_logs[tid] == ttask_pending());
  assert((s.task_logs[tid].len() - 1) as int == 3);
  assert(!crate::composed::spec::wake_queues::taskwake_drained_in(l, tid, 6, 11)) by {
    assert forall |d: int| #![trigger l[d]] 6 < d < 11 implies
      !(el::is_drain_task_wake_at(l, d) && el::task_id_in_drain_at(l, d, tid)) by {}
  }
  assert(taskwake_arrival_within(s, tid, 1nat)) by {
    reveal(taskwake_arrival_within);
    assert forall |d: int| #![trigger s.executor_log[d]]
      6 < d < l.len() && el::is_drain_task_wake_at(l, d)
      implies el::task_id_in_drain_at(l, d, tid) by {
      if d < 11 { assert(!el::is_drain_task_wake_at(l, d)); } else { assert(d == 11); }
    }
  }
}

pub proof fn t_domain_inhabited(tid: TaskId)
  requires
    get_max_queue_length(ts1(tid)) >= 1,
  ensures
    crate::composed::proof::assumption_satisfiable::ete_reachable_N(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ts2(tid), 2nat, 2nat, tid),
    crate::composed::spec::contract::end_to_end_response(ts2(tid), tid),
    !crate::composed::spec::contract::end_to_end_trigger(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), tid),
    !crate::composed::spec::contract::end_to_end_response(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), tid),
{
  let s0 = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s1 = ts1(tid);
  let s2 = ts2(tid);
  texec2_idx(tid);
  assert(get_max_queue_length(s2) == get_max_queue_length(s1));
  assert(get_max_queue_length(s0) == get_max_queue_length(s1));
  crate::composed::proof::inhabitation_goal_wake::bs0_env(tid);
  ts1_env(tid); ts2_env(tid);
  ts1_composed_progress(tid); ts2_composed_progress(tid);
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |x: ComposedState, t2: TaskId| env_N(x, t2, 2nat);
  let trace: Seq<ComposedState> = seq![s0, s1, s2];
  assert(crate::framework::module_spec::is_valid_trace(progress, trace)) by {
    assert forall |i: int| 0 <= i < trace.len() - 1 implies progress(#[trigger] trace[i], trace[i + 1]) by {
      if i == 0 { assert((progress)(s0, s1)); } else { assert(i == 1); assert((progress)(s1, s2)); }
    }
  }
  assert(crate::framework::module_spec::env_holds_along(progress, trace, env, tid)) by {
    assert forall |i: int| 0 <= i < trace.len() implies #[trigger] env(trace[i], tid) by {
      if i == 0 { } else if i == 1 { } else { assert(i == 2); }
    }
  }
  assert(crate::framework::module_spec::env_progress_n(progress, s0, s2, 2nat, env, tid)) by {
    assert(trace.len() == 2nat + 1 && trace.first() == s0 && trace.last() == s2 &&
      crate::framework::module_spec::is_valid_trace(progress, trace) &&
      crate::framework::module_spec::env_holds_along(progress, trace, env, tid));
  }
  assert(crate::composed::spec::contract::end_to_end_response(s2, tid)) by {
    assert(el::is_poll_ready_for_id_at(s2.executor_log, 14, tid));
  }
  assert(!crate::composed::spec::contract::end_to_end_trigger(s0, tid)) by {
    assert forall |i: int| #![trigger s0.executor_log[i]] 0 <= i < s0.executor_log.len() implies false by {}
  }
  assert(!crate::composed::spec::contract::end_to_end_response(s0, tid)) by {
    assert forall |i: int| #![trigger s0.executor_log[i]] 0 <= i < s0.executor_log.len() implies false by {}
  }
}

}
