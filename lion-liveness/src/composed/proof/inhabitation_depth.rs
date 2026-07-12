use vstd::prelude::*;
#[allow(unused_imports)]
use crate::composed::spec::state::*;
#[allow(unused_imports)]
use crate::composed::spec::types::*;
#[allow(unused_imports)]
use crate::composed::spec::progress::*;
#[allow(unused_imports)]
use crate::composed::spec::assumptions::*;
#[allow(unused_imports)]
use crate::composed::spec::alignment::cross_module_alignment;
#[allow(unused_imports)]
use crate::composed::proof::assumption_satisfiable::*;
use crate::executor::spec::events as ee;
use crate::executor::spec::types::TID;
use crate::executor::spec::log as el;
use crate::reactor::spec::events as re;
use crate::reactor::spec::log as rl;
use crate::reactor::spec::types::{IoResultView, ResourceIdView};
use crate::utilities::spec::events as ue;
use crate::utilities::spec::log as ul;

verus! {

// ============================================================================
// Non-vacuity witness for the DEPTH-GENERALIZED trigger :
// tid sits at schedule depth 1 (schedule [qother, tid], length 2) and a real
// env_N-good 2-step trace delivers BOTH tasks in schedule order and polls tid
// to Ready — so `task_scheduled_at(·, tid, 1)`'s theorem domain is inhabited by
// an execution in which tid is genuinely NOT the head of the injection queue.
//
// Tick 1: Pop(Some qother) → poll qother Ready.   Tick 2: Pop(Some tid) → poll
// tid Ready. No timers/io/wakers — the reactor contributes two idle park
// rounds; both task logs are the minimal immediate-Ready [PollBegin,
// PollEnd(Ready)].
// ============================================================================

pub open spec fn qother(tid: TID) -> TID { (tid + 1) as nat }

pub open spec fn qsched(tid: TID) -> Seq<crate::executor::spec::types::TaskView> {
  seq![
    crate::executor::spec::types::TaskView { id: qother(tid) },
    crate::executor::spec::types::TaskView { id: tid },
  ]
}

// --- Executor log: tick 1 (pop qother, poll Ready) ---
pub open spec fn qexec1(tid: TID) -> el::Log {
  seq![
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection {
      task: Some(crate::executor::spec::types::TaskView { id: qother(tid) }),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: qother(tid), task: None,
      result: crate::executor::spec::types::PollResult::Ready(()),
    }),
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
  ]
}

// --- Executor log: tick 1 + tick 2 (pop tid, poll Ready) ---
pub open spec fn qexec2(tid: TID) -> el::Log {
  qexec1(tid) + seq![
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection {
      task: Some(crate::executor::spec::types::TaskView { id: tid }),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: tid, task: None,
      result: crate::executor::spec::types::PollResult::Ready(()),
    }),
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
  ]
}

// --- Reactor log: one idle park round (clock 1), two idle park rounds (1, 2) ---
pub open spec fn qreac1() -> rl::Log {
  seq![
    re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 1int }),
    re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat),
    }),
    re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())),
    }),
  ]
}

pub open spec fn qreac2() -> rl::Log {
  qreac1() + seq![
    re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 2int }),
    re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat),
    }),
    re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())),
    }),
  ]
}

// --- Task log: immediate Ready on the first poll ---
pub open spec fn qtask_ready() -> ul::Log {
  seq![
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll {
      result: Some(ue::PollResult::Ready),
    }),
  ]
}

pub open spec fn qs0(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: Seq::empty(),
    reactor_log: Seq::empty(),
    task_logs: Map::empty(),
    injection_schedule: qsched(tid),
  }
}

pub open spec fn qs1(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: qexec1(tid),
    reactor_log: qreac1(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(qother(tid), qtask_ready()),
    injection_schedule: qsched(tid),
  }
}

pub open spec fn qs2(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: qexec2(tid),
    reactor_log: qreac2(),
    task_logs: Map::<TaskId, ul::Log>::empty()
      .insert(qother(tid), qtask_ready()).insert(tid, qtask_ready()),
    injection_schedule: qsched(tid),
  }
}

// ============================================================================
// Index lemmas
// ============================================================================

pub proof fn qexec1_idx(tid: TID)
  ensures
    qexec1(tid).len() == 8,
    qexec1(tid)[0] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    qexec1(tid)[1] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection {
      task: Some(crate::executor::spec::types::TaskView { id: qother(tid) }) }),
    qexec1(tid)[2] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty() }),
    qexec1(tid)[3] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: Seq::<TID>::empty() }),
    qexec1(tid)[4] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    qexec1(tid)[5] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: Seq::<TID>::empty() }),
    qexec1(tid)[6] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: qother(tid), task: None,
      result: crate::executor::spec::types::PollResult::Ready(()) }),
    qexec1(tid)[7] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
{
}

pub proof fn qexec2_idx(tid: TID)
  ensures
    qexec2(tid).len() == 16,
    forall |j: int| 0 <= j < 8 ==> qexec2(tid)[j] == qexec1(tid)[j],
    qexec2(tid)[8] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    qexec2(tid)[9] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection {
      task: Some(crate::executor::spec::types::TaskView { id: tid }) }),
    qexec2(tid)[10] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty() }),
    qexec2(tid)[11] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: Seq::<TID>::empty() }),
    qexec2(tid)[12] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    qexec2(tid)[13] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: Seq::<TID>::empty() }),
    qexec2(tid)[14] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: tid, task: None,
      result: crate::executor::spec::types::PollResult::Ready(()) }),
    qexec2(tid)[15] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
{
  qexec1_idx(tid);
}

pub proof fn qreac1_idx()
  ensures
    qreac1().len() == 4,
    qreac1()[0] == re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    qreac1()[1] == re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 1int }),
    qreac1()[2] == re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat) }),
    qreac1()[3] == re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())) }),
{
}

pub proof fn qreac2_idx()
  ensures
    qreac2().len() == 8,
    forall |j: int| 0 <= j < 4 ==> qreac2()[j] == qreac1()[j],
    qreac2()[4] == re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    qreac2()[5] == re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 2int }),
    qreac2()[6] == re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat) }),
    qreac2()[7] == re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())) }),
{
  qreac1_idx();
}

pub proof fn qtask_idx()
  ensures
    qtask_ready().len() == 2,
    qtask_ready()[0] == ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    qtask_ready()[1] == ue::UtilityEvent::Inbound(ue::InboundCall::Poll {
      result: Some(ue::PollResult::Ready) }),
{
}

// ============================================================================
// Per-index flags
// ============================================================================

pub proof fn qreac1_flags(j: int)
  ensures
    !rl::is_succ_register_timer_at(qreac1(), j),
    !rl::is_deregister_timer_at(qreac1(), j),
    !rl::io_syscall_registered_at(qreac1(), j),
    !rl::io_syscall_register_at(qreac1(), j),
    !rl::io_syscall_deregistered_at(qreac1(), j),
    !rl::is_succ_set_waker_at(qreac1(), j),
    !rl::is_set_waker_at(qreac1(), j),
    !rl::is_wake_task_at(qreac1(), j),
    !rl::is_io_event_ready_at(qreac1(), j),
    !crate::reactor::invariants::inbound_register_io_result::is_inbound_register_io_end_at(qreac1(), j),
    !crate::reactor::invariants::inbound_deregister_io_result::is_inbound_deregister_io_end_at(qreac1(), j),
    j != 0 ==> !rl::is_park_begin_at(qreac1(), j),
    j != 3 ==> !rl::is_park_end_at(qreac1(), j),
    j != 1 ==> !rl::is_get_current_time_at(qreac1(), j),
    (0 <= j < 4) ==> !crate::composed::spec::alignment::is_task_initiated_reactor_event(qreac1()[j]),
{
  qreac1_idx();
  if j == 0 {
  } else if j == 1 {
  } else if j == 2 {
  } else if j == 3 {
  } else {
  }
}

pub proof fn qreac2_flags(j: int)
  ensures
    !rl::is_succ_register_timer_at(qreac2(), j),
    !rl::is_deregister_timer_at(qreac2(), j),
    !rl::io_syscall_registered_at(qreac2(), j),
    !rl::io_syscall_register_at(qreac2(), j),
    !rl::io_syscall_deregistered_at(qreac2(), j),
    !rl::is_succ_set_waker_at(qreac2(), j),
    !rl::is_set_waker_at(qreac2(), j),
    !rl::is_wake_task_at(qreac2(), j),
    !rl::is_io_event_ready_at(qreac2(), j),
    !crate::reactor::invariants::inbound_register_io_result::is_inbound_register_io_end_at(qreac2(), j),
    !crate::reactor::invariants::inbound_deregister_io_result::is_inbound_deregister_io_end_at(qreac2(), j),
    (j != 0 && j != 4) ==> !rl::is_park_begin_at(qreac2(), j),
    (j != 3 && j != 7) ==> !rl::is_park_end_at(qreac2(), j),
    (j != 1 && j != 5) ==> !rl::is_get_current_time_at(qreac2(), j),
    (0 <= j < 8) ==> !crate::composed::spec::alignment::is_task_initiated_reactor_event(qreac2()[j]),
{
  qreac2_idx();
  qreac1_idx();
  if 0 <= j < 4 {
    assert(qreac2()[j] == qreac1()[j]);
    qreac1_flags(j);
  } else if j == 4 {
  } else if j == 5 {
  } else if j == 6 {
  } else if j == 7 {
  } else {
  }
}

pub proof fn qexec1_flags(tid: TID, k: int)
  ensures
    k != 0 ==> !el::is_tick_begin_at(qexec1(tid), k),
    k != 7 ==> !el::is_tick_end_at(qexec1(tid), k),
    k != 4 ==> !el::is_park_at(qexec1(tid), k),
    k != 1 ==> !el::is_pop_injection_at(qexec1(tid), k),
    k != 6 ==> !el::is_poll_task_at(qexec1(tid), k),
{
  qexec1_idx(tid);
}

pub proof fn qexec2_flags(tid: TID, k: int)
  ensures
    (k != 0 && k != 8) ==> !el::is_tick_begin_at(qexec2(tid), k),
    (k != 7 && k != 15) ==> !el::is_tick_end_at(qexec2(tid), k),
    (k != 4 && k != 12) ==> !el::is_park_at(qexec2(tid), k),
    (k != 1 && k != 9) ==> !el::is_pop_injection_at(qexec2(tid), k),
    (k != 6 && k != 14) ==> !el::is_poll_task_at(qexec2(tid), k),
{
  qexec2_idx(tid);
  if 0 <= k < 8 { qexec1_idx(tid); }
}

// ============================================================================
// FIFO queue evolution
// ============================================================================

// pop Some(qother)@1 pushes; poll@6 removes (→ empty); pop Some(tid)@9 pushes;
// poll@14 removes.
pub proof fn qexec1_queue(tid: TID)
  ensures
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec1(tid), 0) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec1(tid), 6) =~= seq![qother(tid)],
    forall |i: int| 2 <= i <= 6 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec1(tid), i) =~= seq![qother(tid)],
    forall |i: int| (i == 0 || i == 1 || i == 7 || i == 8) ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec1(tid), i) =~= Seq::<TID>::empty(),
{
  let l = qexec1(tid);
  qexec1_idx(tid);
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  assert(fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 1) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 2) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 3) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 4) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 5) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 6) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 7) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 8) =~= Seq::<TID>::empty());
  assert forall |i: int| 2 <= i <= 6 implies #[trigger] fifo_queue_at(l, i) =~= seq![qother(tid)] by {
    if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {}
  }
  assert forall |i: int| (i == 0 || i == 1 || i == 7 || i == 8) implies
    #[trigger] fifo_queue_at(l, i) =~= Seq::<TID>::empty() by {
    if i == 0 {} else if i == 1 {} else if i == 7 {} else if i == 8 {}
  }
}

pub proof fn qexec2_queue(tid: TID)
  ensures
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec2(tid), 0) =~= Seq::<TID>::empty(),
    forall |i: int| 2 <= i <= 6 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec2(tid), i) =~= seq![qother(tid)],
    forall |i: int| (i == 0 || i == 1 || i == 7 || i == 8 || i == 9) ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec2(tid), i) =~= Seq::<TID>::empty(),
    forall |i: int| 10 <= i <= 14 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec2(tid), i) =~= seq![tid],
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec2(tid), 15) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(qexec2(tid), 16) =~= Seq::<TID>::empty(),
{
  let l = qexec2(tid);
  qexec2_idx(tid);
  qexec1_idx(tid);
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  assert(fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 1) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 2) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 3) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 4) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 5) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 6) =~= seq![qother(tid)]);
  assert(fifo_queue_at(l, 7) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 8) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 9) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 10) =~= seq![tid]);
  assert(fifo_queue_at(l, 11) =~= seq![tid]);
  assert(fifo_queue_at(l, 12) =~= seq![tid]);
  assert(fifo_queue_at(l, 13) =~= seq![tid]);
  assert(fifo_queue_at(l, 14) =~= seq![tid]);
  assert(fifo_queue_at(l, 15) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 16) =~= Seq::<TID>::empty());
  assert forall |i: int| 2 <= i <= 6 implies #[trigger] fifo_queue_at(l, i) =~= seq![qother(tid)] by {
    if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {}
  }
  assert forall |i: int| (i == 0 || i == 1 || i == 7 || i == 8 || i == 9) implies
    #[trigger] fifo_queue_at(l, i) =~= Seq::<TID>::empty() by {
    if i == 0 {} else if i == 1 {} else if i == 7 {} else if i == 8 {} else if i == 9 {}
  }
  assert forall |i: int| 10 <= i <= 14 implies #[trigger] fifo_queue_at(l, i) =~= seq![tid] by {
    if i == 10 {} else if i == 11 {} else if i == 12 {} else if i == 13 {} else if i == 14 {}
  }
}

// ============================================================================
// Executor invariant + progress
// ============================================================================

proof fn qexec1_tick_structure(tid: TID)
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_park::tick_has_park(), qexec1(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection(), qexec1(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred(), qexec1(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake(), qexec1(tid)),
{
  let l = qexec1(tid);
  qexec1_idx(tid);
  let pk = crate::executor::invariants::tick_has_park::tick_has_park();
  assert(crate::framework::action_safety::action_safety_satisfied(pk, l)) by {
    assert forall |i: int| #[trigger] (pk.acceptance)(l, i) implies (pk.validity)(l, i) by {
      qexec1_flags(tid, i);
      if i == 7 { assert(el::is_park_at(l, 4)); assert forall |k: int| 4 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec1_flags(tid, k); } }
    } }
  let pp = crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection();
  assert(crate::framework::action_safety::action_safety_satisfied(pp, l)) by {
    assert forall |i: int| #[trigger] (pp.acceptance)(l, i) implies (pp.validity)(l, i) by {
      qexec1_flags(tid, i);
      if i == 7 { assert(el::is_pop_injection_at(l, 1)); assert forall |k: int| 1 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec1_flags(tid, k); } }
    } }
  let dd = crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred();
  assert(crate::framework::action_safety::action_safety_satisfied(dd, l)) by {
    assert forall |i: int| #[trigger] (dd.acceptance)(l, i) implies (dd.validity)(l, i) by {
      qexec1_flags(tid, i);
      if i == 7 { assert(el::is_drain_deferred_at(l, 2)); assert forall |k: int| 2 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec1_flags(tid, k); } }
    } }
  let dt = crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake();
  assert(crate::framework::action_safety::action_safety_satisfied(dt, l)) by {
    assert forall |i: int| #[trigger] (dt.acceptance)(l, i) implies (dt.validity)(l, i) by {
      qexec1_flags(tid, i);
      if i == 7 { assert(el::is_drain_task_wake_at(l, 3)); assert forall |k: int| 3 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec1_flags(tid, k); } }
    } }
}

#[verifier::rlimit(100)]
proof fn qexec1_exec_inv(tid: TID)
  ensures
    crate::executor::invariants::executor_inv(qexec1(tid)),
{
  let l = qexec1(tid);
  qexec1_idx(tid);
  qexec1_queue(tid);
  let p_fifo = crate::executor::invariants::fifo_task_selection::fifo_task_selection();
  assert(crate::framework::action_safety::action_safety_satisfied(p_fifo, l)) by {
    assert forall |i: int| #[trigger] (p_fifo.acceptance)(l, i) implies (p_fifo.validity)(l, i) by {
      qexec1_flags(tid, i);
      if i == 6 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 6, qother(tid))); }
    }
  }
  let p_vtp = crate::executor::invariants::valid_task_polling::valid_task_polling();
  assert(crate::framework::action_safety::action_safety_satisfied(p_vtp, l)) by {
    assert forall |i: int| #[trigger] (p_vtp.acceptance)(l, i) implies (p_vtp.validity)(l, i) by {
      qexec1_flags(tid, i);
      if i == 6 {
        assert(el::is_pop_injection_at(l, 1) && ee::get_pop_injection_task(l[1]).unwrap().id == qother(tid));
        assert(crate::executor::invariants::valid_task_polling::tid_was_injected_before(l, 6, qother(tid)));
        assert(!crate::executor::invariants::valid_task_polling::tid_returned_ready_before(l, 6, qother(tid))) by {
          assert forall |j: int| 0 <= j < 6 implies
            !(el::is_poll_task_at(l, j) && ee::get_poll_task_id(l[j]) == qother(tid)
              && ee::get_poll_result(l[j]) == crate::executor::spec::types::PollResult::Ready(())) by { qexec1_flags(tid, j); }
        }
        assert(!crate::executor::invariants::valid_task_polling::tid_is_invalid(l, 6, qother(tid)));
      }
    }
  }
  qexec1_tick_structure(tid);
  let p_pdrw = crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_pdrw, l)) by {
    assert forall |i: int| #[trigger] (p_pdrw.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_pdrw.fulfillment)(l, i, j)]
        j > i && (p_pdrw.fulfillment)(l, i, j) && (p_pdrw.timely)(l, i, j) by {
      qexec1_flags(tid, i);
      if i == 4 {
        assert(el::is_drain_reactor_wake_at(l, 5));
        assert forall |k: int| 4 < k < 5 implies !#[trigger] el::is_tick_end_at(l, k) by { qexec1_flags(tid, k); }
        assert(5 > 4 && (p_pdrw.fulfillment)(l, 4, 5) && (p_pdrw.timely)(l, 4, 5));
      }
    }
  }
  let p_tpr = crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_tpr, l)) by {
    assert forall |i: int| #[trigger] (p_tpr.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_tpr.fulfillment)(l, i, j)]
        j > i && (p_tpr.fulfillment)(l, i, j) && (p_tpr.timely)(l, i, j) by {
      qexec1_flags(tid, i);
      if i == 0 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
      }
    }
  }
}

pub proof fn qexec1_exec_progress(tid: TID)
  ensures
    crate::executor::executor_progress(Seq::<ee::ExecutorEvent>::empty(), qexec1(tid)),
{
  let l = qexec1(tid);
  qexec1_idx(tid);
  qexec1_exec_inv(tid);
  assert(Seq::<ee::ExecutorEvent>::empty() =~= l.subrange(0, 0));
  assert(crate::executor::is_complete_tick_cycle(l, 0, 8)) by {
    assert(el::is_tick_begin_at(l, 0));
    assert(el::is_tick_end_at(l, 7));
    assert forall |k: int| 0 < k < 7 implies
      !#[trigger] el::is_tick_begin_at(l, k) && !el::is_tick_end_at(l, k) by { qexec1_flags(tid, k); }
  }
}

proof fn qexec2_tick_structure(tid: TID)
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_park::tick_has_park(), qexec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection(), qexec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred(), qexec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake(), qexec2(tid)),
{
  let l = qexec2(tid);
  qexec2_idx(tid);
  let pk = crate::executor::invariants::tick_has_park::tick_has_park();
  assert(crate::framework::action_safety::action_safety_satisfied(pk, l)) by {
    assert forall |i: int| #[trigger] (pk.acceptance)(l, i) implies (pk.validity)(l, i) by {
      qexec2_flags(tid, i);
      if i == 7 { assert(el::is_park_at(l, 4)); assert forall |k: int| 4 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_park_at(l, 12)); assert forall |k: int| 12 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec2_flags(tid, k); } }
    } }
  let pp = crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection();
  assert(crate::framework::action_safety::action_safety_satisfied(pp, l)) by {
    assert forall |i: int| #[trigger] (pp.acceptance)(l, i) implies (pp.validity)(l, i) by {
      qexec2_flags(tid, i);
      if i == 7 { assert(el::is_pop_injection_at(l, 1)); assert forall |k: int| 1 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_pop_injection_at(l, 9)); assert forall |k: int| 9 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec2_flags(tid, k); } }
    } }
  let dd = crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred();
  assert(crate::framework::action_safety::action_safety_satisfied(dd, l)) by {
    assert forall |i: int| #[trigger] (dd.acceptance)(l, i) implies (dd.validity)(l, i) by {
      qexec2_flags(tid, i);
      if i == 7 { assert(el::is_drain_deferred_at(l, 2)); assert forall |k: int| 2 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_drain_deferred_at(l, 10)); assert forall |k: int| 10 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec2_flags(tid, k); } }
    } }
  let dt = crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake();
  assert(crate::framework::action_safety::action_safety_satisfied(dt, l)) by {
    assert forall |i: int| #[trigger] (dt.acceptance)(l, i) implies (dt.validity)(l, i) by {
      qexec2_flags(tid, i);
      if i == 7 { assert(el::is_drain_task_wake_at(l, 3)); assert forall |k: int| 3 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_drain_task_wake_at(l, 11)); assert forall |k: int| 11 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { qexec2_flags(tid, k); } }
    } }
}

#[verifier::rlimit(100)]
pub proof fn qexec2_exec_inv(tid: TID)
  ensures
    crate::executor::invariants::executor_inv(qexec2(tid)),
{
  let l = qexec2(tid);
  qexec2_idx(tid);
  qexec2_queue(tid);
  let p_fifo = crate::executor::invariants::fifo_task_selection::fifo_task_selection();
  assert(crate::framework::action_safety::action_safety_satisfied(p_fifo, l)) by {
    assert forall |i: int| #[trigger] (p_fifo.acceptance)(l, i) implies (p_fifo.validity)(l, i) by {
      qexec2_flags(tid, i);
      if i == 6 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 6, qother(tid))); }
      else if i == 14 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 14, tid)); }
    }
  }
  let p_vtp = crate::executor::invariants::valid_task_polling::valid_task_polling();
  assert(crate::framework::action_safety::action_safety_satisfied(p_vtp, l)) by {
    assert forall |i: int| #[trigger] (p_vtp.acceptance)(l, i) implies (p_vtp.validity)(l, i) by {
      qexec2_flags(tid, i);
      if i == 6 {
        assert(el::is_pop_injection_at(l, 1) && ee::get_pop_injection_task(l[1]).unwrap().id == qother(tid));
        assert(crate::executor::invariants::valid_task_polling::tid_was_injected_before(l, 6, qother(tid)));
        assert(!crate::executor::invariants::valid_task_polling::tid_returned_ready_before(l, 6, qother(tid))) by {
          assert forall |j: int| 0 <= j < 6 implies
            !(el::is_poll_task_at(l, j) && ee::get_poll_task_id(l[j]) == qother(tid)
              && ee::get_poll_result(l[j]) == crate::executor::spec::types::PollResult::Ready(())) by { qexec2_flags(tid, j); }
        }
        assert(!crate::executor::invariants::valid_task_polling::tid_is_invalid(l, 6, qother(tid)));
      } else if i == 14 {
        assert(el::is_pop_injection_at(l, 9) && ee::get_pop_injection_task(l[9]).unwrap().id == tid);
        assert(crate::executor::invariants::valid_task_polling::tid_was_injected_before(l, 14, tid));
        assert(!crate::executor::invariants::valid_task_polling::tid_returned_ready_before(l, 14, tid)) by {
          assert forall |j: int| 0 <= j < 14 implies
            !(el::is_poll_task_at(l, j) && ee::get_poll_task_id(l[j]) == tid
              && ee::get_poll_result(l[j]) == crate::executor::spec::types::PollResult::Ready(())) by {
            qexec2_flags(tid, j);
            if j == 6 { assert(ee::get_poll_task_id(l[6]) == qother(tid) && qother(tid) != tid); }
          }
        }
        assert(!crate::executor::invariants::valid_task_polling::tid_is_invalid(l, 14, tid));
      }
    }
  }
  qexec2_tick_structure(tid);
  let p_pdrw = crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_pdrw, l)) by {
    assert forall |i: int| #[trigger] (p_pdrw.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_pdrw.fulfillment)(l, i, j)]
        j > i && (p_pdrw.fulfillment)(l, i, j) && (p_pdrw.timely)(l, i, j) by {
      qexec2_flags(tid, i);
      if i == 4 {
        assert(el::is_drain_reactor_wake_at(l, 5));
        assert forall |k: int| 4 < k < 5 implies !#[trigger] el::is_tick_end_at(l, k) by { qexec2_flags(tid, k); }
        assert(5 > 4 && (p_pdrw.fulfillment)(l, 4, 5) && (p_pdrw.timely)(l, 4, 5));
      } else if i == 12 {
        assert(el::is_drain_reactor_wake_at(l, 13));
        assert forall |k: int| 12 < k < 13 implies !#[trigger] el::is_tick_end_at(l, k) by { qexec2_flags(tid, k); }
        assert(13 > 12 && (p_pdrw.fulfillment)(l, 12, 13) && (p_pdrw.timely)(l, 12, 13));
      }
    }
  }
  let p_tpr = crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_tpr, l)) by {
    assert forall |i: int| #[trigger] (p_tpr.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_tpr.fulfillment)(l, i, j)]
        j > i && (p_tpr.fulfillment)(l, i, j) && (p_tpr.timely)(l, i, j) by {
      qexec2_flags(tid, i);
      if i == 0 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
      } else if i == 8 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 8) =~= Seq::<TID>::empty());
      }
    }
  }
}

pub proof fn qexec2_exec_progress(tid: TID)
  ensures
    crate::executor::executor_progress(qexec1(tid), qexec2(tid)),
{
  let l1 = qexec1(tid);
  let l2 = qexec2(tid);
  qexec2_idx(tid);
  qexec2_exec_inv(tid);
  assert(l1 =~= l2.subrange(0, 8));
  assert(crate::executor::is_complete_tick_cycle(l2, 8, 16)) by {
    assert(el::is_tick_begin_at(l2, 8));
    assert(el::is_tick_end_at(l2, 15));
    assert forall |k: int| 8 < k < 15 implies
      !#[trigger] el::is_tick_begin_at(l2, k) && !el::is_tick_end_at(l2, k) by { qexec2_flags(tid, k); }
  }
}

// ============================================================================
// Reactor invariant + progress (two idle park rounds)
// ============================================================================

// All timer/io/wake action-safety families are vacuous (no such events at all).
#[verifier::rlimit(50)]
proof fn qreac_vacuous_as(l: rl::Log)
  requires l == qreac1() || l == qreac2(),
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_deadline_future::timer_deadline_future(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_ready_in_park::io_ready_in_park(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_waker_validity::timer_waker_validity(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_waker_validity::io_waker_validity(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::wake_has_registration::wake_has_registration(), l),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::set_waker_active_io::set_waker_active_io(), l),
{
  let p1 = crate::reactor::invariants::timer_deadline_future::timer_deadline_future();
  assert(crate::framework::action_safety::action_safety_satisfied(p1, l)) by {
    assert forall |i: int| #[trigger] (p1.acceptance)(l, i) implies (p1.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p2 = crate::reactor::invariants::io_ready_in_park::io_ready_in_park();
  assert(crate::framework::action_safety::action_safety_satisfied(p2, l)) by {
    assert forall |i: int| #[trigger] (p2.acceptance)(l, i) implies (p2.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p3 = crate::reactor::invariants::timer_waker_validity::timer_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p3, l)) by {
    assert forall |i: int| #[trigger] (p3.acceptance)(l, i) implies (p3.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p4 = crate::reactor::invariants::io_waker_validity::io_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p4, l)) by {
    assert forall |i: int| #[trigger] (p4.acceptance)(l, i) implies (p4.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p5 = crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p5, l)) by {
    assert forall |i: int| #[trigger] (p5.acceptance)(l, i) implies (p5.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p6 = crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p6, l)) by {
    assert forall |i: int| #[trigger] (p6.acceptance)(l, i) implies (p6.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p7 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer();
  assert(crate::framework::action_safety::action_safety_satisfied(p7, l)) by {
    assert forall |i: int| #[trigger] (p7.acceptance)(l, i) implies (p7.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p8 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p8, l)) by {
    assert forall |i: int| #[trigger] (p8.acceptance)(l, i) implies (p8.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p9 = crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p9, l)) by {
    assert forall |i: int| #[trigger] (p9.acceptance)(l, i) implies (p9.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p10 = crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p10, l)) by {
    assert forall |i: int| #[trigger] (p10.acceptance)(l, i) implies (p10.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p11 = crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p11, l)) by {
    assert forall |i: int| #[trigger] (p11.acceptance)(l, i) implies (p11.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p12 = crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p12, l)) by {
    assert forall |i: int| #[trigger] (p12.acceptance)(l, i) implies (p12.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p13 = crate::reactor::invariants::wake_has_registration::wake_has_registration();
  assert(crate::framework::action_safety::action_safety_satisfied(p13, l)) by {
    assert forall |i: int| #[trigger] (p13.acceptance)(l, i) implies (p13.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let p14 = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p14, l)) by {
    assert forall |i: int| #[trigger] (p14.acceptance)(l, i) implies (p14.validity)(l, i) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
}

#[verifier::rlimit(50)]
proof fn qreac_vacuous_ll(l: rl::Log)
  requires l == qreac1() || l == qreac2(),
  ensures
    crate::reactor::invariants::reactor_local_liveness_inv(l),
{
  let q1 = crate::reactor::invariants::wake_on_expired::wake_on_expired();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q1, l)) by {
    assert forall |i: int| #[trigger] (q1.acceptance)(l, i) implies
      exists |j: int| #![trigger (q1.fulfillment)(l, i, j)]
        j > i && (q1.fulfillment)(l, i, j) && (q1.timely)(l, i, j) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let q2 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_readable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q2, l)) by {
    assert forall |i: int| #[trigger] (q2.acceptance)(l, i) implies
      exists |j: int| #![trigger (q2.fulfillment)(l, i, j)]
        j > i && (q2.fulfillment)(l, i, j) && (q2.timely)(l, i, j) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
  let q3 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_writable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q3, l)) by {
    assert forall |i: int| #[trigger] (q3.acceptance)(l, i) implies
      exists |j: int| #![trigger (q3.fulfillment)(l, i, j)]
        j > i && (q3.fulfillment)(l, i, j) && (q3.timely)(l, i, j) by {
      if l == qreac1() { qreac1_flags(i); } else { qreac2_flags(i); } } }
}

pub proof fn qreac1_reac_inv()
  ensures
    crate::reactor::invariants::reactor_inv(qreac1()),
{
  let l = qreac1();
  qreac1_idx();
  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      qreac1_flags(i);
      if i == 3 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(rl::is_get_current_time_at(l, 1));
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 3));
      }
    }
  }
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      qreac1_flags(i);
      if i == 3 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 3, 3) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 2, 3) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 1, 3) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 0, 3) == 1);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, 3));
      }
    }
  }
  qreac_vacuous_as(l);
  qreac_vacuous_ll(l);
}

pub proof fn qreac2_reac_inv()
  ensures
    crate::reactor::invariants::reactor_inv(qreac2()),
{
  let l = qreac2();
  qreac2_idx();
  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      qreac2_flags(i);
      if i == 3 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(rl::is_get_current_time_at(l, 1));
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 3));
      } else if i == 7 {
        assert(rl::current_park_start(l, 5) == 4);
        assert(rl::current_park_start(l, 6) == 4);
        assert(rl::current_park_start(l, 7) == 4);
        assert(rl::is_get_current_time_at(l, 5));
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 7));
      }
    }
  }
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      qreac2_flags(i);
      if i == 3 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 3, 3) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 2, 3) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 1, 3) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 0, 3) == 1);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, 3));
      } else if i == 7 {
        assert(rl::current_park_start(l, 5) == 4);
        assert(rl::current_park_start(l, 6) == 4);
        assert(rl::current_park_start(l, 7) == 4);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 7, 7) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 6, 7) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 5, 7) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 4, 7) == 1);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, 7));
      }
    }
  }
  qreac_vacuous_as(l);
  qreac_vacuous_ll(l);
}

pub proof fn qreac1_reac_progress()
  ensures
    crate::reactor::reactor_progress(Seq::<re::ReactorEvent>::empty(), qreac1()),
{
  let l = qreac1();
  qreac1_idx();
  qreac1_reac_inv();
  assert(Seq::<re::ReactorEvent>::empty() =~= l.subrange(0, 0));
  assert(crate::reactor::is_complete_park_cycle(l, 0, 4)) by {
    assert(rl::is_park_begin_at(l, 0));
    assert(rl::is_park_end_at(l, 3));
    assert forall |k: int| 0 < k < 3 implies
      !#[trigger] rl::is_park_begin_at(l, k) && !rl::is_park_end_at(l, k) by { qreac1_flags(k); }
  }
  assert(exists |ps: int, pe: int|
    0 <= ps && ps < pe && pe <= l.len() &&
    crate::reactor::is_complete_park_cycle(l, ps, pe) &&
    (forall |i: int| 0 <= i < ps ==> re::is_inbound_non_park(#[trigger] l[i])) &&
    (forall |i: int| pe <= i < l.len() ==> re::is_inbound_non_park(#[trigger] l[i]))) by {
    assert(crate::reactor::is_complete_park_cycle(l, 0, 4));
  }
}

pub proof fn qreac2_reac_progress()
  ensures
    crate::reactor::reactor_progress(qreac1(), qreac2()),
{
  let l1 = qreac1();
  let l2 = qreac2();
  qreac2_idx();
  qreac1_idx();
  qreac2_reac_inv();
  assert(l1 =~= l2.subrange(0, 4));
  assert(crate::reactor::is_complete_park_cycle(l2, 4, 8)) by {
    assert(rl::is_park_begin_at(l2, 4));
    assert(rl::is_park_end_at(l2, 7));
    assert forall |k: int| 4 < k < 7 implies
      !#[trigger] rl::is_park_begin_at(l2, k) && !rl::is_park_end_at(l2, k) by { qreac2_flags(k); }
  }
  assert(exists |ps: int, pe: int|
    4 <= ps && ps < pe && pe <= l2.len() &&
    crate::reactor::is_complete_park_cycle(l2, ps, pe) &&
    (forall |i: int| 4 <= i < ps ==> re::is_inbound_non_park(#[trigger] l2[i])) &&
    (forall |i: int| pe <= i < l2.len() ==> re::is_inbound_non_park(#[trigger] l2[i]))) by {
    assert(crate::reactor::is_complete_park_cycle(l2, 4, 8));
  }
}

// ============================================================================
// utilities_inv, task-op facts
// ============================================================================

// qtask_ready has no PollEnd(Pending) and no resource operations, so both
// utility action-safety families are vacuous.
pub proof fn qtask_utilities_inv()
  ensures
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(qtask_ready()),
{
  qtask_idx();
  use crate::utilities::invariants::wakeup_guarantee::*;
  let wg = wakeup_guarantee();
  let ro = crate::utilities::invariants::resource_ownership::resource_ownership();
  assert(crate::framework::action_safety::action_safety_satisfied(wg, qtask_ready())) by {
    assert forall |i: int| #[trigger] (wg.acceptance)(qtask_ready(), i) implies (wg.validity)(qtask_ready(), i) by {
      if i == 0 {} else if i == 1 {}
    }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(ro, qtask_ready())) by {
    assert forall |i: int| #[trigger] (ro.acceptance)(qtask_ready(), i) implies (ro.validity)(qtask_ready(), i) by {
      if i == 0 {} else if i == 1 {}
    }
  }
}

// No entry of qtask_ready is a reactor operation / Woken / PassWaker / Defer.
pub proof fn qtask_op_facts()
  ensures
    forall |i: int| #![trigger qtask_ready()[i]] 0 <= i < qtask_ready().len() ==>
      !crate::composed::spec::alignment::is_reactor_operation(qtask_ready()[i]),
    forall |i: int| #![trigger qtask_ready()[i]] 0 <= i < qtask_ready().len() ==>
      !ue::is_woken(qtask_ready()[i]),
    forall |i: int| #![trigger qtask_ready()[i]] 0 <= i < qtask_ready().len() ==>
      !ue::is_pass_waker(qtask_ready()[i]),
    forall |i: int| #![trigger qtask_ready()[i]] 0 <= i < qtask_ready().len() ==>
      !ue::is_defer(qtask_ready()[i]),
{
  qtask_idx();
  assert forall |i: int| #![trigger qtask_ready()[i]] 0 <= i < qtask_ready().len() implies
    !crate::composed::spec::alignment::is_reactor_operation(qtask_ready()[i]) &&
    !ue::is_woken(qtask_ready()[i]) &&
    !ue::is_pass_waker(qtask_ready()[i]) &&
    !ue::is_defer(qtask_ready()[i]) by {
    if i == 0 {} else if i == 1 {}
  }
}

// ============================================================================
// Cross-module alignment
// ============================================================================

// Action mediation at qs1/qs2: NO task-initiated reactor events and NO reactor
// operations in any task log — every conjunct is vacuous.
proof fn q_am_state(s: ComposedState, tid: TID)
  requires
    s.reactor_log == qreac1() || s.reactor_log == qreac2(),
    forall |t2: TaskId| #[trigger] s.task_logs.contains_key(t2) ==> s.task_logs[t2] == qtask_ready(),
  ensures
    crate::composed::spec::alignment::action_mediation_state(s),
{
  qtask_op_facts();
  use crate::composed::spec::alignment::*;
  assert(operation_to_reactor_exists(s)) by {
    assert forall |t2: TaskId, i: int|
      s.task_logs.contains_key(t2) && 0 <= i < s.task_logs[t2].len() &&
      is_reactor_operation(#[trigger] s.task_logs[t2][i])
      implies false by {
      assert(s.task_logs[t2] == qtask_ready());
    }
  }
  assert(reactor_registration_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() &&
      (re::is_succ_register_timer(s.reactor_log[j]) || re::is_succ_io_syscall_register(s.reactor_log[j]))
      implies false by {
      if s.reactor_log == qreac1() { qreac1_flags(j); } else { qreac2_flags(j); }
    }
  }
  assert(reactor_outbound_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() && is_task_initiated_reactor_event(s.reactor_log[j])
      implies false by {
      if s.reactor_log == qreac1() { qreac1_flags(j); } else { qreac2_flags(j); }
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
      implies t1 == t2 && ti1 == ti2 by {
      assert(s.task_logs[t1] == qtask_ready());
      assert(!is_reactor_operation(s.task_logs[t1][ti1]));
    }
  }
  assert forall |t2: TaskId, a: int, b: int|
    #![trigger s.task_logs[t2][a], s.task_logs[t2][b]]
    s.task_logs.contains_key(t2) && 0 <= a < b < s.task_logs[t2].len() &&
    is_reactor_operation(s.task_logs[t2][a])
    implies !is_reactor_operation(s.task_logs[t2][b]) by {
    assert(s.task_logs[t2] == qtask_ready());
    assert(!is_reactor_operation(s.task_logs[t2][a]));
  }
  monotonic_alignment_holds_no_two_ops(s);
  assert(succ_deregister_by_owner(s)) by { reveal(succ_deregister_by_owner); }
  assert(deregister_matches_own_registration(s)) by { reveal(deregister_matches_own_registration); }
  assert(deregister_io_matches_own_registration(s)) by { reveal(deregister_io_matches_own_registration); }
  assert(succ_deregister_io_by_owner(s)) by { reveal(succ_deregister_io_by_owner); }
}

// Action-mediation step: no new reactor ops in task logs, no new task-initiated
// reactor events (both idle park rounds) — all five conjuncts vacuous.
proof fn q_am_step(s: ComposedState, s2: ComposedState)
  requires
    s2.reactor_log == qreac1() || s2.reactor_log == qreac2(),
    forall |t2: TaskId| #[trigger] s2.task_logs.contains_key(t2) ==> s2.task_logs[t2] == qtask_ready(),
  ensures
    crate::composed::spec::alignment::action_mediation_step(s, s2),
{
  qtask_op_facts();
  use crate::composed::spec::alignment::*;
  assert(new_operation_alignment(s, s2)) by {
    assert forall |t2: TaskId, i: int|
      is_new_task_operation(s, s2, t2, i) && is_reactor_operation(#[trigger] s2.task_logs[t2][i])
      implies exists |j: int| s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][i]) by {
      assert(s2.task_logs[t2] == qtask_ready());
      assert(!is_reactor_operation(s2.task_logs[t2][i]));
    }
  }
  assert(new_operation_uniqueness(s, s2)) by {
    assert forall |t1: TaskId, t2: TaskId, a1: int, a2: int, ri: int|
      #![trigger s2.task_logs[t1][a1], s2.task_logs[t2][a2], s2.reactor_log[ri]]
      is_new_task_operation(s, s2, t1, a1) && is_new_task_operation(s, s2, t2, a2) &&
      is_reactor_operation(s2.task_logs[t1][a1]) && is_reactor_operation(s2.task_logs[t2][a2]) &&
      s.reactor_log.len() as int <= ri < s2.reactor_log.len() &&
      succ_reactor_event_matches_task_operation(s2.reactor_log[ri], s2.task_logs[t1][a1]) &&
      succ_reactor_event_matches_task_operation(s2.reactor_log[ri], s2.task_logs[t2][a2])
      implies t1 == t2 && a1 == a2 by {
      assert(s2.task_logs[t1] == qtask_ready());
      assert(!is_reactor_operation(s2.task_logs[t1][a1]));
    }
  }
  assert(new_op_matches_only_new_reactor(s, s2)) by {
    assert forall |t2: TaskId, ti: int, ri: int|
      is_new_task_operation(s, s2, t2, ti) && is_reactor_operation(#[trigger] s2.task_logs[t2][ti]) &&
      0 <= ri < s2.reactor_log.len() &&
      succ_reactor_event_matches_task_operation(#[trigger] s2.reactor_log[ri], s2.task_logs[t2][ti])
      implies ri >= s.reactor_log.len() by {
      assert(s2.task_logs[t2] == qtask_ready());
      assert(!is_reactor_operation(s2.task_logs[t2][ti]));
    }
  }
  assert(reactor_outbound_has_task_operation(s, s2)) by {
    assert forall |j: int| #![trigger s2.reactor_log[j]]
      s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
      is_task_initiated_reactor_event(s2.reactor_log[j])
      implies false by {
      if s2.reactor_log == qreac1() { qreac1_flags(j); } else { qreac2_flags(j); }
    }
  }
  assert(new_reactor_event_has_new_op(s, s2)) by {
    assert forall |j: int| #![trigger s2.reactor_log[j]]
      s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
      is_task_initiated_reactor_event(s2.reactor_log[j])
      implies false by {
      if s2.reactor_log == qreac1() { qreac1_flags(j); } else { qreac2_flags(j); }
    }
  }
}

// The last poll of qother in qexec1/qexec2 is the Ready poll @6 — not Pending.
proof fn qother_last_poll_not_pending(tid: TID, l: el::Log)
  requires l == qexec1(tid) || l == qexec2(tid),
  ensures !el::last_poll_is_pending(l, qother(tid)),
{
  qexec1_idx(tid); qexec2_idx(tid);
  if el::last_poll_is_pending(l, qother(tid)) {
    crate::composed::proof::end_to_end::last_poll_idx_properties(l, qother(tid));
    let idx = el::last_poll_idx_for_id(l, qother(tid));
    assert(el::is_poll_task_for_id_at(l, idx, qother(tid)));
    if l == qexec1(tid) { qexec1_flags(tid, idx); } else {
      qexec2_flags(tid, idx);
      if idx == 14 { assert(ee::get_poll_task_id(l[14]) == tid && qother(tid) != tid); }
    }
    assert(idx == 6);
    assert(!el::is_poll_pending_for_id_at(l, 6, qother(tid)));
  }
}

// The last poll of tid in qexec2 is the Ready poll @14 — not Pending.
proof fn qtid_last_poll_not_pending(tid: TID)
  ensures !el::last_poll_is_pending(qexec2(tid), tid),
{
  let l = qexec2(tid);
  qexec2_idx(tid);
  if el::last_poll_is_pending(l, tid) {
    crate::composed::proof::end_to_end::last_poll_idx_properties(l, tid);
    let idx = el::last_poll_idx_for_id(l, tid);
    assert(el::is_poll_task_for_id_at(l, idx, tid));
    qexec2_flags(tid, idx);
    if idx == 6 { assert(ee::get_poll_task_id(l[6]) == qother(tid) && qother(tid) != tid); }
    assert(idx == 14);
    assert(!el::is_poll_pending_for_id_at(l, 14, tid));
  }
}

proof fn qs1_obs_consistency(tid: TID)
  ensures
    crate::composed::spec::alignment::observation_consistency_state(qs1(tid)),
    crate::composed::spec::alignment::observation_consistency_step(qs0(tid), qs1(tid)),
{
  let s = qs0(tid);
  let s2 = qs1(tid);
  qexec1_idx(tid); qtask_idx();
  use crate::composed::spec::alignment::*;
  assert(observation_consistency_state(s2)) by {
    assert(polled_task_has_log_inv(s2)) by {
      assert forall |t2: TaskId| el::has_poll_for_id(s2.executor_log, t2) implies s2.task_logs.contains_key(t2) by {
        if !s2.task_logs.contains_key(t2) {
          assert forall |i: int| #![trigger s2.executor_log[i]] 0 <= i < s2.executor_log.len()
            implies !el::is_poll_task_for_id_at(s2.executor_log, i, t2) by {
            qexec1_flags(tid, i);
            if i == 6 { assert(ee::get_poll_task_id(s2.executor_log[6]) == qother(tid)); }
          }
        }
      }
    }
    assert(pending_poll_inv(s2)) by {
      assert forall |t2: TaskId| #![trigger s2.task_logs[t2]]
        s2.task_logs.contains_key(t2) && el::last_poll_is_pending(s2.executor_log, t2)
        implies task_log_ends_with_pending(s2.task_logs[t2]) by {
        assert(t2 == qother(tid));
        qother_last_poll_not_pending(tid, s2.executor_log);
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
        qexec1_flags(tid, i);
        if i == 6 {
          assert(ee::get_poll_result(s2.executor_log[6]) == crate::executor::spec::types::PollResult::Ready(()));
        }
      }
    }
    assert(new_poll_has_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2)
        implies s2.task_logs.contains_key(t2) by {
        qexec1_flags(tid, i);
        if i == 6 { assert(t2 == qother(tid)); }
      }
    }
    assert(new_poll_changes_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2) && s.task_logs.contains_key(t2)
        implies s.task_logs[t2].len() < s2.task_logs[t2].len() by {
        assert(!s.task_logs.contains_key(t2));
      }
    }
  }
}

proof fn qs2_obs_consistency(tid: TID)
  ensures
    crate::composed::spec::alignment::observation_consistency_state(qs2(tid)),
    crate::composed::spec::alignment::observation_consistency_step(qs1(tid), qs2(tid)),
{
  let s = qs1(tid);
  let s2 = qs2(tid);
  qexec2_idx(tid); qexec1_idx(tid); qtask_idx();
  use crate::composed::spec::alignment::*;
  assert(observation_consistency_state(s2)) by {
    assert(polled_task_has_log_inv(s2)) by {
      assert forall |t2: TaskId| el::has_poll_for_id(s2.executor_log, t2) implies s2.task_logs.contains_key(t2) by {
        if !s2.task_logs.contains_key(t2) {
          assert forall |i: int| #![trigger s2.executor_log[i]] 0 <= i < s2.executor_log.len()
            implies !el::is_poll_task_for_id_at(s2.executor_log, i, t2) by {
            qexec2_flags(tid, i);
            if i == 6 { assert(ee::get_poll_task_id(s2.executor_log[6]) == qother(tid)); }
            else if i == 14 { assert(ee::get_poll_task_id(s2.executor_log[14]) == tid); }
          }
        }
      }
    }
    assert(pending_poll_inv(s2)) by {
      assert forall |t2: TaskId| #![trigger s2.task_logs[t2]]
        s2.task_logs.contains_key(t2) && el::last_poll_is_pending(s2.executor_log, t2)
        implies task_log_ends_with_pending(s2.task_logs[t2]) by {
        assert(t2 == qother(tid) || t2 == tid);
        if t2 == qother(tid) { qother_last_poll_not_pending(tid, s2.executor_log); }
        else { qtid_last_poll_not_pending(tid); }
      }
    }
  }
  assert(observation_consistency_step(s, s2)) by {
    assert(poll_alignment(s, s2)) by {
      assert forall |t2: TaskId| #![trigger s2.task_logs[t2]]
        s.task_logs.contains_key(t2) && s2.task_logs.contains_key(t2) &&
        s.task_logs[t2].len() < s2.task_logs[t2].len()
        implies el::has_poll_task_for_id_after(s2.executor_log, t2, s.executor_log.len() as int) by {
        // the only pre-existing task log (qother) does NOT grow this step
        assert(t2 == qother(tid));
        assert(s.task_logs[t2] == qtask_ready() && s2.task_logs[t2] == qtask_ready());
      }
    }
    assert(pending_poll_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_pending_for_id_at(s2.executor_log, i, t2) && s2.task_logs.contains_key(t2)
        implies task_log_ends_with_pending(s2.task_logs[t2]) by {
        qexec2_flags(tid, i);
        if i == 14 {
          assert(ee::get_poll_result(s2.executor_log[14]) == crate::executor::spec::types::PollResult::Ready(()));
        }
      }
    }
    assert(new_poll_has_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2)
        implies s2.task_logs.contains_key(t2) by {
        qexec2_flags(tid, i);
        if i == 14 { assert(t2 == tid); }
      }
    }
    assert(new_poll_changes_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2) && s.task_logs.contains_key(t2)
        implies s.task_logs[t2].len() < s2.task_logs[t2].len() by {
        qexec2_flags(tid, i);
        if i == 14 { assert(t2 == tid); assert(!s.task_logs.contains_key(tid)); }
      }
    }
  }
}

proof fn qs1_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(qs0(tid), qs1(tid)),
{
  qexec1_idx(tid); qreac1_idx();
  use crate::composed::spec::alignment::*;
  let e = qexec1(tid);
  assert(count_park_events_in(e, 8, 8) == 0);
  assert(count_park_events_in(e, 7, 8) == 0) by { qexec1_flags(tid, 7); }
  assert(count_park_events_in(e, 6, 8) == 0) by { qexec1_flags(tid, 6); }
  assert(count_park_events_in(e, 5, 8) == 0) by { qexec1_flags(tid, 5); }
  assert(count_park_events_in(e, 4, 8) == 1) by { qexec1_flags(tid, 4); }
  assert(count_park_events_in(e, 3, 8) == 1) by { qexec1_flags(tid, 3); }
  assert(count_park_events_in(e, 2, 8) == 1) by { qexec1_flags(tid, 2); }
  assert(count_park_events_in(e, 1, 8) == 1) by { qexec1_flags(tid, 1); }
  assert(count_park_events_in(e, 0, 8) == 1) by { qexec1_flags(tid, 0); }
  let r = qreac1();
  assert(count_park_cycles_in(r, 4, 4) == 0);
  assert(count_park_cycles_in(r, 3, 4) == 1) by { qreac1_flags(3); }
  assert(count_park_cycles_in(r, 2, 4) == 1) by { qreac1_flags(2); }
  assert(count_park_cycles_in(r, 1, 4) == 1) by { qreac1_flags(1); }
  assert(count_park_cycles_in(r, 0, 4) == 1) by { qreac1_flags(0); }
}

proof fn qs2_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(qs1(tid), qs2(tid)),
{
  qexec2_idx(tid); qreac2_idx();
  use crate::composed::spec::alignment::*;
  let e = qexec2(tid);
  assert(count_park_events_in(e, 16, 16) == 0);
  assert(count_park_events_in(e, 15, 16) == 0) by { qexec2_flags(tid, 15); }
  assert(count_park_events_in(e, 14, 16) == 0) by { qexec2_flags(tid, 14); }
  assert(count_park_events_in(e, 13, 16) == 0) by { qexec2_flags(tid, 13); }
  assert(count_park_events_in(e, 12, 16) == 1) by { qexec2_flags(tid, 12); }
  assert(count_park_events_in(e, 11, 16) == 1) by { qexec2_flags(tid, 11); }
  assert(count_park_events_in(e, 10, 16) == 1) by { qexec2_flags(tid, 10); }
  assert(count_park_events_in(e, 9, 16) == 1) by { qexec2_flags(tid, 9); }
  assert(count_park_events_in(e, 8, 16) == 1) by { qexec2_flags(tid, 8); }
  let r = qreac2();
  assert(count_park_cycles_in(r, 8, 8) == 0);
  assert(count_park_cycles_in(r, 7, 8) == 1) by { qreac2_flags(7); }
  assert(count_park_cycles_in(r, 6, 8) == 1) by { qreac2_flags(6); }
  assert(count_park_cycles_in(r, 5, 8) == 1) by { qreac2_flags(5); }
  assert(count_park_cycles_in(r, 4, 8) == 1) by { qreac2_flags(4); }
}

#[verifier::rlimit(100)]
pub proof fn qs1_cross(tid: TID)
  ensures
    cross_module_alignment(qs0(tid), qs1(tid)),
{
  reveal(cross_module_alignment);
  let s = qs0(tid);
  let s2 = qs1(tid);
  qexec1_idx(tid); qreac1_idx(); qtask_idx();
  q_am_state(s2, tid);
  q_am_step(s, s2);
  qs1_obs_consistency(tid);
  qs1_park_alignment(tid);
}

#[verifier::rlimit(100)]
pub proof fn qs2_cross(tid: TID)
  ensures
    cross_module_alignment(qs1(tid), qs2(tid)),
{
  reveal(cross_module_alignment);
  let s = qs1(tid);
  let s2 = qs2(tid);
  qexec2_idx(tid); qreac2_idx(); qtask_idx();
  q_am_state(s2, tid);
  q_am_step(s, s2);
  qs2_obs_consistency(tid);
  qs2_park_alignment(tid);
}

// ============================================================================
// Injection schedule: pops deliver [qother, tid] in order
// ============================================================================

pub proof fn qexec_injected(tid: TID)
  ensures
    crate::executor::spec::injection_schedule::injected_tasks(qexec1(tid)) =~=
      seq![crate::executor::spec::types::TaskView { id: qother(tid) }],
    crate::executor::spec::injection_schedule::injected_tasks(qexec2(tid)) =~= qsched(tid),
{
  use crate::executor::spec::injection_schedule::injected_tasks;
  qexec1_idx(tid);
  qexec2_idx(tid);
  let l1 = qexec1(tid);
  let q1 = seq![crate::executor::spec::types::TaskView { id: qother(tid) }];
  assert(injected_tasks(l1.subrange(0, 0)) =~= Seq::<crate::executor::spec::types::TaskView>::empty());
  assert(l1.subrange(0,1).subrange(0,0) =~= l1.subrange(0,0));
  assert(injected_tasks(l1.subrange(0, 1)) =~= Seq::<crate::executor::spec::types::TaskView>::empty());
  assert(l1.subrange(0,2).subrange(0,1) =~= l1.subrange(0,1));
  assert(injected_tasks(l1.subrange(0, 2)) =~= q1);
  assert(l1.subrange(0,3).subrange(0,2) =~= l1.subrange(0,2));
  assert(injected_tasks(l1.subrange(0, 3)) =~= q1);
  assert(l1.subrange(0,4).subrange(0,3) =~= l1.subrange(0,3));
  assert(injected_tasks(l1.subrange(0, 4)) =~= q1);
  assert(l1.subrange(0,5).subrange(0,4) =~= l1.subrange(0,4));
  assert(injected_tasks(l1.subrange(0, 5)) =~= q1);
  assert(l1.subrange(0,6).subrange(0,5) =~= l1.subrange(0,5));
  assert(injected_tasks(l1.subrange(0, 6)) =~= q1);
  assert(l1.subrange(0,7).subrange(0,6) =~= l1.subrange(0,6));
  assert(injected_tasks(l1.subrange(0, 7)) =~= q1);
  assert(l1.subrange(0,8).subrange(0,7) =~= l1.subrange(0,7));
  assert(l1.subrange(0,8) =~= l1);
  assert(injected_tasks(l1) =~= q1);
  let l2 = qexec2(tid);
  assert(l2.subrange(0, 8) =~= l1);
  assert(injected_tasks(l2.subrange(0, 8)) =~= q1);
  assert(l2.subrange(0,9).subrange(0,8) =~= l2.subrange(0,8));
  assert(injected_tasks(l2.subrange(0, 9)) =~= q1);
  assert(l2.subrange(0,10).subrange(0,9) =~= l2.subrange(0,9));
  assert(injected_tasks(l2.subrange(0, 10)) =~= qsched(tid));
  assert(l2.subrange(0,11).subrange(0,10) =~= l2.subrange(0,10));
  assert(injected_tasks(l2.subrange(0, 11)) =~= qsched(tid));
  assert(l2.subrange(0,12).subrange(0,11) =~= l2.subrange(0,11));
  assert(injected_tasks(l2.subrange(0, 12)) =~= qsched(tid));
  assert(l2.subrange(0,13).subrange(0,12) =~= l2.subrange(0,12));
  assert(injected_tasks(l2.subrange(0, 13)) =~= qsched(tid));
  assert(l2.subrange(0,14).subrange(0,13) =~= l2.subrange(0,13));
  assert(injected_tasks(l2.subrange(0, 14)) =~= qsched(tid));
  assert(l2.subrange(0,15).subrange(0,14) =~= l2.subrange(0,14));
  assert(injected_tasks(l2.subrange(0, 15)) =~= qsched(tid));
  assert(l2.subrange(0,16).subrange(0,15) =~= l2.subrange(0,15));
  assert(l2.subrange(0,16) =~= l2);
  assert(injected_tasks(l2) =~= qsched(tid));
}

pub proof fn qpops_deliver(tid: TID)
  ensures
    crate::executor::spec::injection_schedule::pops_deliver_schedule(qexec1(tid), qsched(tid)),
    crate::executor::spec::injection_schedule::pops_deliver_schedule(qexec2(tid), qsched(tid)),
{
  use crate::executor::spec::injection_schedule::*;
  qexec1_idx(tid); qexec2_idx(tid);
  qexec_injected(tid);
  let q = qsched(tid);
  assert(injected_tasks(qexec1(tid)) =~= q.subrange(0, 1));
  assert(is_task_prefix(injected_tasks(qexec1(tid)), q));
  assert(injected_tasks(qexec2(tid)) =~= q.subrange(0, 2));
  assert(is_task_prefix(injected_tasks(qexec2(tid)), q));
  assert(injected_tasks(qexec2(tid)).len() >= q.len());
  // qexec1's threshold clause: only 1 pop so far (< |q| = 2) — antecedent false.
  let l1 = qexec1(tid);
  assert(el::count_pop_injection_between(l1, 8, 8) == 0);
  assert(el::count_pop_injection_between(l1, 7, 8) == 0) by { qexec1_flags(tid, 7); }
  assert(el::count_pop_injection_between(l1, 6, 8) == 0) by { qexec1_flags(tid, 6); }
  assert(el::count_pop_injection_between(l1, 5, 8) == 0) by { qexec1_flags(tid, 5); }
  assert(el::count_pop_injection_between(l1, 4, 8) == 0) by { qexec1_flags(tid, 4); }
  assert(el::count_pop_injection_between(l1, 3, 8) == 0) by { qexec1_flags(tid, 3); }
  assert(el::count_pop_injection_between(l1, 2, 8) == 0) by { qexec1_flags(tid, 2); }
  assert(el::count_pop_injection_between(l1, 1, 8) == 1);
  assert(el::count_pop_injection_between(l1, 0, 8) == 1) by { qexec1_flags(tid, 0); }
}

// ============================================================================
// Wake-queue drain steps are vacuous (no Defer/Woken/WakeTask anywhere)
// ============================================================================

proof fn q_no_deferred(s: ComposedState, tid: TID)
  requires
    s == qs0(tid) || s == qs1(tid),
  ensures
    forall |t2: TaskId| !crate::composed::spec::wake_queues::in_deferred_queue(s, t2),
{
  assert forall |t2: TaskId| !crate::composed::spec::wake_queues::in_deferred_queue(s, t2) by {
    if s.task_logs.contains_key(t2) {
      assert(s == qs1(tid) && t2 == qother(tid));
      qother_last_poll_not_pending(tid, qexec1(tid));
    }
  }
}

proof fn q_wake_queue_steps(s: ComposedState, s2: ComposedState, tid: TID)
  requires
    s == qs0(tid) || s == qs1(tid),
  ensures
    crate::composed::spec::wake_queues::deferred_drain_step(s, s2),
    crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2),
    crate::composed::spec::wake_queues::taskwake_drain_step(s, s2),
{
  // Deferred: nothing is deferred at s.
  q_no_deferred(s, tid);
  // ReactorWake: no WakeTask in s's reactor log.
  assert forall |w: int| 0 <= w < s.reactor_log.len() implies
    !rl::is_wake_task_at(s.reactor_log, w) by {
    if s == qs1(tid) { qreac1_flags(w); }
  }
  no_reactor_wake_pending_no_waketask(s);
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2));
  // TaskWake: no Woken in any of s's task logs.
  qtask_op_facts();
  assert forall |t2: TID| #[trigger] s.task_logs.contains_key(t2) implies
    (forall |j: int| 0 <= j < s.task_logs[t2].len() ==> !ue::is_woken(s.task_logs[t2][j])) by {
    assert(s == qs1(tid) && t2 == qother(tid));
    assert(s.task_logs[t2] == qtask_ready());
  }
  no_taskwake_pending_no_woken(s);
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2));
}

// ============================================================================
// composed_progress for both steps
// ============================================================================

#[verifier::rlimit(100)]
pub proof fn qs1_composed_progress(tid: TID)
  ensures
    composed_progress(qs0(tid), qs1(tid)),
{
  reveal(composed_progress);
  let s = qs0(tid);
  let s2 = qs1(tid);
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 0)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 0)); }
  assert(is_extension_of(s, s2));
  qexec1_exec_progress(tid);
  assert(s.executor_log =~= Seq::<ee::ExecutorEvent>::empty());
  qreac1_reac_progress();
  assert(s.reactor_log =~= Seq::<re::ReactorEvent>::empty());
  qs1_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    qtask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(t2 == qother(tid) && s2.task_logs[t2] == qtask_ready());
    }
  }
  qtask_op_facts();
  assert forall |t2: TaskId, a: int, b: int|
    #![trigger s2.task_logs[t2][a], s2.task_logs[t2][b]]
    s2.task_logs.contains_key(t2) && 0 <= a < b < s2.task_logs[t2].len() &&
    crate::composed::spec::alignment::is_reactor_operation(s2.task_logs[t2][a])
    implies !crate::composed::spec::alignment::is_reactor_operation(s2.task_logs[t2][b]) by {
    assert(s2.task_logs[t2] == qtask_ready());
    assert(!crate::composed::spec::alignment::is_reactor_operation(s2.task_logs[t2][a]));
  }
  crate::composed::spec::alignment::monotonic_alignment_holds_no_two_ops(s2);
  qpops_deliver(tid);
  q_wake_queue_steps(s, s2, tid);
}

#[verifier::rlimit(100)]
pub proof fn qs2_composed_progress(tid: TID)
  ensures
    composed_progress(qs1(tid), qs2(tid)),
{
  reveal(composed_progress);
  let s = qs1(tid);
  let s2 = qs2(tid);
  qexec2_idx(tid); qreac2_idx(); qtask_idx();
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 8)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 4)); }
  assert(is_extension_of(s, s2)) by {
    assert forall |t2: TaskId| s.task_logs.contains_key(t2) implies
      s2.task_logs.contains_key(t2) &&
      crate::composed::spec::state::is_task_log_prefix(#[trigger] s.task_logs[t2], s2.task_logs[t2]) by {
      assert(t2 == qother(tid));
      assert(s.task_logs[t2] == qtask_ready() && s2.task_logs[t2] == qtask_ready());
    }
  }
  qexec2_exec_progress(tid);
  qreac2_reac_progress();
  qs2_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    qtask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(s2.task_logs[t2] == qtask_ready());
    }
  }
  qtask_op_facts();
  assert forall |t2: TaskId, a: int, b: int|
    #![trigger s2.task_logs[t2][a], s2.task_logs[t2][b]]
    s2.task_logs.contains_key(t2) && 0 <= a < b < s2.task_logs[t2].len() &&
    crate::composed::spec::alignment::is_reactor_operation(s2.task_logs[t2][a])
    implies !crate::composed::spec::alignment::is_reactor_operation(s2.task_logs[t2][b]) by {
    assert(s2.task_logs[t2] == qtask_ready());
    assert(!crate::composed::spec::alignment::is_reactor_operation(s2.task_logs[t2][a]));
  }
  crate::composed::spec::alignment::monotonic_alignment_holds_no_two_ops(s2);
  qpops_deliver(tid);
  q_wake_queue_steps(s, s2, tid);
}

// ============================================================================
// env_N at each witness state (cap = 1, for tid)
// ============================================================================

// Reactor-side env facts for the idle park rounds.
proof fn qreac_env_facts(s: ComposedState, tid: TID)
  requires
    s.reactor_log == qreac1() || s.reactor_log == qreac2(),
  ensures
    crate::composed::spec::assumptions::timestamps_strictly_increasing(s.reactor_log),
    crate::reactor::timestamps_positive(s.reactor_log),
    timer_deadline_gap_bounded(s, tid),
    timer_resources_remain_active(s),
    contract_io_assumption_here(s),
    forall |rid: ResourceIdView, n: nat|
      #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
      io_ready_forward_here(s.reactor_log, rid, n),
{
  qreac1_idx(); qreac2_idx();
  let l = s.reactor_log;
  assert(crate::composed::spec::assumptions::timestamps_strictly_increasing(l)) by {
    assert forall |a: int, b: int| 0 <= a < b < l.len() &&
      rl::is_get_current_time_at(l, a) && rl::is_get_current_time_at(l, b)
      implies re::get_current_timestamp(l[a]) < re::get_current_timestamp(l[b]) by {
      if l == qreac1() { qreac1_flags(a); qreac1_flags(b); } else { qreac2_flags(a); qreac2_flags(b); }
    }
  }
  assert(crate::reactor::timestamps_positive(l)) by {
    assert forall |a: int| 0 <= a < l.len() && rl::is_get_current_time_at(l, a)
      implies re::get_current_timestamp(l[a]) >= 1 by {
      if l == qreac1() { qreac1_flags(a); } else { qreac2_flags(a); }
    }
  }
  assert(timer_deadline_gap_bounded(s, tid)) by {
    reveal(timer_deadline_gap_bounded);
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < l.len() && rl::is_succ_register_timer_at(l, reg_idx)
      implies false by {
      if l == qreac1() { qreac1_flags(reg_idx); } else { qreac2_flags(reg_idx); }
    }
  }
  assert(timer_resources_remain_active(s)) by {
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < l.len() && rl::is_succ_register_timer_at(l, reg_idx)
      implies false by {
      if l == qreac1() { qreac1_flags(reg_idx); } else { qreac2_flags(reg_idx); }
    }
  }
  q_find_last_sw_facts(l);
  assert(contract_io_assumption_here(s)) by {
    assert forall |rid: ResourceIdView| #![trigger io_assumption_here(s.reactor_log, rid)]
      io_assumption_here(s.reactor_log, rid) by {
      assert(crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
        l, rid, l.len() as int) == -1);
      assert(crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(l, rid));
    }
  }
  assert forall |rid: ResourceIdView, n: nat|
    #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
    io_ready_forward_here(s.reactor_log, rid, n) by {
    assert(crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(l, rid, l.len() as int) == -1);
  }
}

// find_last_set_waker_for_rid == -1 on the idle park rounds (no SetWaker at all).
proof fn q_find_last_sw_facts(l: rl::Log)
  requires l == qreac1() || l == qreac2(),
  ensures
    forall |rid: ResourceIdView|
      #![trigger crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(l, rid, l.len() as int)]
      crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(l, rid, l.len() as int) == -1,
{
  qreac1_idx(); qreac2_idx();
  use crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid as fl;
  assert forall |rid: ResourceIdView|
    #![trigger fl(l, rid, l.len() as int)]
    fl(l, rid, l.len() as int) == -1 by {
    assert(fl(l, rid, 0) == -1);
    assert(fl(l, rid, 1) == -1) by { if l == qreac1() { qreac1_flags(0); } else { qreac2_flags(0); } }
    assert(fl(l, rid, 2) == -1) by { if l == qreac1() { qreac1_flags(1); } else { qreac2_flags(1); } }
    assert(fl(l, rid, 3) == -1) by { if l == qreac1() { qreac1_flags(2); } else { qreac2_flags(2); } }
    assert(fl(l, rid, 4) == -1) by { if l == qreac1() { qreac1_flags(3); } else { qreac2_flags(3); } }
    if l == qreac2() {
      assert(fl(l, rid, 5) == -1) by { qreac2_flags(4); }
      assert(fl(l, rid, 6) == -1) by { qreac2_flags(5); }
      assert(fl(l, rid, 7) == -1) by { qreac2_flags(6); }
      assert(fl(l, rid, 8) == -1) by { qreac2_flags(7); }
    }
  }
}

// tid is popped exactly once in qexec2 (and never in qexec1).
proof fn q_tid_unique(tid: TID, l: el::Log)
  requires l == qexec1(tid) || l == qexec2(tid),
  ensures el::tid_unique(l, tid),
{
  qexec1_idx(tid); qexec2_idx(tid);
  assert forall |a: int, b: int|
    #![trigger l[a], l[b]]
    0 <= a < l.len() && 0 <= b < l.len() && a != b &&
    el::is_pop_injection_at(l, a) && ee::get_pop_injection_task(l[a]).is_some() &&
    ee::get_pop_injection_task(l[a]).unwrap().id == tid &&
    el::is_pop_injection_at(l, b) && ee::get_pop_injection_task(l[b]).is_some() &&
    ee::get_pop_injection_task(l[b]).unwrap().id == tid
    implies false by {
    if l == qexec1(tid) {
      qexec1_flags(tid, a); qexec1_flags(tid, b);
      assert(ee::get_pop_injection_task(l[1]).unwrap().id == qother(tid) && qother(tid) != tid);
    } else {
      qexec2_flags(tid, a); qexec2_flags(tid, b);
      assert(ee::get_pop_injection_task(l[1]).unwrap().id == qother(tid) && qother(tid) != tid);
      assert(a == 9 && b == 9);
    }
  }
}

// FIFO queue bound 1 on both executor logs.
proof fn q_queue_len(tid: TID, l: el::Log)
  requires l == qexec1(tid) || l == qexec2(tid),
  ensures
    forall |i: int| 0 <= i <= l.len() ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i).len() <= 1,
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  if l == qexec1(tid) {
    qexec1_queue(tid);
    assert forall |i: int| 0 <= i <= l.len() implies #[trigger] fifo_queue_at(l, i).len() <= 1 by {
      qexec1_queue(tid);
      if 2 <= i <= 6 { } else { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
    }
  } else {
    qexec2_queue(tid);
    assert forall |i: int| 0 <= i <= l.len() implies #[trigger] fifo_queue_at(l, i).len() <= 1 by {
      qexec2_queue(tid);
      if 2 <= i <= 6 { } else if 10 <= i <= 14 { }
      else { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
    }
  }
}

// count_polls_for_tid(qexec1, tid) == 0: the only poll (@6) is qother's.
proof fn qpoll_count_qexec1(tid: TID)
  ensures
    crate::composed::spec::assumptions::count_polls_for_tid(qexec1(tid), tid) == 0,
{
  qexec1_idx(tid);
  use crate::composed::spec::assumptions::count_polls_for_tid;
  let l = qexec1(tid);
  assert forall |i: int| #![trigger l[i]] 0 <= i < l.len() implies
    !el::is_poll_task_for_id_at(l, i, tid) by {
    qexec1_flags(tid, i);
    if i == 6 { assert(ee::get_poll_task_id(l[6]) == qother(tid) && qother(tid) != tid); }
  }
  assert(count_polls_for_tid(l.subrange(0, 0), tid) == 0);
  assert(l.subrange(0,1).subrange(0,0) =~= l.subrange(0,0));
  assert(count_polls_for_tid(l.subrange(0, 1), tid) == 0);
  assert(l.subrange(0,2).subrange(0,1) =~= l.subrange(0,1));
  assert(count_polls_for_tid(l.subrange(0, 2), tid) == 0);
  assert(l.subrange(0,3).subrange(0,2) =~= l.subrange(0,2));
  assert(count_polls_for_tid(l.subrange(0, 3), tid) == 0);
  assert(l.subrange(0,4).subrange(0,3) =~= l.subrange(0,3));
  assert(count_polls_for_tid(l.subrange(0, 4), tid) == 0);
  assert(l.subrange(0,5).subrange(0,4) =~= l.subrange(0,4));
  assert(count_polls_for_tid(l.subrange(0, 5), tid) == 0);
  assert(l.subrange(0,6).subrange(0,5) =~= l.subrange(0,5));
  assert(count_polls_for_tid(l.subrange(0, 6), tid) == 0);
  assert(l.subrange(0,7).subrange(0,6) =~= l.subrange(0,6));
  assert(count_polls_for_tid(l.subrange(0, 7), tid) == 0);
  assert(l.subrange(0, 8) =~= l);
  assert(l.subrange(0,8).subrange(0,7) =~= l.subrange(0,7));
  assert(count_polls_for_tid(l, tid) == 0);
}

// Common executor-side env facts + the arrival bridge (discharged through its
// CONSEQUENT: tid IS committed in the schedule, at depth 1).
proof fn q_common_env_facts(s: ComposedState, tid: TID)
  requires
    s == qs1(tid) || s == qs2(tid),
    get_max_queue_length(s) >= 1,
  ensures
    el::tid_unique(s.executor_log, tid),
    queue_length_bounded(s),
{
  let l = s.executor_log;
  qexec1_idx(tid); qexec2_idx(tid); qpops_deliver(tid);
  q_tid_unique(tid, l);
  q_queue_len(tid, l);
  assert(queue_length_bounded(s)) by {
    assert forall |i: int|
      #![trigger crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i)]
      0 <= i <= l.len() implies
      crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i).len() <= get_max_queue_length(s) by {
      q_queue_len(tid, l);
    }
  }
}

pub proof fn qs0_env(tid: TID)
  ensures
    env_N(qs0(tid), tid, 1nat),
{
  let s = qs0(tid);
  env_core_holds_empty_logs(s, tid);
  assert(end_to_end_env(s, tid));
  assert(bounded_poll_count_here_with_bound(s, tid, 1nat)) by {
    assert(crate::composed::spec::assumptions::count_polls_for_tid(s.executor_log, tid) == 0);
  }
  assert forall |rid: ResourceIdView, n: nat|
    #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
    io_ready_forward_here(s.reactor_log, rid, n) by {
    assert(crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(s.reactor_log, rid, 0) == -1);
  }
  assert(!s.task_logs.contains_key(tid));
  taskwake_arrival_within_vacuous(s, tid, 1nat);
}

#[verifier::rlimit(100)]
proof fn qs1_env(tid: TID)
  requires
    get_max_queue_length(qs1(tid)) >= 1,
  ensures
    env_N(qs1(tid), tid, 1nat),
{
  let s = qs1(tid);
  qexec1_idx(tid); qreac1_idx(); qtask_idx();
  qreac_env_facts(s, tid);
  q_common_env_facts(s, tid);
  assert(bounded_poll_count_here_with_bound(s, tid, 1nat)) by { qpoll_count_qexec1(tid); }
  assert(env_holds_at_state_core(s, tid));
  assert(end_to_end_env(s, tid));
  assert(!s.task_logs.contains_key(tid)) by { assert(qother(tid) != tid); }
  taskwake_arrival_within_vacuous(s, tid, 1nat);
}

#[verifier::rlimit(100)]
proof fn qs2_env(tid: TID)
  requires
    get_max_queue_length(qs2(tid)) >= 1,
  ensures
    env_N(qs2(tid), tid, 1nat),
{
  let s = qs2(tid);
  qexec2_idx(tid); qreac2_idx(); qtask_idx();
  qreac_env_facts(s, tid);
  q_common_env_facts(s, tid);
  assert(bounded_poll_count_here_with_bound(s, tid, 1nat)) by {
    assert(el::is_poll_ready_for_id_at(s.executor_log, 14, tid));
    assert(crate::composed::spec::assumptions::task_polled_to_ready(s.executor_log, tid));
  }
  assert(env_holds_at_state_core(s, tid));
  assert(end_to_end_env(s, tid));
  qtid_last_poll_not_pending(tid);
  taskwake_arrival_within_vacuous(s, tid, 1nat);
}

// ============================================================================
// Assembly: the depth-1 domain is inhabited by a Ready-reaching trace
// ============================================================================

// composed_well_formed at the start state (empty logs, committed schedule
// [qother, tid]) — schedule content does not affect well-formedness.
pub proof fn qs0_well_formed(tid: TID)
  ensures
    crate::composed::spec::progress::composed_well_formed(qs0(tid)),
{
  let w = qs0(tid);
  assert(crate::executor::invariants::executor_inv(w.executor_log));
  assert(crate::reactor::invariants::reactor_inv(w.reactor_log));
  assert(crate::composed::spec::alignment::action_mediation_state(w)) by {
    assert(crate::composed::spec::alignment::operation_to_reactor_exists(w));
    assert(crate::composed::spec::alignment::reactor_to_operation_unique(w));
    assert(crate::composed::spec::alignment::reactor_outbound_to_task_exists(w));
    assert(crate::composed::spec::alignment::reactor_registration_to_task_exists(w));
    crate::composed::spec::alignment::monotonic_alignment_holds_empty(w);
    assert(crate::composed::spec::alignment::succ_deregister_by_owner(w)) by {
      reveal(crate::composed::spec::alignment::succ_deregister_by_owner);
    }
    assert(crate::composed::spec::alignment::deregister_matches_own_registration(w)) by {
      reveal(crate::composed::spec::alignment::deregister_matches_own_registration);
    }
    assert(crate::composed::spec::alignment::deregister_io_matches_own_registration(w)) by {
      reveal(crate::composed::spec::alignment::deregister_io_matches_own_registration);
    }
    assert(crate::composed::spec::alignment::succ_deregister_io_by_owner(w)) by {
      reveal(crate::composed::spec::alignment::succ_deregister_io_by_owner);
    }
  }
  assert(crate::composed::spec::alignment::observation_consistency_state(w));
}

// THE depth-generalization witness: tid at schedule depth 1 (a DIFFERENT task
// ahead of it), every theorem antecedent satisfied at qs0, and a REAL
// env_N(cap=1)-good 2-step trace from qs0 reaching Ready for tid — the
// depth-k theorem's domain is inhabited at k = 1 non-vacuously.
pub proof fn depth_domain_inhabited(tid: TaskId)
  requires
    get_max_queue_length(qs1(tid)) >= 1,
  ensures
    crate::composed::spec::contract::task_scheduled_at(qs0(tid), tid, 1nat),
    crate::composed::spec::progress::composed_well_formed(qs0(tid)),
    end_to_end_env(qs0(tid), tid),
    ete_reachable_N(qs0(tid), qs2(tid), 2nat, 1nat, tid),
    crate::composed::spec::contract::end_to_end_response(qs2(tid), tid),
    !crate::composed::spec::contract::end_to_end_trigger(qs0(tid), tid),
    !crate::composed::spec::contract::end_to_end_response(qs0(tid), tid),
{
  let s0 = qs0(tid);
  let s1 = qs1(tid);
  let s2 = qs2(tid);
  qexec2_idx(tid);
  assert(get_max_queue_length(s2) == get_max_queue_length(s1));
  assert(crate::composed::spec::contract::task_scheduled_at(s0, tid, 1nat)) by {
    assert(crate::executor::spec::injection_schedule::injected_tasks(s0.executor_log)
      =~= Seq::<crate::executor::spec::types::TaskView>::empty());
    assert(s0.injection_schedule[1].id == tid);
  }
  qs0_well_formed(tid);
  qs0_env(tid); qs1_env(tid); qs2_env(tid);
  assert(end_to_end_env(s0, tid));
  qs1_composed_progress(tid); qs2_composed_progress(tid);
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |x: ComposedState, t2: TaskId| env_N(x, t2, 1nat);
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

// Packaged satisfiability of the depth theorem's precondition at depth k = 1:
// there IS a real (s, tid, k >= 1) meeting every antecedent of
// end_to_end_liveness_from_depth (cap is universally quantified there; any
// cap >= 1 qualifies).
pub proof fn depth_precondition_satisfiable()
  ensures
    exists |s: ComposedState, tid: TaskId, k: nat|
      crate::composed::spec::progress::composed_well_formed(s) &&
      #[trigger] end_to_end_env(s, tid) &&
      #[trigger] crate::composed::spec::contract::task_scheduled_at(s, tid, k) &&
      k >= 1,
{
  let tid: TaskId = 0;
  if get_max_queue_length(qs1(tid)) >= 1 {
    depth_domain_inhabited(tid);
    assert(crate::composed::spec::progress::composed_well_formed(qs0(tid)) &&
      end_to_end_env(qs0(tid), tid) &&
      crate::composed::spec::contract::task_scheduled_at(qs0(tid), tid, 1nat) &&
      1nat >= 1 && 1nat >= 1);
  } else {
    // get_max_queue_length is an arbitrary() constant; when it is 0 fall back to
    // the schedule-only witness at qs0 (empty logs need no queue bound).
    qs0_well_formed(tid);
    qs0_env(tid);
    assert(crate::composed::spec::contract::task_scheduled_at(qs0(tid), tid, 1nat)) by {
      assert(crate::executor::spec::injection_schedule::injected_tasks(qs0(tid).executor_log)
        =~= Seq::<crate::executor::spec::types::TaskView>::empty());
      assert(qs0(tid).injection_schedule[1].id == tid);
    }
    env_N_implies_env(qs0(tid), tid, 1nat);
    assert(crate::composed::spec::progress::composed_well_formed(qs0(tid)) &&
      end_to_end_env(qs0(tid), tid) &&
      crate::composed::spec::contract::task_scheduled_at(qs0(tid), tid, 1nat) &&
      1nat >= 1 && 1nat >= 1);
  }
}

}
