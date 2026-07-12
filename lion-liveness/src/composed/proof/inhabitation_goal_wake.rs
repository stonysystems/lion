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
use crate::reactor::spec::types::{IoResultView, ResourceIdView};
use crate::utilities::spec::events as ue;
use crate::utilities::spec::log as ul;
#[cfg(verus_keep_ghost)]
use crate::composed::proof::assumption_satisfiable::{env_N, bounded_poll_count_here_with_bound,
  io_ready_forward_here, contract_io_assumption_here, io_assumption_here,
  end_to_end_env, env_holds_at_state_core};
#[cfg(verus_keep_ghost)]
use crate::composed::spec::assumptions::{
  timer_deadline_gap_bounded, timer_resources_remain_active,
  queue_length_bounded, get_max_timer_deadline_gap,
  get_max_queue_length};

verus! {

// ============================================================================
// Real-wake witness: a REAL-WAKE goal-reaching env-good trace
// exercising a genuine WAIT state (poll Pending on a registered timer) and a
// real WakeTask (WakeTask states are
// env-legal). cap = 2 (two polls: Pending then Ready).
//
//   s0 = arrival_witness(tid)
//   tick 1 (s0 → bs1): PopInj Some(tid); poll(Pending) registering timer RID;
//                      reactor registers the timer, one park cycle (clock=1<2).
//   tick 2 (bs1 → bs2): reactor clock reaches deadline 2 ⟹ WakeTask fires;
//                       executor DrainReactorWake[tid] delivers tid; poll(Ready).
//
// Target: ete_reachable_N(s0, bs2, 2, 2, tid) ∧ end_to_end_response(bs2, tid).
// ============================================================================

pub open spec fn RID() -> ResourceIdView { 7 }
pub open spec fn WK() -> int { 3 }
pub open spec fn DL() -> int { 2 }

// --- Reactor log: tick 1 (register timer + one park cycle, clock = 1) ---
pub open spec fn breac1() -> rl::Log {
  seq![
    re::ReactorEvent::Inbound(re::InboundCall::RegisterTimer {
      deadline: DL(), waker: WK(), result: Some(IoResultView::Ok(RID())),
    }),
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

// --- Reactor log: tick 1 + tick 2 (clock reaches 2 ⟹ WakeTask fires) ---
pub open spec fn breac2() -> rl::Log {
  breac1() + seq![
    re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 2int }),
    re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat),
    }),
    re::ReactorEvent::Outbound(re::OutboundCall::WakeTask {
      waker: WK(), source_rid: RID(),
    }),
    re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())),
    }),
  ]
}

// --- Executor log: tick 1 (spawn tid, poll Pending) ---
pub open spec fn bexec1(tid: TID) -> el::Log {
  seq![
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
      task_id: tid, task: None, result: crate::executor::spec::types::PollResult::Pending,
    }),
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
  ]
}

// --- Executor log: tick 1 + tick 2 (drain reactor-wake[tid], poll Ready) ---
pub open spec fn bexec2(tid: TID) -> el::Log {
  bexec1(tid) + seq![
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection { task: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: seq![tid],
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: tid, task: None, result: crate::executor::spec::types::PollResult::Ready(()),
    }),
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
  ]
}

// --- Task log: after tick 1 (PollBegin, RegisterTimer, PollEnd(Pending)) ---
pub open spec fn btask_pending() -> ul::Log {
  seq![
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    ue::UtilityEvent::Outbound(ue::OutboundCall::RegisterTimer {
      resource_id: RID(), deadline: 2nat,
    }),
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll {
      result: Some(ue::PollResult::Pending),
    }),
  ]
}

// --- Task log: after tick 2 (+ PollBegin, PollEnd(Ready)) ---
pub open spec fn btask_ready() -> ul::Log {
  btask_pending() + seq![
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll {
      result: Some(ue::PollResult::Ready),
    }),
  ]
}

pub open spec fn bsched(tid: TID) -> Seq<crate::executor::spec::types::TaskView> {
  seq![crate::executor::spec::types::TaskView { id: tid }]
}

pub open spec fn bs1(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: bexec1(tid),
    reactor_log: breac1(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, btask_pending()),
    injection_schedule: bsched(tid),
  }
}

pub open spec fn bs2(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: bexec2(tid),
    reactor_log: breac2(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, btask_ready()),
    injection_schedule: bsched(tid),
  }
}

// ============================================================================
// Index lemmas
// ============================================================================

pub proof fn breac1_idx()
  ensures
    breac1().len() == 5,
    breac1()[0] == re::ReactorEvent::Inbound(re::InboundCall::RegisterTimer {
      deadline: DL(), waker: WK(), result: Some(IoResultView::Ok(RID())) }),
    breac1()[1] == re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    breac1()[2] == re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 1int }),
    breac1()[3] == re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat) }),
    breac1()[4] == re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())) }),
{
}

pub proof fn breac2_idx()
  ensures
    breac2().len() == 10,
    forall |j: int| 0 <= j < 5 ==> breac2()[j] == breac1()[j],
    breac2()[5] == re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    breac2()[6] == re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 2int }),
    breac2()[7] == re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat) }),
    breac2()[8] == re::ReactorEvent::Outbound(re::OutboundCall::WakeTask {
      waker: WK(), source_rid: RID() }),
    breac2()[9] == re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())) }),
{
  breac1_idx();
}

pub proof fn bexec1_idx(tid: TID)
  ensures
    bexec1(tid).len() == 8,
    bexec1(tid)[0] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    bexec1(tid)[1] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection {
      task: Some(crate::executor::spec::types::TaskView { id: tid }) }),
    bexec1(tid)[4] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    bexec1(tid)[6] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: tid, task: None, result: crate::executor::spec::types::PollResult::Pending }),
    bexec1(tid)[7] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
{
}

pub proof fn bexec2_idx(tid: TID)
  ensures
    bexec2(tid).len() == 16,
    forall |k: int| 0 <= k < 8 ==> bexec2(tid)[k] == bexec1(tid)[k],
    bexec2(tid)[8] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    bexec2(tid)[11] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: Seq::<TID>::empty() }),
    bexec2(tid)[12] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    bexec2(tid)[13] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: seq![tid] }),
    bexec2(tid)[14] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: tid, task: None, result: crate::executor::spec::types::PollResult::Ready(()) }),
    bexec2(tid)[15] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
{
  bexec1_idx(tid);
}

pub proof fn btask_idx()
  ensures
    btask_pending().len() == 3,
    btask_ready().len() == 5,
    forall |i: int| 0 <= i < 3 ==> btask_ready()[i] == btask_pending()[i],
    ue::is_poll_begin(btask_pending()[0]),
    ue::is_register_timer(btask_pending()[1]),
    ue::get_resource_id(btask_pending()[1]) == Some(RID()),
    ue::is_poll_end_pending(btask_pending()[2]),
    ue::is_poll_begin(btask_ready()[3]),
    ue::is_poll_end(btask_ready()[4]),
    !ue::is_poll_end_pending(btask_ready()[4]),
{
}

// ============================================================================
// Reactor per-index flags
// ============================================================================

// breac1: RegisterTimer@0, Park[Begin]@1, GCT(1)@2, PollEvents@3, Park[End]@4.
pub proof fn breac1_flags(j: int)
  ensures
    j != 0 ==> !rl::is_succ_register_timer_at(breac1(), j),
    rl::is_succ_register_timer_at(breac1(), 0),
    re::get_register_timer_rid(breac1()[0]) == RID(),
    re::get_register_timer_deadline(breac1()[0]) == DL(),
    re::get_register_timer_waker(breac1()[0]) == WK(),
    !rl::is_deregister_timer_at(breac1(), j),
    !rl::io_syscall_registered_at(breac1(), j),
    !rl::io_syscall_register_at(breac1(), j),
    !rl::io_syscall_deregistered_at(breac1(), j),
    !rl::is_succ_set_waker_at(breac1(), j),
    !rl::is_set_waker_at(breac1(), j),
    !rl::is_wake_task_at(breac1(), j),
    !rl::is_io_event_ready_at(breac1(), j),
    j != 1 ==> !rl::is_park_begin_at(breac1(), j),
    j != 4 ==> !rl::is_park_end_at(breac1(), j),
    j != 2 ==> !rl::is_get_current_time_at(breac1(), j),
{
  breac1_idx();
  if j == 0 {
  } else if j == 1 {
  } else if j == 2 {
  } else if j == 3 {
  } else if j == 4 {
  } else {
  }
}

// breac2: as breac1 for [0,5); Park[Begin]@5, GCT(2)@6, PollEvents@7, WakeTask@8, Park[End]@9.
pub proof fn breac2_flags(j: int)
  ensures
    j != 0 ==> !rl::is_succ_register_timer_at(breac2(), j),
    rl::is_succ_register_timer_at(breac2(), 0),
    re::get_register_timer_rid(breac2()[0]) == RID(),
    re::get_register_timer_deadline(breac2()[0]) == DL(),
    re::get_register_timer_waker(breac2()[0]) == WK(),
    !rl::is_deregister_timer_at(breac2(), j),
    !rl::io_syscall_registered_at(breac2(), j),
    !rl::io_syscall_register_at(breac2(), j),
    !rl::io_syscall_deregistered_at(breac2(), j),
    !rl::is_succ_set_waker_at(breac2(), j),
    !rl::is_set_waker_at(breac2(), j),
    j != 8 ==> !rl::is_wake_task_at(breac2(), j),
    rl::is_wake_task_at(breac2(), 8),
    re::get_wake_task_source_rid(breac2()[8]) == RID(),
    re::get_wake_task_waker(breac2()[8]) == WK(),
    !rl::is_io_event_ready_at(breac2(), j),
    (j != 1 && j != 5) ==> !rl::is_park_begin_at(breac2(), j),
    (j != 4 && j != 9) ==> !rl::is_park_end_at(breac2(), j),
    (j != 2 && j != 6) ==> !rl::is_get_current_time_at(breac2(), j),
{
  breac2_idx();
  breac1_idx();
  if 0 <= j < 5 {
    assert(breac2()[j] == breac1()[j]);
    breac1_flags(j);
  } else if j == 5 {
  } else if j == 6 {
  } else if j == 7 {
  } else if j == 8 {
  } else if j == 9 {
  } else {
  }
}

// ============================================================================
// reactor_inv(breac1) and reactor_inv(breac2)
// ============================================================================

// The 12 action-safety properties whose acceptance never fires on breac1/breac2
// beyond the timer register (@0) and the wake (@8, breac2 only): io/set_waker/
// ready families + the io-side halves. Parameterised over the log via the flag fn.
#[verifier::rlimit(50)]
proof fn breac1_vacuous_as()
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_ready_in_park::io_ready_in_park(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_waker_validity::timer_waker_validity(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_waker_validity::io_waker_validity(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::wake_has_registration::wake_has_registration(), breac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::set_waker_active_io::set_waker_active_io(), breac1()),
{
  let l = breac1();
  let p2 = crate::reactor::invariants::io_ready_in_park::io_ready_in_park();
  assert(crate::framework::action_safety::action_safety_satisfied(p2, l)) by {
    assert forall |i: int| #[trigger] (p2.acceptance)(l, i) implies (p2.validity)(l, i) by { breac1_flags(i); } }
  let p3 = crate::reactor::invariants::timer_waker_validity::timer_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p3, l)) by {
    assert forall |i: int| #[trigger] (p3.acceptance)(l, i) implies (p3.validity)(l, i) by { breac1_flags(i); } }
  let p4 = crate::reactor::invariants::io_waker_validity::io_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p4, l)) by {
    assert forall |i: int| #[trigger] (p4.acceptance)(l, i) implies (p4.validity)(l, i) by { breac1_flags(i); } }
  let p6 = crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p6, l)) by {
    assert forall |i: int| #[trigger] (p6.acceptance)(l, i) implies (p6.validity)(l, i) by { breac1_flags(i); } }
  let p8 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p8, l)) by {
    assert forall |i: int| #[trigger] (p8.acceptance)(l, i) implies (p8.validity)(l, i) by { breac1_flags(i); } }
  let p9 = crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p9, l)) by {
    assert forall |i: int| #[trigger] (p9.acceptance)(l, i) implies (p9.validity)(l, i) by { breac1_flags(i); } }
  let p10 = crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p10, l)) by {
    assert forall |i: int| #[trigger] (p10.acceptance)(l, i) implies (p10.validity)(l, i) by { breac1_flags(i); } }
  let p11 = crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p11, l)) by {
    assert forall |i: int| #[trigger] (p11.acceptance)(l, i) implies (p11.validity)(l, i) by { breac1_flags(i); } }
  let p12 = crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p12, l)) by {
    assert forall |i: int| #[trigger] (p12.acceptance)(l, i) implies (p12.validity)(l, i) by { breac1_flags(i); } }
  let p13 = crate::reactor::invariants::wake_has_registration::wake_has_registration();
  assert(crate::framework::action_safety::action_safety_satisfied(p13, l)) by {
    assert forall |i: int| #[trigger] (p13.acceptance)(l, i) implies (p13.validity)(l, i) by { breac1_flags(i); } }
  let p14 = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p14, l)) by {
    assert forall |i: int| #[trigger] (p14.acceptance)(l, i) implies (p14.validity)(l, i) by { breac1_flags(i); } }
}

pub proof fn breac1_reac_inv()
  ensures
    crate::reactor::invariants::reactor_inv(breac1()),
{
  let l = breac1();
  breac1_idx();

  // park_has_timestamp: park end @4, GCT @2 in cycle [1,5).
  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      breac1_flags(i);
      if i == 4 {
        assert(rl::current_park_start(l, 2) == 1);
        assert(rl::current_park_start(l, 3) == 1);
        assert(rl::current_park_start(l, 4) == 1);
        assert(rl::is_get_current_time_at(l, 2));
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 4));
      }
    }
  }
  // park_poll_once: one PollEvents @3.
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      breac1_flags(i);
      if i == 4 {
        assert(rl::current_park_start(l, 2) == 1);
        assert(rl::current_park_start(l, 3) == 1);
        assert(rl::current_park_start(l, 4) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 4, 4) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 3, 4) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 2, 4) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 1, 4) == 1);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, 4));
      }
    }
  }
  // timer_deadline_future @0: deadline 2 > max_timestamp_up_to(l, 0) = 0.
  let p_tdf = crate::reactor::invariants::timer_deadline_future::timer_deadline_future();
  assert(crate::framework::action_safety::action_safety_satisfied(p_tdf, l)) by {
    assert forall |i: int| #[trigger] (p_tdf.acceptance)(l, i) implies (p_tdf.validity)(l, i) by {
      breac1_flags(i);
      if i == 0 {
        assert(rl::max_timestamp_up_to(l, 0) == 0);
      }
    }
  }
  // timer_reg_uniqueness @0: no prior registration.
  let p_tru = crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p_tru, l)) by {
    assert forall |i: int| #[trigger] (p_tru.acceptance)(l, i) implies (p_tru.validity)(l, i) by {
      breac1_flags(i);
      if i == 0 {
        crate::reactor::invariants::timer_reg_uniqueness::intro_no_prior_timer_registration(l, RID(), 0);
      }
    }
  }
  // timer_io_disjoint_at_timer @0: no io registration for rid.
  let p_tid = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer();
  assert(crate::framework::action_safety::action_safety_satisfied(p_tid, l)) by {
    assert forall |i: int| #[trigger] (p_tid.acceptance)(l, i) implies (p_tid.validity)(l, i) by {
      breac1_flags(i);
      if i == 0 {
        crate::reactor::invariants::timer_io_disjoint::intro_no_io_syscall_registration_with_rid(l, RID(), 0);
      }
    }
  }
  breac1_vacuous_as();

  // local liveness: wake_on_expired acceptance false (no timeout: clock 1 < deadline 2).
  let q1 = crate::reactor::invariants::wake_on_expired::wake_on_expired();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q1, l)) by {
    assert forall |i: int| #[trigger] (q1.acceptance)(l, i) implies
      exists |j: int| #![trigger (q1.fulfillment)(l, i, j)]
        j > i && (q1.fulfillment)(l, i, j) && (q1.timely)(l, i, j) by {
      breac1_flags(i);
      if i == 0 {
        // no timeout point: the only GCT (idx 2) has ts 1 < deadline 2.
        use crate::reactor::invariants::wake_on_expired::{find_first_timeout_point_from, has_timeout_point_at, has_first_timeout_point};
        assert(!has_timeout_point_at(l, 0, 2)) by { assert(re::get_current_timestamp(l[2]) == 1); }
        assert(find_first_timeout_point_from(l, 0, 5) == -1);
        assert(find_first_timeout_point_from(l, 0, 4) == -1);
        assert(find_first_timeout_point_from(l, 0, 3) == -1);
        assert(find_first_timeout_point_from(l, 0, 2) == -1);
        assert(find_first_timeout_point_from(l, 0, 1) == -1);
        assert(!has_first_timeout_point(l, 0));
      }
    }
  }
  let q2 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_readable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q2, l)) by {
    assert forall |i: int| #[trigger] (q2.acceptance)(l, i) implies
      exists |j: int| #![trigger (q2.fulfillment)(l, i, j)]
        j > i && (q2.fulfillment)(l, i, j) && (q2.timely)(l, i, j) by { breac1_flags(i); } }
  let q3 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_writable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q3, l)) by {
    assert forall |i: int| #[trigger] (q3.acceptance)(l, i) implies
      exists |j: int| #![trigger (q3.fulfillment)(l, i, j)]
        j > i && (q3.fulfillment)(l, i, j) && (q3.timely)(l, i, j) by { breac1_flags(i); } }
}

// io-family action-safety that stays vacuous on breac2 (no io/set_waker/ready).
#[verifier::rlimit(50)]
proof fn breac2_vacuous_as()
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_ready_in_park::io_ready_in_park(), breac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_waker_validity::io_waker_validity(), breac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness(), breac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io(), breac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle(), breac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle(), breac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result(), breac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result(), breac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::set_waker_active_io::set_waker_active_io(), breac2()),
{
  let l = breac2();
  let p2 = crate::reactor::invariants::io_ready_in_park::io_ready_in_park();
  assert(crate::framework::action_safety::action_safety_satisfied(p2, l)) by {
    assert forall |i: int| #[trigger] (p2.acceptance)(l, i) implies (p2.validity)(l, i) by { breac2_flags(i); } }
  let p4 = crate::reactor::invariants::io_waker_validity::io_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p4, l)) by {
    assert forall |i: int| #[trigger] (p4.acceptance)(l, i) implies (p4.validity)(l, i) by { breac2_flags(i); } }
  let p6 = crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p6, l)) by {
    assert forall |i: int| #[trigger] (p6.acceptance)(l, i) implies (p6.validity)(l, i) by { breac2_flags(i); } }
  let p8 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p8, l)) by {
    assert forall |i: int| #[trigger] (p8.acceptance)(l, i) implies (p8.validity)(l, i) by { breac2_flags(i); } }
  let p9 = crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p9, l)) by {
    assert forall |i: int| #[trigger] (p9.acceptance)(l, i) implies (p9.validity)(l, i) by { breac2_flags(i); } }
  let p10 = crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p10, l)) by {
    assert forall |i: int| #[trigger] (p10.acceptance)(l, i) implies (p10.validity)(l, i) by { breac2_flags(i); } }
  let p11 = crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p11, l)) by {
    assert forall |i: int| #[trigger] (p11.acceptance)(l, i) implies (p11.validity)(l, i) by { breac2_flags(i); } }
  let p12 = crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p12, l)) by {
    assert forall |i: int| #[trigger] (p12.acceptance)(l, i) implies (p12.validity)(l, i) by { breac2_flags(i); } }
  let p14 = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p14, l)) by {
    assert forall |i: int| #[trigger] (p14.acceptance)(l, i) implies (p14.validity)(l, i) by { breac2_flags(i); } }
}

// timer_active_at(breac2, 0, 8): no retire in (0,8) — no deregister, no rid-wake
// (the only wake is at 8, not in the open interval).
proof fn breac2_timer_active_to_wake()
  ensures
    rl::timer_active_at(breac2(), 0, 8),
{
  let l = breac2();
  assert forall |m: int| 0 < m < 8 implies !rl::timer_retired_at(l, RID(), m) by {
    breac2_flags(m);
    if rl::timer_retired_at(l, RID(), m) {
      rl::reveal_timer_retired_implies(l, RID(), m);
    }
  }
}

pub proof fn breac2_reac_inv()
  ensures
    crate::reactor::invariants::reactor_inv(breac2()),
{
  let l = breac2();
  breac2_idx();

  // park_has_timestamp: park ends @4 (GCT @2) and @9 (GCT @6).
  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      breac2_flags(i);
      if i == 4 {
        assert(rl::current_park_start(l, 2) == 1);
        assert(rl::current_park_start(l, 3) == 1);
        assert(rl::current_park_start(l, 4) == 1);
        assert(rl::is_get_current_time_at(l, 2));
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 4));
      } else if i == 9 {
        assert(rl::current_park_start(l, 6) == 5);
        assert(rl::current_park_start(l, 7) == 5);
        assert(rl::current_park_start(l, 8) == 5);
        assert(rl::current_park_start(l, 9) == 5);
        assert(rl::is_get_current_time_at(l, 6));
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 9));
      }
    }
  }
  // park_poll_once: PollEvents @3 and @7.
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      breac2_flags(i);
      if i == 4 {
        assert(rl::current_park_start(l, 2) == 1);
        assert(rl::current_park_start(l, 3) == 1);
        assert(rl::current_park_start(l, 4) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 4, 4) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 3, 4) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 2, 4) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 1, 4) == 1);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, 4));
      } else if i == 9 {
        assert(rl::current_park_start(l, 6) == 5);
        assert(rl::current_park_start(l, 7) == 5);
        assert(rl::current_park_start(l, 8) == 5);
        assert(rl::current_park_start(l, 9) == 5);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 9, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 8, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 7, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 6, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 5, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, 9));
      }
    }
  }
  // timer_deadline_future @0.
  let p_tdf = crate::reactor::invariants::timer_deadline_future::timer_deadline_future();
  assert(crate::framework::action_safety::action_safety_satisfied(p_tdf, l)) by {
    assert forall |i: int| #[trigger] (p_tdf.acceptance)(l, i) implies (p_tdf.validity)(l, i) by {
      breac2_flags(i);
      if i == 0 { assert(rl::max_timestamp_up_to(l, 0) == 0); }
    }
  }
  // timer_reg_uniqueness @0.
  let p_tru = crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p_tru, l)) by {
    assert forall |i: int| #[trigger] (p_tru.acceptance)(l, i) implies (p_tru.validity)(l, i) by {
      breac2_flags(i);
      if i == 0 {
        crate::reactor::invariants::timer_reg_uniqueness::intro_no_prior_timer_registration(l, RID(), 0);
      }
    }
  }
  // timer_io_disjoint_at_timer @0.
  let p_tid = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer();
  assert(crate::framework::action_safety::action_safety_satisfied(p_tid, l)) by {
    assert forall |i: int| #[trigger] (p_tid.acceptance)(l, i) implies (p_tid.validity)(l, i) by {
      breac2_flags(i);
      if i == 0 {
        crate::reactor::invariants::timer_io_disjoint::intro_no_io_syscall_registration_with_rid(l, RID(), 0);
      }
    }
  }
  // timer_waker_validity @8: the wake is ours (register @0, matching waker, active).
  breac2_timer_active_to_wake();
  let p_twv = crate::reactor::invariants::timer_waker_validity::timer_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p_twv, l)) by {
    assert forall |i: int| #[trigger] (p_twv.acceptance)(l, i) implies (p_twv.validity)(l, i) by {
      breac2_flags(i);
      if i == 8 {
        assert(rl::is_succ_register_timer_at(l, 0) &&
          re::get_register_timer_rid(l[0]) == re::get_wake_task_source_rid(l[8]) &&
          re::get_register_timer_waker(l[0]) == re::get_wake_task_waker(l[8]) &&
          rl::timer_active_at(l, 0, 8));
      }
    }
  }
  // wake_has_registration @8: register @0 precedes the wake for rid.
  let p_whr = crate::reactor::invariants::wake_has_registration::wake_has_registration();
  assert(crate::framework::action_safety::action_safety_satisfied(p_whr, l)) by {
    assert forall |i: int| #[trigger] (p_whr.acceptance)(l, i) implies (p_whr.validity)(l, i) by {
      breac2_flags(i);
      if i == 8 {
        assert(0 <= 0 < 8 && rl::is_succ_register_timer_at(l, 0) &&
          re::get_register_timer_rid(l[0]) == re::get_wake_task_source_rid(l[8]));
      }
    }
  }
  breac2_vacuous_as();

  // local liveness: wake_on_expired acceptance false — timer_awaiting_wake(0) is
  // false because a wake for rid exists at 8.
  let q1 = crate::reactor::invariants::wake_on_expired::wake_on_expired();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q1, l)) by {
    assert forall |i: int| #[trigger] (q1.acceptance)(l, i) implies
      exists |j: int| #![trigger (q1.fulfillment)(l, i, j)]
        j > i && (q1.fulfillment)(l, i, j) && (q1.timely)(l, i, j) by {
      breac2_flags(i);
      if i == 0 {
        assert(rl::is_wake_task_at(l, 8) && re::get_wake_task_source_rid(l[8]) ==
          re::get_register_timer_rid(l[0]));
        assert(!crate::reactor::invariants::wake_on_expired::timer_awaiting_wake(l, 0));
      }
    }
  }
  let q2 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_readable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q2, l)) by {
    assert forall |i: int| #[trigger] (q2.acceptance)(l, i) implies
      exists |j: int| #![trigger (q2.fulfillment)(l, i, j)]
        j > i && (q2.fulfillment)(l, i, j) && (q2.timely)(l, i, j) by { breac2_flags(i); } }
  let q3 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_writable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q3, l)) by {
    assert forall |i: int| #[trigger] (q3.acceptance)(l, i) implies
      exists |j: int| #![trigger (q3.fulfillment)(l, i, j)]
        j > i && (q3.fulfillment)(l, i, j) && (q3.timely)(l, i, j) by { breac2_flags(i); } }
}

// reactor_progress ∅ → breac1: RegisterTimer@0 is inbound-non-park (before the
// cycle), then the complete park cycle [1, 5).
pub proof fn breac1_reac_progress()
  ensures
    crate::reactor::reactor_progress(Seq::<re::ReactorEvent>::empty(), breac1()),
{
  let l = breac1();
  breac1_idx();
  breac1_reac_inv();
  assert(Seq::<re::ReactorEvent>::empty() =~= l.subrange(0, 0));
  assert(crate::reactor::is_complete_park_cycle(l, 1, 5)) by {
    assert(rl::is_park_begin_at(l, 1));
    assert(rl::is_park_end_at(l, 4));
    assert forall |k: int| 1 < k < 4 implies
      !#[trigger] rl::is_park_begin_at(l, k) && !rl::is_park_end_at(l, k) by { breac1_flags(k); }
  }
  assert(exists |ps: int, pe: int|
    0 <= ps && ps < pe && pe <= l.len() &&
    crate::reactor::is_complete_park_cycle(l, ps, pe) &&
    (forall |i: int| 0 <= i < ps ==> re::is_inbound_non_park(#[trigger] l[i])) &&
    (forall |i: int| pe <= i < l.len() ==> re::is_inbound_non_park(#[trigger] l[i]))) by {
    assert(crate::reactor::is_complete_park_cycle(l, 1, 5));
    assert(re::is_inbound_non_park(l[0]));
  }
}

// reactor_progress breac1 → breac2: append the complete park cycle [5, 10)
// (the WakeTask@8 is inside the cycle — is_complete_park_cycle allows it).
pub proof fn breac2_reac_progress()
  ensures
    crate::reactor::reactor_progress(breac1(), breac2()),
{
  let l1 = breac1();
  let l2 = breac2();
  breac2_idx();
  breac1_idx();
  breac2_reac_inv();
  assert(l1 =~= l2.subrange(0, 5));
  assert(crate::reactor::is_complete_park_cycle(l2, 5, 10)) by {
    assert(rl::is_park_begin_at(l2, 5));
    assert(rl::is_park_end_at(l2, 9));
    assert forall |k: int| 5 < k < 9 implies
      !#[trigger] rl::is_park_begin_at(l2, k) && !rl::is_park_end_at(l2, k) by { breac2_flags(k); }
  }
  assert(exists |ps: int, pe: int|
    5 <= ps && ps < pe && pe <= l2.len() &&
    crate::reactor::is_complete_park_cycle(l2, ps, pe) &&
    (forall |i: int| 5 <= i < ps ==> re::is_inbound_non_park(#[trigger] l2[i])) &&
    (forall |i: int| pe <= i < l2.len() ==> re::is_inbound_non_park(#[trigger] l2[i]))) by {
    assert(crate::reactor::is_complete_park_cycle(l2, 5, 10));
  }
}

// ============================================================================
// Executor per-index flags + FIFO queue
// ============================================================================

pub proof fn bexec1_flags(tid: TID, k: int)
  ensures
    k != 0 ==> !el::is_tick_begin_at(bexec1(tid), k),
    k != 7 ==> !el::is_tick_end_at(bexec1(tid), k),
    k != 4 ==> !el::is_park_at(bexec1(tid), k),
    k != 1 ==> !el::is_pop_injection_at(bexec1(tid), k),
    k != 6 ==> !el::is_poll_task_at(bexec1(tid), k),
{
  bexec1_idx(tid);
}

pub proof fn bexec2_flags(tid: TID, k: int)
  ensures
    (k != 0 && k != 8) ==> !el::is_tick_begin_at(bexec2(tid), k),
    (k != 7 && k != 15) ==> !el::is_tick_end_at(bexec2(tid), k),
    (k != 4 && k != 12) ==> !el::is_park_at(bexec2(tid), k),
    (k != 1 && k != 9) ==> !el::is_pop_injection_at(bexec2(tid), k),
    (k != 6 && k != 14) ==> !el::is_poll_task_at(bexec2(tid), k),
{
  bexec2_idx(tid);
  if 0 <= k < 8 { bexec1_idx(tid); }
}

// Queue: pop Some(tid)@1 pushes tid; poll@6 removes it (→ empty); DrainReactorWake
// [tid]@13 pushes it again; poll@14 removes it.
pub proof fn bexec1_queue(tid: TID)
  ensures
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec1(tid), 0) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec1(tid), 6) =~= seq![tid],
    forall |i: int| 2 <= i <= 6 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec1(tid), i) =~= seq![tid],
{
  let l = bexec1(tid);
  bexec1_idx(tid);
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  assert(fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 1) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 2) =~= seq![tid]);
  assert(fifo_queue_at(l, 3) =~= seq![tid]);
  assert(fifo_queue_at(l, 4) =~= seq![tid]);
  assert(fifo_queue_at(l, 5) =~= seq![tid]);
  assert(fifo_queue_at(l, 6) =~= seq![tid]);
  assert forall |i: int| 2 <= i <= 6 implies #[trigger] fifo_queue_at(l, i) =~= seq![tid] by {
    if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {}
  }
}

pub proof fn bexec2_queue(tid: TID)
  ensures
    forall |i: int| 2 <= i <= 6 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec2(tid), i) =~= seq![tid],
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec2(tid), 0) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec2(tid), 6) =~= seq![tid],
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec2(tid), 14) =~= seq![tid],
    forall |i: int| 7 <= i <= 13 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec2(tid), i) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec2(tid), 15) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec2(tid), 16) =~= Seq::<TID>::empty(),
{
  let l = bexec2(tid);
  bexec2_idx(tid);
  bexec1_idx(tid);
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
  assert(fifo_queue_at(l, 12) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 13) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 14) =~= seq![tid]);
  assert(fifo_queue_at(l, 15) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 16) =~= Seq::<TID>::empty());
  assert forall |i: int| 2 <= i <= 6 implies #[trigger] fifo_queue_at(l, i) =~= seq![tid] by {
    if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {}
  }
  assert forall |i: int| 7 <= i <= 13 implies #[trigger] fifo_queue_at(l, i) =~= Seq::<TID>::empty() by {
    if i == 7 {} else if i == 8 {} else if i == 9 {} else if i == 10 {}
    else if i == 11 {} else if i == 12 {} else if i == 13 {}
  }
}

// ============================================================================
// Executor invariant + progress obligations
// ============================================================================

// Per-tick action-safety at the single poll `pi` (Pending or Ready) in a tick
// whose park is `pk`, pop `pp`, drain-deferred `dd`, drain-task-wake `dt`,
// tick-end `te`. Shared by both bexec1 and bexec2's ticks via direct index work.
#[verifier::rlimit(100)]
proof fn bexec1_exec_inv(tid: TID)
  ensures
    crate::executor::invariants::executor_inv(bexec1(tid)),
{
  let l = bexec1(tid);
  bexec1_idx(tid);
  bexec1_queue(tid);
  let p_fifo = crate::executor::invariants::fifo_task_selection::fifo_task_selection();
  assert(crate::framework::action_safety::action_safety_satisfied(p_fifo, l)) by {
    assert forall |i: int| #[trigger] (p_fifo.acceptance)(l, i) implies (p_fifo.validity)(l, i) by {
      bexec1_flags(tid, i);
      if i == 6 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 6, tid)); }
    }
  }
  let p_vtp = crate::executor::invariants::valid_task_polling::valid_task_polling();
  assert(crate::framework::action_safety::action_safety_satisfied(p_vtp, l)) by {
    assert forall |i: int| #[trigger] (p_vtp.acceptance)(l, i) implies (p_vtp.validity)(l, i) by {
      bexec1_flags(tid, i);
      if i == 6 {
        assert(el::is_pop_injection_at(l, 1) && ee::get_pop_injection_task(l[1]).unwrap().id == tid);
        assert(crate::executor::invariants::valid_task_polling::tid_was_injected_before(l, 6, tid));
        assert(!crate::executor::invariants::valid_task_polling::tid_returned_ready_before(l, 6, tid)) by {
          assert forall |j: int| 0 <= j < 6 implies
            !(el::is_poll_task_at(l, j) && ee::get_poll_task_id(l[j]) == tid
              && ee::get_poll_result(l[j]) == crate::executor::spec::types::PollResult::Ready(())) by { bexec1_flags(tid, j); }
        }
        assert(!crate::executor::invariants::valid_task_polling::tid_is_invalid(l, 6, tid));
      }
    }
  }
  bexec1_tick_structure(tid);
  // local liveness
  let p_pdrw = crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_pdrw, l)) by {
    assert forall |i: int| #[trigger] (p_pdrw.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_pdrw.fulfillment)(l, i, j)]
        j > i && (p_pdrw.fulfillment)(l, i, j) && (p_pdrw.timely)(l, i, j) by {
      bexec1_flags(tid, i);
      if i == 4 {
        assert(el::is_drain_reactor_wake_at(l, 5));
        assert forall |k: int| 4 < k < 5 implies !#[trigger] el::is_tick_end_at(l, k) by { bexec1_flags(tid, k); }
        assert(5 > 4 && (p_pdrw.fulfillment)(l, 4, 5) && (p_pdrw.timely)(l, 4, 5));
      }
    }
  }
  let p_tpr = crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_tpr, l)) by {
    assert forall |i: int| #[trigger] (p_tpr.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_tpr.fulfillment)(l, i, j)]
        j > i && (p_tpr.fulfillment)(l, i, j) && (p_tpr.timely)(l, i, j) by {
      bexec1_flags(tid, i);
      if i == 0 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
      }
    }
  }
}

// Tick structure (park/pop/drain-deferred/drain-task-wake) at tick-end 7.
proof fn bexec1_tick_structure(tid: TID)
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_park::tick_has_park(), bexec1(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection(), bexec1(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred(), bexec1(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake(), bexec1(tid)),
{
  let l = bexec1(tid);
  bexec1_idx(tid);
  let pk = crate::executor::invariants::tick_has_park::tick_has_park();
  assert(crate::framework::action_safety::action_safety_satisfied(pk, l)) by {
    assert forall |i: int| #[trigger] (pk.acceptance)(l, i) implies (pk.validity)(l, i) by {
      bexec1_flags(tid, i);
      if i == 7 { assert(el::is_park_at(l, 4)); assert forall |k: int| 4 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec1_flags(tid, k); } }
    } }
  let pp = crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection();
  assert(crate::framework::action_safety::action_safety_satisfied(pp, l)) by {
    assert forall |i: int| #[trigger] (pp.acceptance)(l, i) implies (pp.validity)(l, i) by {
      bexec1_flags(tid, i);
      if i == 7 { assert(el::is_pop_injection_at(l, 1)); assert forall |k: int| 1 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec1_flags(tid, k); } }
    } }
  let dd = crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred();
  assert(crate::framework::action_safety::action_safety_satisfied(dd, l)) by {
    assert forall |i: int| #[trigger] (dd.acceptance)(l, i) implies (dd.validity)(l, i) by {
      bexec1_flags(tid, i);
      if i == 7 { assert(el::is_drain_deferred_at(l, 2)); assert forall |k: int| 2 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec1_flags(tid, k); } }
    } }
  let dt = crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake();
  assert(crate::framework::action_safety::action_safety_satisfied(dt, l)) by {
    assert forall |i: int| #[trigger] (dt.acceptance)(l, i) implies (dt.validity)(l, i) by {
      bexec1_flags(tid, i);
      if i == 7 { assert(el::is_drain_task_wake_at(l, 3)); assert forall |k: int| 3 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec1_flags(tid, k); } }
    } }
}

pub proof fn bexec1_exec_progress(tid: TID)
  ensures
    crate::executor::executor_progress(Seq::<ee::ExecutorEvent>::empty(), bexec1(tid)),
{
  let l = bexec1(tid);
  bexec1_idx(tid);
  bexec1_exec_inv(tid);
  assert(Seq::<ee::ExecutorEvent>::empty() =~= l.subrange(0, 0));
  assert(crate::executor::is_complete_tick_cycle(l, 0, 8)) by {
    assert(el::is_tick_begin_at(l, 0));
    assert(el::is_tick_end_at(l, 7));
    assert forall |k: int| 0 < k < 7 implies
      !#[trigger] el::is_tick_begin_at(l, k) && !el::is_tick_end_at(l, k) by { bexec1_flags(tid, k); }
  }
}

// Tick structure for bexec2 (two ticks: ends @7 with park@4/pop@1/dd@2/dt@3;
// end @15 with park@12/pop@9/dd@10/dt@11).
proof fn bexec2_tick_structure(tid: TID)
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_park::tick_has_park(), bexec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection(), bexec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred(), bexec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake(), bexec2(tid)),
{
  let l = bexec2(tid);
  bexec2_idx(tid);
  let pk = crate::executor::invariants::tick_has_park::tick_has_park();
  assert(crate::framework::action_safety::action_safety_satisfied(pk, l)) by {
    assert forall |i: int| #[trigger] (pk.acceptance)(l, i) implies (pk.validity)(l, i) by {
      bexec2_flags(tid, i);
      if i == 7 { assert(el::is_park_at(l, 4)); assert forall |k: int| 4 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_park_at(l, 12)); assert forall |k: int| 12 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec2_flags(tid, k); } }
    } }
  let pp = crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection();
  assert(crate::framework::action_safety::action_safety_satisfied(pp, l)) by {
    assert forall |i: int| #[trigger] (pp.acceptance)(l, i) implies (pp.validity)(l, i) by {
      bexec2_flags(tid, i);
      if i == 7 { assert(el::is_pop_injection_at(l, 1)); assert forall |k: int| 1 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_pop_injection_at(l, 9)); assert forall |k: int| 9 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec2_flags(tid, k); } }
    } }
  let dd = crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred();
  assert(crate::framework::action_safety::action_safety_satisfied(dd, l)) by {
    assert forall |i: int| #[trigger] (dd.acceptance)(l, i) implies (dd.validity)(l, i) by {
      bexec2_flags(tid, i);
      if i == 7 { assert(el::is_drain_deferred_at(l, 2)); assert forall |k: int| 2 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_drain_deferred_at(l, 10)); assert forall |k: int| 10 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec2_flags(tid, k); } }
    } }
  let dt = crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake();
  assert(crate::framework::action_safety::action_safety_satisfied(dt, l)) by {
    assert forall |i: int| #[trigger] (dt.acceptance)(l, i) implies (dt.validity)(l, i) by {
      bexec2_flags(tid, i);
      if i == 7 { assert(el::is_drain_task_wake_at(l, 3)); assert forall |k: int| 3 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_drain_task_wake_at(l, 11)); assert forall |k: int| 11 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { bexec2_flags(tid, k); } }
    } }
}

#[verifier::rlimit(100)]
pub proof fn bexec2_exec_inv(tid: TID)
  ensures
    crate::executor::invariants::executor_inv(bexec2(tid)),
{
  let l = bexec2(tid);
  bexec2_idx(tid);
  bexec2_queue(tid);
  let p_fifo = crate::executor::invariants::fifo_task_selection::fifo_task_selection();
  assert(crate::framework::action_safety::action_safety_satisfied(p_fifo, l)) by {
    assert forall |i: int| #[trigger] (p_fifo.acceptance)(l, i) implies (p_fifo.validity)(l, i) by {
      bexec2_flags(tid, i);
      if i == 6 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 6, tid)); }
      else if i == 14 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 14, tid)); }
    }
  }
  let p_vtp = crate::executor::invariants::valid_task_polling::valid_task_polling();
  assert(crate::framework::action_safety::action_safety_satisfied(p_vtp, l)) by {
    assert forall |i: int| #[trigger] (p_vtp.acceptance)(l, i) implies (p_vtp.validity)(l, i) by {
      bexec2_flags(tid, i);
      if i == 6 || i == 14 {
        assert(el::is_pop_injection_at(l, 1) && ee::get_pop_injection_task(l[1]).unwrap().id == tid);
        assert(crate::executor::invariants::valid_task_polling::tid_was_injected_before(l, i, tid));
        assert(!crate::executor::invariants::valid_task_polling::tid_returned_ready_before(l, i, tid)) by {
          assert forall |j: int| 0 <= j < i implies
            !(el::is_poll_task_at(l, j) && ee::get_poll_task_id(l[j]) == tid
              && ee::get_poll_result(l[j]) == crate::executor::spec::types::PollResult::Ready(())) by { bexec2_flags(tid, j); }
        }
        assert(!crate::executor::invariants::valid_task_polling::tid_is_invalid(l, i, tid));
      }
    }
  }
  bexec2_tick_structure(tid);
  let p_pdrw = crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_pdrw, l)) by {
    assert forall |i: int| #[trigger] (p_pdrw.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_pdrw.fulfillment)(l, i, j)]
        j > i && (p_pdrw.fulfillment)(l, i, j) && (p_pdrw.timely)(l, i, j) by {
      bexec2_flags(tid, i);
      if i == 4 {
        assert(el::is_drain_reactor_wake_at(l, 5));
        assert forall |k: int| 4 < k < 5 implies !#[trigger] el::is_tick_end_at(l, k) by { bexec2_flags(tid, k); }
        assert(5 > 4 && (p_pdrw.fulfillment)(l, 4, 5) && (p_pdrw.timely)(l, 4, 5));
      } else if i == 12 {
        assert(el::is_drain_reactor_wake_at(l, 13));
        assert forall |k: int| 12 < k < 13 implies !#[trigger] el::is_tick_end_at(l, k) by { bexec2_flags(tid, k); }
        assert(13 > 12 && (p_pdrw.fulfillment)(l, 12, 13) && (p_pdrw.timely)(l, 12, 13));
      }
    }
  }
  let p_tpr = crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_tpr, l)) by {
    assert forall |i: int| #[trigger] (p_tpr.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_tpr.fulfillment)(l, i, j)]
        j > i && (p_tpr.fulfillment)(l, i, j) && (p_tpr.timely)(l, i, j) by {
      bexec2_flags(tid, i);
      if i == 0 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
      } else if i == 8 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 8) =~= Seq::<TID>::empty());
      }
    }
  }
}

pub proof fn bexec2_exec_progress(tid: TID)
  ensures
    crate::executor::executor_progress(bexec1(tid), bexec2(tid)),
{
  let l1 = bexec1(tid);
  let l2 = bexec2(tid);
  bexec2_idx(tid);
  bexec2_exec_inv(tid);
  assert(l1 =~= l2.subrange(0, 8));
  assert(crate::executor::is_complete_tick_cycle(l2, 8, 16)) by {
    assert(el::is_tick_begin_at(l2, 8));
    assert(el::is_tick_end_at(l2, 15));
    assert forall |k: int| 8 < k < 15 implies
      !#[trigger] el::is_tick_begin_at(l2, k) && !el::is_tick_end_at(l2, k) by { bexec2_flags(tid, k); }
  }
}

// ============================================================================
// Cross-module alignment: the ONE timer registration (task btask[1] ⟷ reactor
// breac[0]) is the only non-vacuous mediation; the WakeTask@8 is Outbound (not
// task-initiated) so it needs no source op.
// ============================================================================

// Task-log op classification: only btask[1] (RegisterTimer, rid 7) is a reactor
// operation; the others are poll markers.
pub proof fn btask_op_facts()
  ensures
    forall |i: int| #![trigger btask_ready()[i]] 0 <= i < btask_ready().len() ==>
      (crate::composed::spec::alignment::is_reactor_operation(btask_ready()[i]) <==> i == 1),
    forall |i: int| #![trigger btask_pending()[i]] 0 <= i < btask_pending().len() ==>
      (crate::composed::spec::alignment::is_reactor_operation(btask_pending()[i]) <==> i == 1),
    crate::composed::spec::alignment::is_reactor_operation(btask_pending()[1]),
    !ue::is_deregister_timer(btask_ready()[1]) && !ue::is_register_io(btask_ready()[1]) &&
    !ue::is_deregister_io(btask_ready()[1]) && !ue::is_succ_set_waker(btask_ready()[1]),
{
  btask_idx();
  assert forall |i: int| #![trigger btask_ready()[i]] 0 <= i < btask_ready().len() implies
    (crate::composed::spec::alignment::is_reactor_operation(btask_ready()[i]) <==> i == 1) by {
    if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {}
  }
  assert forall |i: int| #![trigger btask_pending()[i]] 0 <= i < btask_pending().len() implies
    (crate::composed::spec::alignment::is_reactor_operation(btask_pending()[i]) <==> i == 1) by {
    if i == 0 {} else if i == 1 {} else if i == 2 {}
  }
}

// The register@0 (reactor) matches btask[1] (task RegisterTimer, rid 7).
pub proof fn breg_matches(tid: TID)
  ensures
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      breac1()[0], btask_pending()[1]),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      breac2()[0], btask_ready()[1]),
{
  breac1_idx(); breac2_idx(); btask_idx();
}

proof fn bs_am_state(s: ComposedState, tid: TID)
  requires
    s.task_logs.contains_key(tid),
    s.task_logs[tid] == btask_pending() || s.task_logs[tid] == btask_ready(),
    forall |t2: TaskId| s.task_logs.contains_key(t2) ==> t2 == tid,
    s.reactor_log == breac1() || s.reactor_log == breac2(),
  ensures
    crate::composed::spec::alignment::action_mediation_state(s),
{
  breac1_idx(); breac2_idx(); btask_idx(); btask_op_facts(); breg_matches(tid);
  use crate::composed::spec::alignment::*;
  // operation_to_reactor_exists: the only reactor op is btask[1] → reactor @0.
  assert(operation_to_reactor_exists(s)) by {
    assert forall |t2: TaskId, i: int|
      s.task_logs.contains_key(t2) && 0 <= i < s.task_logs[t2].len() &&
      is_reactor_operation(#[trigger] s.task_logs[t2][i])
      implies exists |j: int| 0 <= j < s.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][i]) by {
      assert(t2 == tid);
      assert(i == 1);
      assert(0 <= 0 < s.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[0], s.task_logs[t2][1]));
    }
  }
  // reactor_registration_to_task_exists + reactor_outbound_to_task_exists: reg @0 → btask[1].
  assert(reactor_registration_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() &&
      (re::is_succ_register_timer(s.reactor_log[j]) || re::is_succ_io_syscall_register(s.reactor_log[j]))
      implies exists |t2: TaskId, ti: int| s.task_logs.contains_key(t2) &&
        0 <= ti < s.task_logs[t2].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][ti]) by {
      assert(j == 0);
      assert(s.task_logs.contains_key(tid) && 0 <= 1 < s.task_logs[tid].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[0], s.task_logs[tid][1]));
    }
  }
  assert(reactor_outbound_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() && is_task_initiated_reactor_event(s.reactor_log[j])
      implies exists |t2: TaskId, ti: int| s.task_logs.contains_key(t2) &&
        0 <= ti < s.task_logs[t2].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][ti]) by {
      assert(j == 0);
      assert(s.task_logs.contains_key(tid) && 0 <= 1 < s.task_logs[tid].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[0], s.task_logs[tid][1]));
    }
  }
  // reactor_to_operation_unique: the sole reactor op maps to the sole reactor event.
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
      assert(t1 == tid && t2 == tid && ti1 == 1 && ti2 == 1);
    }
  }
  monotonic_alignment_holds_single(s, tid);
  assert(succ_deregister_by_owner(s)) by { reveal(succ_deregister_by_owner); }
  assert(deregister_matches_own_registration(s)) by { reveal(deregister_matches_own_registration); }
  assert(deregister_io_matches_own_registration(s)) by { reveal(deregister_io_matches_own_registration); }
  assert(succ_deregister_io_by_owner(s)) by { reveal(succ_deregister_io_by_owner); }
}

// monotonic_task_reactor_alignment for a state with a single reactor op.
pub proof fn monotonic_alignment_holds_single(s: ComposedState, tid: TID)
  requires
    s.task_logs.contains_key(tid),
    s.task_logs[tid] == btask_pending() || s.task_logs[tid] == btask_ready(),
    forall |t2: TaskId| s.task_logs.contains_key(t2) ==> t2 == tid,
  ensures
    crate::composed::spec::alignment::monotonic_task_reactor_alignment(s),
{
  btask_idx(); btask_op_facts();
  use crate::composed::spec::alignment::*;
  // only index 1 is a reactor op ⟹ no two distinct reactor ops in a task log.
  assert forall |t2: TaskId, a: int, b: int|
    #![trigger s.task_logs[t2][a], s.task_logs[t2][b]]
    s.task_logs.contains_key(t2) && 0 <= a < b < s.task_logs[t2].len() &&
    is_reactor_operation(s.task_logs[t2][a])
    implies !is_reactor_operation(s.task_logs[t2][b]) by {
    assert(t2 == tid);
    assert(a == 1);  // the only reactor op
  }
  monotonic_alignment_holds_no_two_ops(s);
}

// ============================================================================
// cross_module_alignment for both steps
// ============================================================================

#[verifier::rlimit(100)]
pub proof fn bs1_cross(tid: TID)
  ensures
    cross_module_alignment(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bs1(tid)),
{
  reveal(cross_module_alignment);
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = bs1(tid);
  bexec1_idx(tid); breac1_idx(); btask_idx(); btask_op_facts(); breg_matches(tid);
  use crate::composed::spec::alignment::*;

  bs_am_state(s2, tid);
  // action_mediation_step: the new register@0 ⟷ the new task op btask[1].
  assert(is_new_task_operation(s, s2, tid, 1));
  assert(action_mediation_step(s, s2)) by {
    assert(new_operation_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int|
        is_new_task_operation(s, s2, t2, i) && is_reactor_operation(#[trigger] s2.task_logs[t2][i])
        implies exists |j: int| s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][i]) by {
        assert(t2 == tid && i == 1);
        assert(0 <= 0 < s2.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[0], s2.task_logs[tid][1]));
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
        implies t1 == t2 && a1 == a2 by { assert(t1 == tid && t2 == tid && a1 == 1 && a2 == 1); }
    }
    assert(new_op_matches_only_new_reactor(s, s2)) by {
      assert forall |t2: TaskId, ti: int, ri: int|
        is_new_task_operation(s, s2, t2, ti) && is_reactor_operation(#[trigger] s2.task_logs[t2][ti]) &&
        0 <= ri < s2.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(#[trigger] s2.reactor_log[ri], s2.task_logs[t2][ti])
        implies ri >= s.reactor_log.len() by { assert(t2 == tid && ti == 1); }
    }
    assert(reactor_outbound_has_task_operation(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          0 <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by {
        assert(j == 0);
        assert(s2.task_logs.contains_key(tid) && 0 <= 1 < s2.task_logs[tid].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[0], s2.task_logs[tid][1]));
      }
    }
    assert(new_reactor_event_has_new_op(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          (if s.task_logs.contains_key(t2) { s.task_logs[t2].len() as int } else { 0int })
            <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by {
        assert(j == 0);
        assert(!s.task_logs.contains_key(tid));
        assert(s2.task_logs.contains_key(tid) && 0int <= 1 < s2.task_logs[tid].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[0], s2.task_logs[tid][1]));
      }
    }
  }
  bs1_obs_consistency(tid);
  bs1_park_alignment(tid);
}

// Observation consistency for step s0 → bs1 (poll@6 Pending).
proof fn bs1_obs_consistency(tid: TID)
  ensures
    observation_consistency_state(bs1(tid)),
    observation_consistency_step(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bs1(tid)),
{
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = bs1(tid);
  bexec1_idx(tid); btask_idx();
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
        assert(s2.task_logs[tid] == btask_pending());
        assert(ue::is_poll_end_pending(btask_pending()[2]));
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
        assert(s2.task_logs[tid] == btask_pending());
        assert(ue::is_poll_end_pending(btask_pending()[2]));
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

proof fn bs1_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bs1(tid)),
{
  let s2 = bs1(tid);
  bexec1_idx(tid); breac1_idx();
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
  let r = breac1();
  assert(count_park_cycles_in(r, 5, 5) == 0);
  assert(count_park_cycles_in(r, 4, 5) == 1) by { breac1_flags(4); }
  assert(count_park_cycles_in(r, 3, 5) == 1) by { breac1_flags(3); }
  assert(count_park_cycles_in(r, 2, 5) == 1) by { breac1_flags(2); }
  assert(count_park_cycles_in(r, 1, 5) == 1) by { breac1_flags(1); }
  assert(count_park_cycles_in(r, 0, 5) == 1) by { breac1_flags(0); }
}

#[verifier::rlimit(100)]
pub proof fn bs2_cross(tid: TID)
  ensures
    cross_module_alignment(bs1(tid), bs2(tid)),
{
  reveal(cross_module_alignment);
  let s = bs1(tid);
  let s2 = bs2(tid);
  bexec2_idx(tid); breac2_idx(); btask_idx(); btask_op_facts(); breg_matches(tid);
  use crate::composed::spec::alignment::*;

  bs_am_state(s2, tid);
  // action_mediation_step: no NEW task-initiated reactor events (WakeTask@8 is
  // Outbound) and no NEW reactor-op task ops (btask[3,4] are poll markers).
  assert(action_mediation_step(s, s2)) by {
    assert(new_operation_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int|
        is_new_task_operation(s, s2, t2, i) && is_reactor_operation(#[trigger] s2.task_logs[t2][i])
        implies exists |j: int| s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][i]) by {
        assert(t2 == tid);
        assert(i == 3 || i == 4);  // the only new task ops — neither a reactor op
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
        implies t1 == t2 && a1 == a2 by { assert(t1 == tid && (a1 == 3 || a1 == 4)); }
    }
    assert(new_op_matches_only_new_reactor(s, s2)) by {
      assert forall |t2: TaskId, ti: int, ri: int|
        is_new_task_operation(s, s2, t2, ti) && is_reactor_operation(#[trigger] s2.task_logs[t2][ti]) &&
        0 <= ri < s2.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(#[trigger] s2.reactor_log[ri], s2.task_logs[t2][ti])
        implies ri >= s.reactor_log.len() by { assert(t2 == tid && (ti == 3 || ti == 4)); }
    }
    assert(reactor_outbound_has_task_operation(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          0 <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by {
        breac2_flags(j);  // 5≤j<10: none is task-initiated (Park/GCT/PollEvents/WakeTask)
      }
    }
    assert(new_reactor_event_has_new_op(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          (if s.task_logs.contains_key(t2) { s.task_logs[t2].len() as int } else { 0int })
            <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by {
        breac2_flags(j);
      }
    }
  }
  bs2_obs_consistency(tid);
  bs2_park_alignment(tid);
}

proof fn bs2_obs_consistency(tid: TID)
  ensures
    observation_consistency_state(bs2(tid)),
    observation_consistency_step(bs1(tid), bs2(tid)),
{
  let s = bs1(tid);
  let s2 = bs2(tid);
  bexec2_idx(tid); bexec1_idx(tid); btask_idx();
  use crate::composed::spec::alignment::*;
  assert(observation_consistency_state(s2)) by {
    assert(polled_task_has_log_inv(s2)) by {
      assert forall |t2: TaskId| el::has_poll_for_id(s2.executor_log, t2) implies s2.task_logs.contains_key(t2) by {
        if !s2.task_logs.contains_key(t2) {
          assert forall |i: int| #![trigger s2.executor_log[i]] 0 <= i < s2.executor_log.len()
            implies !el::is_poll_task_for_id_at(s2.executor_log, i, t2) by { bexec2_flags(tid, i); }
        }
      }
    }
    assert(pending_poll_inv(s2)) by {
      assert forall |t2: TaskId| #![trigger s2.task_logs[t2]]
        s2.task_logs.contains_key(t2) && el::last_poll_is_pending(s2.executor_log, t2)
        implies task_log_ends_with_pending(s2.task_logs[t2]) by {
        // last poll of tid in bexec2 is @14 (Ready) ⟹ last_poll_is_pending is false
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
        implies task_log_ends_with_pending(s2.task_logs[t2]) by {
        bexec2_flags(tid, i);  // the only new poll (@14) is Ready, not Pending ⟹ vacuous
      }
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
        assert(s.task_logs[tid] == btask_pending() && s2.task_logs[tid] == btask_ready());
      }
    }
  }
}

proof fn bs2_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(bs1(tid), bs2(tid)),
{
  bexec2_idx(tid); breac2_idx();
  use crate::composed::spec::alignment::*;
  let e = bexec2(tid);
  assert(count_park_events_in(e, 16, 16) == 0);
  assert(count_park_events_in(e, 15, 16) == 0) by { bexec2_flags(tid, 15); }
  assert(count_park_events_in(e, 14, 16) == 0) by { bexec2_flags(tid, 14); }
  assert(count_park_events_in(e, 13, 16) == 0) by { bexec2_flags(tid, 13); }
  assert(count_park_events_in(e, 12, 16) == 1) by { bexec2_flags(tid, 12); }
  assert(count_park_events_in(e, 11, 16) == 1) by { bexec2_flags(tid, 11); }
  assert(count_park_events_in(e, 10, 16) == 1) by { bexec2_flags(tid, 10); }
  assert(count_park_events_in(e, 9, 16) == 1) by { bexec2_flags(tid, 9); }
  assert(count_park_events_in(e, 8, 16) == 1) by { bexec2_flags(tid, 8); }
  let r = breac2();
  assert(count_park_cycles_in(r, 10, 10) == 0);
  assert(count_park_cycles_in(r, 9, 10) == 1) by { breac2_flags(9); }
  assert(count_park_cycles_in(r, 8, 10) == 1) by { breac2_flags(8); }
  assert(count_park_cycles_in(r, 7, 10) == 1) by { breac2_flags(7); }
  assert(count_park_cycles_in(r, 6, 10) == 1) by { breac2_flags(6); }
  assert(count_park_cycles_in(r, 5, 10) == 1) by { breac2_flags(5); }
}

// ============================================================================
// utilities_inv, injection schedule, and composed_progress assembly
// ============================================================================

pub proof fn btask_utilities_inv()
  ensures
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(btask_pending()),
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(btask_ready()),
{
  btask_idx();
  use crate::utilities::invariants::wakeup_guarantee::*;
  // btask_pending: PollEnd(Pending)@2 has the timer source (register@1, current poll).
  let wg = wakeup_guarantee();
  let ro = crate::utilities::invariants::resource_ownership::resource_ownership();
  assert(crate::framework::action_safety::action_safety_satisfied(wg, btask_pending())) by {
    assert forall |i: int| #[trigger] (wg.acceptance)(btask_pending(), i) implies (wg.validity)(btask_pending(), i) by {
      if i == 2 {
        assert(crate::utilities::spec::log::current_poll_start(btask_pending(), 2) == 0) by {
          assert(ue::is_poll_begin(btask_pending()[0]));
          assert(!ue::is_poll_begin(btask_pending()[1]));
          assert(!ue::is_poll_begin(btask_pending()[2]));
          assert(crate::utilities::spec::log::find_last_poll_begin(btask_pending(), 0) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(btask_pending(), 1) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(btask_pending(), 2) == 0);
        }
        assert(crate::utilities::spec::log::has_timer_registered_in_current_poll(btask_pending(), RID(), 2)) by {
          assert(crate::utilities::spec::log::in_current_poll_cycle(btask_pending(), 1, 2));
          assert(!crate::utilities::spec::log::timer_deregistered_after_in_poll(btask_pending(), RID(), 1, 2));
        }
        assert(crate::utilities::spec::log::has_active_timer_with_waker(btask_pending(), 2));
      }
    }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(ro, btask_pending())) by {
    assert forall |i: int| #[trigger] (ro.acceptance)(btask_pending(), i) implies (ro.validity)(btask_pending(), i) by { }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(wg, btask_ready())) by {
    assert forall |i: int| #[trigger] (wg.acceptance)(btask_ready(), i) implies (wg.validity)(btask_ready(), i) by {
      if i == 2 {
        assert(crate::utilities::spec::log::current_poll_start(btask_ready(), 2) == 0) by {
          assert(ue::is_poll_begin(btask_ready()[0]));
          assert(!ue::is_poll_begin(btask_ready()[1]));
          assert(!ue::is_poll_begin(btask_ready()[2]));
          assert(crate::utilities::spec::log::find_last_poll_begin(btask_ready(), 0) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(btask_ready(), 1) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(btask_ready(), 2) == 0);
        }
        assert(crate::utilities::spec::log::has_timer_registered_in_current_poll(btask_ready(), RID(), 2)) by {
          assert(crate::utilities::spec::log::in_current_poll_cycle(btask_ready(), 1, 2));
          assert(!crate::utilities::spec::log::timer_deregistered_after_in_poll(btask_ready(), RID(), 1, 2));
        }
        assert(crate::utilities::spec::log::has_active_timer_with_waker(btask_ready(), 2));
      }
    }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(ro, btask_ready())) by {
    assert forall |i: int| #[trigger] (ro.acceptance)(btask_ready(), i) implies (ro.validity)(btask_ready(), i) by { }
  }
}

pub proof fn bexec_injected(tid: TID)
  ensures
    crate::executor::spec::injection_schedule::injected_tasks(bexec1(tid))
      =~= seq![crate::executor::spec::types::TaskView { id: tid }],
    crate::executor::spec::injection_schedule::injected_tasks(bexec2(tid))
      =~= seq![crate::executor::spec::types::TaskView { id: tid }],
{
  use crate::executor::spec::injection_schedule::injected_tasks;
  bexec1_idx(tid); bexec2_idx(tid);
  let l1 = bexec1(tid);
  assert(injected_tasks(l1.subrange(0, 0)) =~= Seq::<crate::executor::spec::types::TaskView>::empty());
  assert(l1.subrange(0,1).subrange(0,0) =~= l1.subrange(0,0));
  assert(injected_tasks(l1.subrange(0, 1)) =~= Seq::<crate::executor::spec::types::TaskView>::empty());
  assert(l1.subrange(0,2).subrange(0,1) =~= l1.subrange(0,1));
  assert(injected_tasks(l1.subrange(0, 2)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l1.subrange(0,3).subrange(0,2) =~= l1.subrange(0,2));
  assert(injected_tasks(l1.subrange(0, 3)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l1.subrange(0,4).subrange(0,3) =~= l1.subrange(0,3));
  assert(injected_tasks(l1.subrange(0, 4)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l1.subrange(0,5).subrange(0,4) =~= l1.subrange(0,4));
  assert(injected_tasks(l1.subrange(0, 5)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l1.subrange(0,6).subrange(0,5) =~= l1.subrange(0,5));
  assert(injected_tasks(l1.subrange(0, 6)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l1.subrange(0,7).subrange(0,6) =~= l1.subrange(0,6));
  assert(injected_tasks(l1.subrange(0, 7)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l1.subrange(0,8).subrange(0,7) =~= l1.subrange(0,7));
  assert(l1.subrange(0,8) =~= l1);
  assert(injected_tasks(l1) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  let l2 = bexec2(tid);
  assert(l2.subrange(0, 8) =~= l1);
  assert(injected_tasks(l2.subrange(0, 8)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l2.subrange(0,9).subrange(0,8) =~= l2.subrange(0,8));
  assert(injected_tasks(l2.subrange(0, 9)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);  // pop@9 = None
  assert(l2.subrange(0,10).subrange(0,9) =~= l2.subrange(0,9));
  assert(injected_tasks(l2.subrange(0, 10)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l2.subrange(0,11).subrange(0,10) =~= l2.subrange(0,10));
  assert(injected_tasks(l2.subrange(0, 11)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l2.subrange(0,12).subrange(0,11) =~= l2.subrange(0,11));
  assert(injected_tasks(l2.subrange(0, 12)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l2.subrange(0,13).subrange(0,12) =~= l2.subrange(0,12));
  assert(injected_tasks(l2.subrange(0, 13)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l2.subrange(0,14).subrange(0,13) =~= l2.subrange(0,13));
  assert(injected_tasks(l2.subrange(0, 14)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l2.subrange(0,15).subrange(0,14) =~= l2.subrange(0,14));
  assert(injected_tasks(l2.subrange(0, 15)) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
  assert(l2.subrange(0,16).subrange(0,15) =~= l2.subrange(0,15));
  assert(l2.subrange(0,16) =~= l2);
  assert(injected_tasks(l2) =~= seq![crate::executor::spec::types::TaskView { id: tid }]);
}

pub proof fn bpops_deliver(tid: TID)
  ensures
    crate::executor::spec::injection_schedule::pops_deliver_schedule(bexec1(tid), bsched(tid)),
    crate::executor::spec::injection_schedule::pops_deliver_schedule(bexec2(tid), bsched(tid)),
{
  use crate::executor::spec::injection_schedule::*;
  bexec1_idx(tid); bexec2_idx(tid);
  bexec_injected(tid);
  let q = bsched(tid);
  assert(injected_tasks(bexec1(tid)) =~= q.subrange(0, 1));
  assert(is_task_prefix(injected_tasks(bexec1(tid)), q));
  assert(injected_tasks(bexec2(tid)) =~= q.subrange(0, 1));
  assert(is_task_prefix(injected_tasks(bexec2(tid)), q));
}

pub proof fn bs1_composed_progress(tid: TID)
  ensures
    composed_progress(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bs1(tid)),
{
  reveal(composed_progress);
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = bs1(tid);
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 0)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 0)); }
  assert(is_extension_of(s, s2));
  bexec1_exec_progress(tid);
  assert(s.executor_log =~= Seq::<ee::ExecutorEvent>::empty());
  breac1_reac_progress();
  assert(s.reactor_log =~= Seq::<re::ReactorEvent>::empty());
  bs1_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    btask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(t2 == tid && s2.task_logs[t2] == btask_pending());
    }
  }
  monotonic_alignment_holds_single(s2, tid);
  bpops_deliver(tid);
  // Phase B: reactor_wake_drain_step vacuous — arrival_witness's reactor log is
  // empty, so nothing is in the reactor-wake queue at s.
  crate::composed::proof::assumption_satisfiable::no_reactor_wake_pending_no_waketask(s);
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2));
  // Phase C: taskwake_drain_step vacuous — arrival_witness has empty task_logs.
  crate::composed::proof::assumption_satisfiable::no_taskwake_pending_no_woken(s);
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2));
}

pub proof fn bs2_composed_progress(tid: TID)
  ensures
    composed_progress(bs1(tid), bs2(tid)),
{
  reveal(composed_progress);
  let s = bs1(tid);
  let s2 = bs2(tid);
  bexec2_idx(tid); breac2_idx(); btask_idx();
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 8)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 5)); }
  assert(is_extension_of(s, s2)) by {
    assert(s.task_logs[tid] == btask_pending() && s2.task_logs[tid] == btask_ready());
    assert(crate::composed::spec::state::is_task_log_prefix(btask_pending(), btask_ready()));
  }
  bexec2_exec_progress(tid);
  breac2_reac_progress();
  bs2_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    btask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(t2 == tid && s2.task_logs[t2] == btask_ready());
    }
  }
  monotonic_alignment_holds_single(s2, tid);
  bpops_deliver(tid);
  // Phase B: reactor_wake_drain_step vacuous — bs1's reactor log (breac1) has no
  // WakeTask (the timer WakeTask fires WITHIN this step, at breac2[8]), so nothing
  // is in the reactor-wake queue at s=bs1; the same-tick drain is unconstrained.
  assert forall |w: int| 0 <= w < s.reactor_log.len() implies
    !rl::is_wake_task_at(s.reactor_log, w) by { breac1_flags(w); }
  crate::composed::proof::assumption_satisfiable::no_reactor_wake_pending_no_waketask(s);
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2));
  // Phase C: taskwake_drain_step vacuous — bs1's task log (btask_pending) has no Woken.
  assert forall |tid2: TID| #[trigger] s.task_logs.contains_key(tid2) implies
    (forall |j: int| 0 <= j < s.task_logs[tid2].len() ==> !ue::is_woken(s.task_logs[tid2][j])) by {
    assert(tid2 == tid && s.task_logs[tid2] == btask_pending());
    assert forall |j: int| #![trigger btask_pending()[j]] 0 <= j < btask_pending().len() implies
      !ue::is_woken(btask_pending()[j]) by { btask_idx(); }
  }
  crate::composed::proof::assumption_satisfiable::no_taskwake_pending_no_woken(s);
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2));
}

// ============================================================================
// env_N at each witness state (cap = 2)
// ============================================================================


// --- recursive-function computations for the witness reactor logs ---
proof fn breac_max_ts_zero(l: rl::Log)
  requires l == breac1() || l == breac2(),
  ensures rl::max_timestamp_up_to(l, 1) == 0,
{
  breac1_idx(); breac2_idx();
  assert(!rl::is_get_current_time_at(l, 0)) by { if l == breac1() { breac1_flags(0); } else { breac2_flags(0); } }
  assert(rl::max_timestamp_up_to(l, 0) == 0);
}

proof fn breac1_find_last_sw(rid: ResourceIdView)
  ensures crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(breac1(), rid, 5) == -1,
{
  breac1_idx();
  use crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid as fl;
  let l = breac1();
  assert(fl(l, rid, 0) == -1);
  assert(fl(l, rid, 1) == -1) by { breac1_flags(0); }
  assert(fl(l, rid, 2) == -1) by { breac1_flags(1); }
  assert(fl(l, rid, 3) == -1) by { breac1_flags(2); }
  assert(fl(l, rid, 4) == -1) by { breac1_flags(3); }
  assert(fl(l, rid, 5) == -1) by { breac1_flags(4); }
}

proof fn breac2_find_last_sw(rid: ResourceIdView)
  ensures crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(breac2(), rid, 10) == -1,
{
  breac2_idx();
  use crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid as fl;
  let l = breac2();
  assert(fl(l, rid, 0) == -1);
  assert(fl(l, rid, 1) == -1) by { breac2_flags(0); }
  assert(fl(l, rid, 2) == -1) by { breac2_flags(1); }
  assert(fl(l, rid, 3) == -1) by { breac2_flags(2); }
  assert(fl(l, rid, 4) == -1) by { breac2_flags(3); }
  assert(fl(l, rid, 5) == -1) by { breac2_flags(4); }
  assert(fl(l, rid, 6) == -1) by { breac2_flags(5); }
  assert(fl(l, rid, 7) == -1) by { breac2_flags(6); }
  assert(fl(l, rid, 8) == -1) by { breac2_flags(7); }
  assert(fl(l, rid, 9) == -1) by { breac2_flags(8); }
  assert(fl(l, rid, 10) == -1) by { breac2_flags(9); }
}

proof fn breac_find_io(l: rl::Log, rid: ResourceIdView)
  requires l == breac1() || l == breac2(),
  ensures crate::reactor::contracts::bounded_io_wakeup::find_io_syscall_register_idx(l, rid) == -1,
{
  breac1_idx(); breac2_idx();
  use crate::reactor::contracts::bounded_io_wakeup::find_io_syscall_register_idx_from as fio;
  let n = l.len() as int;
  assert(fio(l, rid, n) == -1);
  assert forall |m: int| 0 <= m < n implies #[trigger] fio(l, rid, m) == fio(l, rid, m + 1) by {
    if l == breac1() { breac1_flags(m); } else { breac2_flags(m); }
  }
  assert(fio(l, rid, n) == -1);
  if l == breac1() {
    assert(fio(l, rid, 4) == -1); assert(fio(l, rid, 3) == -1); assert(fio(l, rid, 2) == -1);
    assert(fio(l, rid, 1) == -1); assert(fio(l, rid, 0) == -1);
  } else {
    assert(fio(l, rid, 9) == -1); assert(fio(l, rid, 8) == -1); assert(fio(l, rid, 7) == -1);
    assert(fio(l, rid, 6) == -1); assert(fio(l, rid, 5) == -1); assert(fio(l, rid, 4) == -1);
    assert(fio(l, rid, 3) == -1); assert(fio(l, rid, 2) == -1); assert(fio(l, rid, 1) == -1);
    assert(fio(l, rid, 0) == -1);
  }
}

proof fn breac_env_facts(s: ComposedState, tid: TID)
  requires
    s.reactor_log == breac1() || s.reactor_log == breac2(),
    get_max_timer_deadline_gap(s, tid) >= 3,
  ensures
    crate::composed::spec::assumptions::timestamps_strictly_increasing(s.reactor_log),
    crate::reactor::timestamps_positive(s.reactor_log),
    timer_deadline_gap_bounded(s, tid),
    timer_resources_remain_active(s),
    contract_io_assumption_here(s),
    // bound-generic (no SetWaker ⟹ vacuous for every n, in particular the
    // uninterpreted get_io_ready_bound used by env_N)
    forall |rid: ResourceIdView, n: nat|
      #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
      io_ready_forward_here(s.reactor_log, rid, n),
{
  breac1_idx(); breac2_idx();
  let l = s.reactor_log;
  assert(crate::composed::spec::assumptions::timestamps_strictly_increasing(l)) by {
    assert forall |a: int, b: int| 0 <= a < b < l.len() &&
      rl::is_get_current_time_at(l, a) && rl::is_get_current_time_at(l, b)
      implies re::get_current_timestamp(l[a]) < re::get_current_timestamp(l[b]) by {
      if l == breac1() { breac1_flags(a); breac1_flags(b); } else { breac2_flags(a); breac2_flags(b); }
    }
  }
  assert(crate::reactor::timestamps_positive(l)) by {
    assert forall |a: int| 0 <= a < l.len() && rl::is_get_current_time_at(l, a)
      implies re::get_current_timestamp(l[a]) >= 1 by {
      if l == breac1() { breac1_flags(a); } else { breac2_flags(a); }
    }
  }
  assert(timer_deadline_gap_bounded(s, tid)) by {
    reveal(timer_deadline_gap_bounded);
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < l.len() && rl::is_succ_register_timer_at(l, reg_idx) &&
      crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(l, reg_idx, l.len() as int)
      implies crate::reactor::proof::round_extension::compute_bound(
        re::get_register_timer_deadline(l[reg_idx]), rl::max_timestamp_up_to(l, (reg_idx + 1) as int))
        <= get_max_timer_deadline_gap(s, tid) by {
      if l == breac1() { breac1_flags(reg_idx); } else { breac2_flags(reg_idx); }
      assert(reg_idx == 0);
      breac_max_ts_zero(l);
      assert(re::get_register_timer_deadline(l[0]) == 2);
    }
  }
  assert(timer_resources_remain_active(s)) by {
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < l.len() && rl::is_succ_register_timer_at(l, reg_idx)
      implies crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(l, reg_idx, l.len() as int) by {
      if l == breac1() { breac1_flags(reg_idx); } else { breac2_flags(reg_idx); }
      assert(reg_idx == 0);
      assert forall |k: int| 0 < k < l.len() implies
        !(rl::is_deregister_timer_at(l, k) && re::get_deregister_timer_rid(l[k]) == re::get_register_timer_rid(l[0])) by {
        if l == breac1() { breac1_flags(k); } else { breac2_flags(k); }
      }
    }
  }
  assert(contract_io_assumption_here(s)) by {
    assert forall |rid: ResourceIdView| #![trigger io_assumption_here(s.reactor_log, rid)]
      io_assumption_here(s.reactor_log, rid) by {
      breac_find_io(l, rid);
      // reshaped io_remains_active is vacuous: breac has no SetWaker (find_last == -1).
      if l == breac1() { breac1_find_last_sw(rid); } else { breac2_find_last_sw(rid); }
      assert(crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
        l, rid, l.len() as int) == -1);
      assert(crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(l, rid));
    }
  }
  assert forall |rid: ResourceIdView, n: nat|
    #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
    io_ready_forward_here(s.reactor_log, rid, n) by {
    if l == breac1() { breac1_find_last_sw(rid); } else { breac2_find_last_sw(rid); }
    assert(crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(l, rid, l.len() as int) == -1);
  }
}

pub proof fn b_common_env_facts(s: ComposedState, tid: TID)
  requires
    (s.reactor_log == breac1() && s.executor_log == bexec1(tid) && s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, btask_pending()) && s.injection_schedule == bsched(tid)) ||
    (s.reactor_log == breac2() && s.executor_log == bexec2(tid) && s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, btask_ready()) && s.injection_schedule == bsched(tid)),
    get_max_queue_length(s) >= 1,
  ensures
    el::tid_unique(s.executor_log, tid),
    queue_length_bounded(s),
{
  let is1 = s.executor_log == bexec1(tid);
  bexec1_idx(tid); bexec2_idx(tid); btask_idx();
  let l = s.executor_log;
  assert(el::tid_unique(l, tid)) by {
    assert forall |a: int, b: int| 0 <= a < b < l.len() &&
      el::is_pop_injection_at(l, a) && ee::get_pop_injection_task(l[a]) == Some(crate::executor::spec::types::TaskView { id: tid }) &&
      el::is_pop_injection_at(l, b) && ee::get_pop_injection_task(l[b]) == Some(crate::executor::spec::types::TaskView { id: tid })
      implies false by {
      if is1 { bexec1_flags(tid, a); bexec1_flags(tid, b); } else { bexec2_flags(tid, a); bexec2_flags(tid, b); }
    }
  }
  if is1 { bexec1_queue_len(tid); } else { bexec2_queue_len(tid); }
  assert(queue_length_bounded(s)) by {
    assert forall |i: int|
      #![trigger crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i)]
      0 <= i <= l.len() implies
      crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i).len() <= get_max_queue_length(s) by {
      if is1 { bexec1_queue_len(tid); } else { bexec2_queue_len(tid); }
    }
  }
}

pub proof fn bexec1_queue_len(tid: TID)
  ensures
    forall |i: int| 0 <= i <= bexec1(tid).len() ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec1(tid), i).len() <= 1,
    forall |i: int| 0 <= i <= bexec1(tid).len() ==>
      #[trigger] el::fifo_queue_at_for_persistent(bexec1(tid), i).len() <= 1,
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  bexec1_idx(tid);
  let l = bexec1(tid);
  bexec1_queue(tid);
  assert(fifo_queue_at(l, 7) =~= Seq::<TID>::empty());
  assert forall |i: int| 0 <= i <= l.len() implies #[trigger] fifo_queue_at(l, i).len() <= 1 by {
    bexec1_queue(tid);
    assert(fifo_queue_at(l, 7) =~= Seq::<TID>::empty());
    if 2 <= i <= 6 { } else if i == 7 || i == 8 { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
  }
  assert forall |i: int| 0 <= i <= l.len() implies #[trigger] el::fifo_queue_at_for_persistent(l, i).len() <= 1 by {
    bexec1_queue(tid);
    assert(fifo_queue_at(l, 7) =~= Seq::<TID>::empty());
    if 2 <= i <= 6 { } else if i == 7 || i == 8 { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
  }
}

pub proof fn bexec2_queue_len(tid: TID)
  ensures
    forall |i: int| 0 <= i <= bexec2(tid).len() ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(bexec2(tid), i).len() <= 1,
    forall |i: int| 0 <= i <= bexec2(tid).len() ==>
      #[trigger] el::fifo_queue_at_for_persistent(bexec2(tid), i).len() <= 1,
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  bexec2_idx(tid);
  let l = bexec2(tid);
  bexec2_queue(tid);
  assert forall |i: int| 0 <= i <= l.len() implies #[trigger] fifo_queue_at(l, i).len() <= 1 by {
    bexec2_queue(tid);
    if 2 <= i <= 6 { } else if 7 <= i <= 13 { } else if i == 14 { }
    else if i == 15 || i == 16 { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
  }
  assert forall |i: int| 0 <= i <= l.len() implies #[trigger] el::fifo_queue_at_for_persistent(l, i).len() <= 1 by {
    bexec2_queue(tid);
    if 2 <= i <= 6 { } else if 7 <= i <= 13 { } else if i == 14 { }
    else if i == 15 || i == 16 { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
  }
}

pub proof fn bpoll_count_bexec1(tid: TID)
  ensures
    crate::composed::spec::assumptions::count_polls_for_tid(bexec1(tid), tid) == 1,
{
  bexec1_idx(tid);
  use crate::composed::spec::assumptions::count_polls_for_tid;
  let l = bexec1(tid);
  assert(count_polls_for_tid(l.subrange(0, 0), tid) == 0);
  assert(l.subrange(0,1).subrange(0,0) =~= l.subrange(0,0));
  assert(count_polls_for_tid(l.subrange(0, 1), tid) == 0) by { bexec1_flags(tid, 0); }
  assert(l.subrange(0,2).subrange(0,1) =~= l.subrange(0,1));
  assert(count_polls_for_tid(l.subrange(0, 2), tid) == 0) by { bexec1_flags(tid, 1); }
  assert(l.subrange(0,3).subrange(0,2) =~= l.subrange(0,2));
  assert(count_polls_for_tid(l.subrange(0, 3), tid) == 0) by { bexec1_flags(tid, 2); }
  assert(l.subrange(0,4).subrange(0,3) =~= l.subrange(0,3));
  assert(count_polls_for_tid(l.subrange(0, 4), tid) == 0) by { bexec1_flags(tid, 3); }
  assert(l.subrange(0,5).subrange(0,4) =~= l.subrange(0,4));
  assert(count_polls_for_tid(l.subrange(0, 5), tid) == 0) by { bexec1_flags(tid, 4); }
  assert(l.subrange(0,6).subrange(0,5) =~= l.subrange(0,5));
  assert(count_polls_for_tid(l.subrange(0, 6), tid) == 0) by { bexec1_flags(tid, 5); }
  assert(l.subrange(0,7).subrange(0,6) =~= l.subrange(0,6));
  assert(count_polls_for_tid(l.subrange(0, 7), tid) == 1) by { bexec1_flags(tid, 6); }
  assert(l.subrange(0, 8) =~= l);
  assert(l.subrange(0,8).subrange(0,7) =~= l.subrange(0,7));
  assert(count_polls_for_tid(l, tid) == 1) by { bexec1_flags(tid, 7); }
}

pub proof fn bs0_env(tid: TID)
  ensures
    env_N(crate::composed::proof::assumption_satisfiable::arrival_witness(tid), tid, 2nat),
{
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  crate::composed::proof::assumption_satisfiable::env_core_holds_empty_logs(s, tid);
  assert(end_to_end_env(s, tid));
  assert(bounded_poll_count_here_with_bound(s, tid, 2nat)) by {
    assert(crate::composed::spec::assumptions::count_polls_for_tid(s.executor_log, tid) == 0);
  }
  assert forall |rid: ResourceIdView, n: nat|
    #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
    io_ready_forward_here(s.reactor_log, rid, n) by {
    assert(crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(s.reactor_log, rid, 0) == -1);
  }
  assert(!s.task_logs.contains_key(tid));
  crate::composed::proof::assumption_satisfiable::taskwake_arrival_within_vacuous(s, tid, 2nat);
}

#[verifier::rlimit(100)]
proof fn bs1_env(tid: TID)
  requires
    get_max_queue_length(bs1(tid)) >= 1,
    get_max_timer_deadline_gap(bs1(tid), tid) >= 3,
  ensures
    env_N(bs1(tid), tid, 2nat),
{
  let s = bs1(tid);
  bexec1_idx(tid); breac1_idx(); btask_idx();
  breac_env_facts(s, tid);
  b_common_env_facts(s, tid);
  assert(bounded_poll_count_here_with_bound(s, tid, 2nat)) by { bpoll_count_bexec1(tid); }
  assert(env_holds_at_state_core(s, tid));
  assert(end_to_end_env(s, tid));
  assert(!crate::utilities::spec::log::has_pass_waker_in_current_poll(
    s.task_logs[tid], (s.task_logs[tid].len() - 1) as int)) by {
    btask_idx();
    let tl = s.task_logs[tid];
    assert(tl == btask_pending());
    assert((tl.len() - 1) as int == 2);
    assert forall |j: int| #![trigger tl[j]] 0 <= j < tl.len() implies !ue::is_pass_waker(tl[j]) by {}
  }
  crate::composed::proof::assumption_satisfiable::taskwake_arrival_within_vacuous(s, tid, 2nat);
}

#[verifier::rlimit(100)]
proof fn bs2_env(tid: TID)
  requires
    get_max_queue_length(bs2(tid)) >= 1,
    get_max_timer_deadline_gap(bs2(tid), tid) >= 3,
  ensures
    env_N(bs2(tid), tid, 2nat),
{
  let s = bs2(tid);
  bexec2_idx(tid); breac2_idx(); btask_idx();
  breac_env_facts(s, tid);
  b_common_env_facts(s, tid);
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

pub proof fn b_domain_inhabited(tid: TaskId)
  requires
    get_max_queue_length(bs1(tid)) >= 1,
    get_max_timer_deadline_gap(bs1(tid), tid) >= 3,
  ensures
    crate::composed::proof::assumption_satisfiable::ete_reachable_N(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bs2(tid), 2nat, 2nat, tid),
    crate::composed::spec::contract::end_to_end_response(bs2(tid), tid),
    !crate::composed::spec::contract::end_to_end_trigger(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), tid),
    !crate::composed::spec::contract::end_to_end_response(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), tid),
{
  let s0 = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s1 = bs1(tid);
  let s2 = bs2(tid);
  bexec2_idx(tid);
  assert(get_max_queue_length(s2) == get_max_queue_length(s1));
  assert(get_max_timer_deadline_gap(s2, tid) == get_max_timer_deadline_gap(s1, tid));
  bs0_env(tid); bs1_env(tid); bs2_env(tid);
  bs1_composed_progress(tid); bs2_composed_progress(tid);
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
