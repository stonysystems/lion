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
use crate::reactor::spec::types::{IoResultView, ResourceIdView, IoEventView};
use crate::utilities::spec::events as ue;
use crate::utilities::spec::log as ul;
#[cfg(verus_keep_ghost)]
use crate::composed::proof::inhabitation_goal_wake::{bexec1, bexec2, bsched,
  bexec1_idx, bexec2_idx, bexec1_flags, bexec2_flags, bexec1_exec_progress,
  bexec2_exec_inv, bexec2_exec_progress, bexec_injected, bpops_deliver,
  bexec1_queue_len, bexec2_queue_len, bpoll_count_bexec1};
#[cfg(verus_keep_ghost)]
use crate::composed::proof::assumption_satisfiable::{env_N, bounded_poll_count_here_with_bound,
  io_ready_forward_here, end_to_end_env, env_holds_at_state_core};
#[cfg(verus_keep_ghost)]
use crate::composed::spec::assumptions::{
  timer_deadline_gap_bounded, timer_resources_remain_active,
  queue_length_bounded, get_max_timer_deadline_gap,
  get_max_queue_length};

verus! {

// ============================================================================
// L1 (io-symmetry): a REAL-WAKE goal-reaching env-good trace exercising a genuine
// IO wait (poll Pending on a registered io resource with a readable SetWaker) and
// a real io WakeTask (io ready → wake → re-poll Ready). The io analog of
// b_domain_inhabited (timer). cap = 2.
//
//   s0 = arrival_witness(tid)
//   tick 1 (s0 → bios1): PopInj Some(tid); poll(Pending) registering io RIO +
//                        readable SetWaker(WK); reactor does one park cycle in
//                        which the fd is ALREADY readable (register io, set
//                        waker, clock=1, PollEvents 1 ready ⟹ IoEventReady +
//                        WakeTask(WK, RIO) same-cycle). Readiness in tick 1
//                        keeps io_ready_forward_here's consequent concretely
//                        true at bios1, so env_N discharges for ANY value of
//                        the uninterpreted get_io_ready_bound.
//   tick 2 (bios1 → bios2): executor DrainReactorWake[tid] delivers tid;
//                           poll(Ready); reactor does one empty park cycle.
//
// All outbound reactor events (RegisterIo epoll_ctl, GetCurrentTime, PollEvents,
// IoEventReady, WakeTask) sit INSIDE a park cycle (is_inbound_non_park is false for
// Outbound); is_complete_park_cycle permits any non-park event between begin/end.
// ============================================================================

pub open spec fn RIO() -> ResourceIdView { 7 }
pub open spec fn WK() -> int { 3 }
pub open spec fn SRC() -> int { 0 }
// readable-only interest: (readable, writable) = (true, false)
pub open spec fn READABLE() -> (bool, bool) { (true, false) }

// --- Reactor log: tick 1 (one park cycle: register io + set readable waker; the fd
// is already readable ⟹ IoEventReady + WakeTask fire same-cycle) ---
pub open spec fn bioreac1() -> rl::Log {
  seq![
    re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    re::ReactorEvent::Inbound(re::InboundCall::RegisterIoResource {
      source: SRC(), interest: READABLE(), result: None,
    }),
    re::ReactorEvent::Outbound(re::OutboundCall::RegisterIoResource {
      source: SRC(), resource_id: RIO(), interest: READABLE(), result: IoResultView::Ok(()),
    }),
    re::ReactorEvent::Inbound(re::InboundCall::RegisterIoResource {
      source: SRC(), interest: READABLE(), result: Some(IoResultView::Ok(RIO())),
    }),
    re::ReactorEvent::Inbound(re::InboundCall::SetWaker {
      resource_id: RIO(), interest: READABLE(), waker: WK(), result: Some(IoResultView::Ok(())),
    }),
    re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 1int }),
    re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(1nat),
    }),
    re::ReactorEvent::Outbound(re::OutboundCall::IoEventReady {
      event: IoEventView { resource_id: RIO(), readable: true, writable: false },
    }),
    re::ReactorEvent::Outbound(re::OutboundCall::WakeTask {
      waker: WK(), source_rid: RIO(),
    }),
    re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())),
    }),
  ]
}

// --- Reactor log: tick 1 + tick 2 (empty park cycle: wake already fired in tick 1) ---
pub open spec fn bioreac2() -> rl::Log {
  bioreac1() + seq![
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

// ============================================================================
// Index lemmas
// ============================================================================

pub proof fn bioreac1_idx()
  ensures
    bioreac1().len() == 10,
    bioreac1()[0] == re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    bioreac1()[1] == re::ReactorEvent::Inbound(re::InboundCall::RegisterIoResource {
      source: SRC(), interest: READABLE(), result: None }),
    bioreac1()[2] == re::ReactorEvent::Outbound(re::OutboundCall::RegisterIoResource {
      source: SRC(), resource_id: RIO(), interest: READABLE(), result: IoResultView::Ok(()) }),
    bioreac1()[3] == re::ReactorEvent::Inbound(re::InboundCall::RegisterIoResource {
      source: SRC(), interest: READABLE(), result: Some(IoResultView::Ok(RIO())) }),
    bioreac1()[4] == re::ReactorEvent::Inbound(re::InboundCall::SetWaker {
      resource_id: RIO(), interest: READABLE(), waker: WK(), result: Some(IoResultView::Ok(())) }),
    bioreac1()[5] == re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 1int }),
    bioreac1()[6] == re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(1nat) }),
    bioreac1()[7] == re::ReactorEvent::Outbound(re::OutboundCall::IoEventReady {
      event: IoEventView { resource_id: RIO(), readable: true, writable: false } }),
    bioreac1()[8] == re::ReactorEvent::Outbound(re::OutboundCall::WakeTask {
      waker: WK(), source_rid: RIO() }),
    bioreac1()[9] == re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())) }),
{
}

pub proof fn bioreac2_idx()
  ensures
    bioreac2().len() == 14,
    forall |j: int| 0 <= j < 10 ==> bioreac2()[j] == bioreac1()[j],
    bioreac2()[10] == re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    bioreac2()[11] == re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 2int }),
    bioreac2()[12] == re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat) }),
    bioreac2()[13] == re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())) }),
{
  bioreac1_idx();
}

// ============================================================================
// Reactor per-index flags
// ============================================================================

// bioreac1: Park[Begin]@0, RegIoBegin@1, RegIo(succ,outbound)@2, RegIoEnd@3,
// SetWaker(succ)@4, GCT(1)@5, PollEvents@6, IoEventReady@7, WakeTask@8, Park[End]@9.
pub proof fn bioreac1_flags(j: int)
  ensures
    !rl::is_succ_register_timer_at(bioreac1(), j),
    !rl::is_deregister_timer_at(bioreac1(), j),
    j != 2 ==> !rl::io_syscall_registered_at(bioreac1(), j),
    rl::io_syscall_registered_at(bioreac1(), 2),
    re::get_io_syscall_register_rid(bioreac1()[2]) == RIO(),
    j != 2 ==> !rl::io_syscall_register_at(bioreac1(), j),
    !rl::io_syscall_deregistered_at(bioreac1(), j),
    j != 4 ==> !rl::is_succ_set_waker_at(bioreac1(), j),
    rl::is_succ_set_waker_at(bioreac1(), 4),
    re::get_set_waker_rid(bioreac1()[4]) == RIO(),
    re::get_set_waker_waker(bioreac1()[4]) == WK(),
    re::get_set_waker_interest(bioreac1()[4]) == READABLE(),
    j != 4 ==> !rl::is_set_waker_at(bioreac1(), j),
    j != 8 ==> !rl::is_wake_task_at(bioreac1(), j),
    rl::is_wake_task_at(bioreac1(), 8),
    re::get_wake_task_source_rid(bioreac1()[8]) == RIO(),
    re::get_wake_task_waker(bioreac1()[8]) == WK(),
    j != 7 ==> !rl::is_io_event_ready_at(bioreac1(), j),
    rl::is_io_event_ready_at(bioreac1(), 7),
    re::get_io_event(bioreac1()[7]).resource_id == RIO(),
    re::get_io_event(bioreac1()[7]).readable,
    j != 0 ==> !rl::is_park_begin_at(bioreac1(), j),
    rl::is_park_begin_at(bioreac1(), 0),
    j != 9 ==> !rl::is_park_end_at(bioreac1(), j),
    rl::is_park_end_at(bioreac1(), 9),
    j != 5 ==> !rl::is_get_current_time_at(bioreac1(), j),
{
  bioreac1_idx();
  if j == 0 {} else if j == 1 {} else if j == 2 {} else if j == 3 {}
  else if j == 4 {} else if j == 5 {} else if j == 6 {} else if j == 7 {}
  else if j == 8 {} else if j == 9 {} else {}
}

// bioreac2: as bioreac1 for [0,10); Park[Begin]@10, GCT(2)@11, PollEvents@12,
// Park[End]@13.
pub proof fn bioreac2_flags(j: int)
  ensures
    !rl::is_succ_register_timer_at(bioreac2(), j),
    !rl::is_deregister_timer_at(bioreac2(), j),
    j != 2 ==> !rl::io_syscall_registered_at(bioreac2(), j),
    rl::io_syscall_registered_at(bioreac2(), 2),
    re::get_io_syscall_register_rid(bioreac2()[2]) == RIO(),
    j != 2 ==> !rl::io_syscall_register_at(bioreac2(), j),
    !rl::io_syscall_deregistered_at(bioreac2(), j),
    j != 4 ==> !rl::is_succ_set_waker_at(bioreac2(), j),
    rl::is_succ_set_waker_at(bioreac2(), 4),
    re::get_set_waker_rid(bioreac2()[4]) == RIO(),
    re::get_set_waker_waker(bioreac2()[4]) == WK(),
    re::get_set_waker_interest(bioreac2()[4]) == READABLE(),
    j != 4 ==> !rl::is_set_waker_at(bioreac2(), j),
    j != 8 ==> !rl::is_wake_task_at(bioreac2(), j),
    rl::is_wake_task_at(bioreac2(), 8),
    re::get_wake_task_source_rid(bioreac2()[8]) == RIO(),
    re::get_wake_task_waker(bioreac2()[8]) == WK(),
    j != 7 ==> !rl::is_io_event_ready_at(bioreac2(), j),
    rl::is_io_event_ready_at(bioreac2(), 7),
    re::get_io_event(bioreac2()[7]).resource_id == RIO(),
    re::get_io_event(bioreac2()[7]).readable,
    (j != 0 && j != 10) ==> !rl::is_park_begin_at(bioreac2(), j),
    (j != 9 && j != 13) ==> !rl::is_park_end_at(bioreac2(), j),
    (j != 5 && j != 11) ==> !rl::is_get_current_time_at(bioreac2(), j),
{
  bioreac2_idx();
  bioreac1_idx();
  if 0 <= j < 10 {
    assert(bioreac2()[j] == bioreac1()[j]);
    bioreac1_flags(j);
  } else if j == 10 {} else if j == 11 {} else if j == 12 {} else if j == 13 {} else {}
}

// ============================================================================
// reactor_inv(bioreac1)
// ============================================================================

// action-safety that stays vacuous on bioreac1 (no timer events, no io deregister):
// timer families + io deregister families.
#[verifier::rlimit(50)]
proof fn bioreac1_vacuous_as()
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_deadline_future::timer_deadline_future(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_waker_validity::timer_waker_validity(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result(), bioreac1()),
{
  let l = bioreac1();
  let p1 = crate::reactor::invariants::timer_deadline_future::timer_deadline_future();
  assert(crate::framework::action_safety::action_safety_satisfied(p1, l)) by {
    assert forall |i: int| #[trigger] (p1.acceptance)(l, i) implies (p1.validity)(l, i) by { bioreac1_flags(i); } }
  let p3 = crate::reactor::invariants::timer_waker_validity::timer_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p3, l)) by {
    assert forall |i: int| #[trigger] (p3.acceptance)(l, i) implies (p3.validity)(l, i) by { bioreac1_flags(i); } }
  let p5 = crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p5, l)) by {
    assert forall |i: int| #[trigger] (p5.acceptance)(l, i) implies (p5.validity)(l, i) by { bioreac1_flags(i); } }
  let p6 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer();
  assert(crate::framework::action_safety::action_safety_satisfied(p6, l)) by {
    assert forall |i: int| #[trigger] (p6.acceptance)(l, i) implies (p6.validity)(l, i) by { bioreac1_flags(i); } }
  let p7 = crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p7, l)) by {
    assert forall |i: int| #[trigger] (p7.acceptance)(l, i) implies (p7.validity)(l, i) by { bioreac1_flags(i); } }
  let p8 = crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p8, l)) by {
    assert forall |i: int| #[trigger] (p8.acceptance)(l, i) implies (p8.validity)(l, i) by { bioreac1_flags(i); } }
}

// io_syscall_active_at(bioreac1, 2, i) for i in (2, 10]: no io deregister anywhere.
proof fn bioreac1_io_active_from2(i: int)
  requires 2 < i <= 10,
  ensures rl::io_syscall_active_at(bioreac1(), 2, i),
{
  let l = bioreac1();
  bioreac1_idx();
  assert(rl::io_syscall_active_at(l, 2, i)) by {
    assert forall |jj: int| 2 < jj < i implies
      !(rl::io_syscall_deregistered_at(l, jj) && re::get_io_syscall_deregister_rid(l[jj]) == RIO()) by { bioreac1_flags(jj); }
  }
}

// io-family action-safety that FIRES on bioreac1: register@2, setwaker@4,
// io-ready@7, wake@8, plus the uniqueness/disjoint checks at the register.
#[verifier::rlimit(50)]
proof fn bioreac1_io_fires()
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::set_waker_active_io::set_waker_active_io(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_ready_in_park::io_ready_in_park(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_waker_validity::io_waker_validity(), bioreac1()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::wake_has_registration::wake_has_registration(), bioreac1()),
{
  let l = bioreac1();
  bioreac1_idx();

  // io_reg_uniqueness @2: no prior io registration for RIO.
  let pu = crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(pu, l)) by {
    assert forall |i: int| #[trigger] (pu.acceptance)(l, i) implies (pu.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 2 {
        assert forall |k: int| 0 <= k < 2 && rl::io_syscall_registered_at(l, k) &&
          re::get_io_syscall_register_rid(l[k]) == RIO()
          implies exists |jj: int| k < jj < 2 && #[trigger] rl::io_syscall_deregistered_at(l, jj) &&
            re::get_io_syscall_deregister_rid(l[jj]) == RIO() by { bioreac1_flags(k); }
        crate::reactor::invariants::io_reg_uniqueness::intro_no_prior_io_syscall_registration(l, RIO(), 2);
      }
    }
  }
  // timer_io_disjoint_at_io @2: no timer registration for RIO.
  let pd = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io();
  assert(crate::framework::action_safety::action_safety_satisfied(pd, l)) by {
    assert forall |i: int| #[trigger] (pd.acceptance)(l, i) implies (pd.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 2 {
        assert forall |k: int| 0 <= k < 2 && rl::is_succ_register_timer_at(l, k) &&
          re::get_register_timer_rid(l[k]) == RIO()
          implies exists |jj: int| k < jj < 2 && #[trigger] rl::timer_retired_at(l, RIO(), jj) by { bioreac1_flags(k); }
        crate::reactor::invariants::timer_io_disjoint::intro_no_timer_with_rid_before(l, RIO(), 2);
      }
    }
  }
  // register_io_in_cycle @2: outbound register in an open inbound register cycle (begin@1).
  let pr = crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(pr, l)) by {
    assert forall |i: int| #[trigger] (pr.acceptance)(l, i) implies (pr.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 2 {
        assert(crate::reactor::invariants::register_io_in_cycle::find_last_inbound_register_io_begin(l, 2) == 1);
        assert(crate::reactor::invariants::register_io_in_cycle::no_inbound_register_io_end_between(l, 1, 2));
      }
    }
  }
  // inbound_register_io_result @3: inbound end matches begin@1 + outbound@2.
  let pi = crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(pi, l)) by {
    assert forall |i: int| #[trigger] (pi.acceptance)(l, i) implies (pi.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 3 {
        assert(crate::reactor::invariants::inbound_register_io_result::find_register_io_cycle_begin(l, 2) == 1);
        assert(crate::reactor::invariants::inbound_register_io_result::find_register_io_cycle_begin(l, 3) == 1);
        assert(crate::reactor::invariants::inbound_register_io_result::has_matching_outbound_register(
          l, 1, 3, SRC(), READABLE(), IoResultView::Ok(RIO()))) by {
          assert(crate::reactor::invariants::inbound_register_io_result::inbound_result_matches_outbound_register(
            IoResultView::Ok(RIO()), IoResultView::Ok(()), RIO()));
        }
      }
    }
  }
  // set_waker_active_io @4: io active at set waker (register@2 before, no deregister between).
  let ps = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert(crate::framework::action_safety::action_safety_satisfied(ps, l)) by {
    assert forall |i: int| #[trigger] (ps.acceptance)(l, i) implies (ps.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 4 {
        assert(crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, RIO(), 3) == 2);
        assert(crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, RIO(), 4) == 2);
        assert(rl::io_syscall_active_at(l, 2, 4)) by {
          assert forall |jj: int| 2 < jj < 4 implies
            !(rl::io_syscall_deregistered_at(l, jj) && re::get_io_syscall_deregister_rid(l[jj]) == RIO()) by { bioreac1_flags(jj); }
        }
      }
    }
  }
  // io_ready_in_park @7: inside the park cycle [0, 10).
  let pk = crate::reactor::invariants::io_ready_in_park::io_ready_in_park();
  assert(crate::framework::action_safety::action_safety_satisfied(pk, l)) by {
    assert forall |i: int| #[trigger] (pk.acceptance)(l, i) implies (pk.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 7 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(rl::current_park_start(l, 4) == 0);
        assert(rl::current_park_start(l, 5) == 0);
        assert(rl::current_park_start(l, 6) == 0);
        assert(rl::current_park_start(l, 7) == 0);
      }
    }
  }
  // io_waker_validity @8: the wake's waker is the active SetWaker@4's waker.
  let pw = crate::reactor::invariants::io_waker_validity::io_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(pw, l)) by {
    assert forall |i: int| #[trigger] (pw.acceptance)(l, i) implies (pw.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 8 {
        assert(crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, RIO(), 3) == 2);
        assert(crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, RIO(), 4) == 2);
        bioreac1_io_active_from2(4);
        assert(crate::reactor::invariants::io_waker_validity::io_syscall_active_at_set_waker(l, RIO(), 4));
        assert(rl::is_succ_set_waker_at(l, 4) && re::get_set_waker_rid(l[4]) == RIO() &&
          re::get_set_waker_waker(l[4]) == WK());
      }
    }
  }
  // wake_has_registration @8: RIO registered @2 and still active.
  let ph = crate::reactor::invariants::wake_has_registration::wake_has_registration();
  assert(crate::framework::action_safety::action_safety_satisfied(ph, l)) by {
    assert forall |i: int| #[trigger] (ph.acceptance)(l, i) implies (ph.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 8 {
        bioreac1_io_active_from2(8);
        assert(crate::reactor::invariants::io_waker_validity::is_io_syscall_wake_at(l, 8));
      }
    }
  }
}

pub proof fn bioreac1_reac_inv()
  ensures
    crate::reactor::invariants::reactor_inv(bioreac1()),
{
  let l = bioreac1();
  bioreac1_idx();

  // park_has_timestamp: park end @9, GCT @5 in cycle [0,10).
  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 9 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(rl::current_park_start(l, 4) == 0);
        assert(rl::current_park_start(l, 5) == 0);
        assert(rl::current_park_start(l, 6) == 0);
        assert(rl::current_park_start(l, 7) == 0);
        assert(rl::current_park_start(l, 8) == 0);
        assert(rl::current_park_start(l, 9) == 0);
        assert(rl::is_get_current_time_at(l, 5));
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 9));
      }
    }
  }
  // park_poll_once: one PollEvents @6.
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      bioreac1_flags(i);
      if i == 9 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(rl::current_park_start(l, 4) == 0);
        assert(rl::current_park_start(l, 5) == 0);
        assert(rl::current_park_start(l, 6) == 0);
        assert(rl::current_park_start(l, 7) == 0);
        assert(rl::current_park_start(l, 8) == 0);
        assert(rl::current_park_start(l, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 9, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 8, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 7, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 6, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 5, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 4, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 3, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 2, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 1, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 0, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, 9));
      }
    }
  }
  bioreac1_vacuous_as();
  bioreac1_io_fires();

  // local liveness: wake_on_io_ready_readable fires @7 (wake@8); others vacuous.
  let q1 = crate::reactor::invariants::wake_on_expired::wake_on_expired();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q1, l)) by {
    assert forall |i: int| #[trigger] (q1.acceptance)(l, i) implies
      exists |j: int| #![trigger (q1.fulfillment)(l, i, j)]
        j > i && (q1.fulfillment)(l, i, j) && (q1.timely)(l, i, j) by { bioreac1_flags(i); } }
  let q2 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_readable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q2, l)) by {
    assert forall |i: int| #[trigger] (q2.acceptance)(l, i) implies
      exists |j: int| #![trigger (q2.fulfillment)(l, i, j)]
        j > i && (q2.fulfillment)(l, i, j) && (q2.timely)(l, i, j) by {
      bioreac1_flags(i);
      if i == 7 {
        assert(crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(l, RIO(), 5) == 4);
        assert(crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(l, RIO(), 6) == 4);
        assert(crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(l, RIO(), 7) == 4);
        assert((q2.fulfillment)(l, 7, 8) && (q2.timely)(l, 7, 8)) by {
          assert(rl::is_wake_task_at(l, 8));
          assert(re::get_wake_task_source_rid(l[8]) == RIO());
          assert(re::get_wake_task_waker(l[8]) == WK());
          assert(re::get_set_waker_waker(l[4]) == WK());
          assert forall |k: int| 7 < k < 8 implies
            !(rl::is_park_end_at(l, k) || rl::is_poll_events_at(l, k)) by { bioreac1_flags(k); }
        }
        assert(8 > 7 && (q2.fulfillment)(l, 7, 8) && (q2.timely)(l, 7, 8));
      }
    }
  }
  let q3 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_writable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q3, l)) by {
    assert forall |i: int| #[trigger] (q3.acceptance)(l, i) implies
      exists |j: int| #![trigger (q3.fulfillment)(l, i, j)]
        j > i && (q3.fulfillment)(l, i, j) && (q3.timely)(l, i, j) by { bioreac1_flags(i); } }
}

// ============================================================================
// reactor_inv(bioreac2)
// ============================================================================

// timer + deregister families stay vacuous on bioreac2.
#[verifier::rlimit(50)]
proof fn bioreac2_vacuous_as()
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_deadline_future::timer_deadline_future(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_waker_validity::timer_waker_validity(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result(), bioreac2()),
{
  let l = bioreac2();
  let p1 = crate::reactor::invariants::timer_deadline_future::timer_deadline_future();
  assert(crate::framework::action_safety::action_safety_satisfied(p1, l)) by {
    assert forall |i: int| #[trigger] (p1.acceptance)(l, i) implies (p1.validity)(l, i) by { bioreac2_flags(i); } }
  let p3 = crate::reactor::invariants::timer_waker_validity::timer_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p3, l)) by {
    assert forall |i: int| #[trigger] (p3.acceptance)(l, i) implies (p3.validity)(l, i) by { bioreac2_flags(i); } }
  let p5 = crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p5, l)) by {
    assert forall |i: int| #[trigger] (p5.acceptance)(l, i) implies (p5.validity)(l, i) by { bioreac2_flags(i); } }
  let p6 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer();
  assert(crate::framework::action_safety::action_safety_satisfied(p6, l)) by {
    assert forall |i: int| #[trigger] (p6.acceptance)(l, i) implies (p6.validity)(l, i) by { bioreac2_flags(i); } }
  let p7 = crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p7, l)) by {
    assert forall |i: int| #[trigger] (p7.acceptance)(l, i) implies (p7.validity)(l, i) by { bioreac2_flags(i); } }
  let p8 = crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p8, l)) by {
    assert forall |i: int| #[trigger] (p8.acceptance)(l, i) implies (p8.validity)(l, i) by { bioreac2_flags(i); } }
}

// io_syscall_active_at(bioreac2, 2, i) for i in (2, 14]: no io deregister anywhere.
proof fn bioreac2_io_active_from2(i: int)
  requires 2 < i <= 14,
  ensures rl::io_syscall_active_at(bioreac2(), 2, i),
{
  let l = bioreac2();
  bioreac2_idx();
  assert(rl::io_syscall_active_at(l, 2, i)) by {
    assert forall |jj: int| 2 < jj < i implies
      !(rl::io_syscall_deregistered_at(l, jj) && re::get_io_syscall_deregister_rid(l[jj]) == RIO()) by { bioreac2_flags(jj); }
  }
}

// io action-safety that FIRES on bioreac2 (register@2, setwaker@4, io-ready@7, wake@8).
#[verifier::rlimit(50)]
proof fn bioreac2_io_fires()
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::set_waker_active_io::set_waker_active_io(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_ready_in_park::io_ready_in_park(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_waker_validity::io_waker_validity(), bioreac2()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::wake_has_registration::wake_has_registration(), bioreac2()),
{
  let l = bioreac2();
  bioreac2_idx();

  let pu = crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(pu, l)) by {
    assert forall |i: int| #[trigger] (pu.acceptance)(l, i) implies (pu.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 2 {
        assert forall |k: int| 0 <= k < 2 && rl::io_syscall_registered_at(l, k) &&
          re::get_io_syscall_register_rid(l[k]) == RIO()
          implies exists |jj: int| k < jj < 2 && #[trigger] rl::io_syscall_deregistered_at(l, jj) &&
            re::get_io_syscall_deregister_rid(l[jj]) == RIO() by { bioreac2_flags(k); }
        crate::reactor::invariants::io_reg_uniqueness::intro_no_prior_io_syscall_registration(l, RIO(), 2);
      }
    }
  }
  let pd = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io();
  assert(crate::framework::action_safety::action_safety_satisfied(pd, l)) by {
    assert forall |i: int| #[trigger] (pd.acceptance)(l, i) implies (pd.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 2 {
        assert forall |k: int| 0 <= k < 2 && rl::is_succ_register_timer_at(l, k) &&
          re::get_register_timer_rid(l[k]) == RIO()
          implies exists |jj: int| k < jj < 2 && #[trigger] rl::timer_retired_at(l, RIO(), jj) by { bioreac2_flags(k); }
        crate::reactor::invariants::timer_io_disjoint::intro_no_timer_with_rid_before(l, RIO(), 2);
      }
    }
  }
  let pr = crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(pr, l)) by {
    assert forall |i: int| #[trigger] (pr.acceptance)(l, i) implies (pr.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 2 {
        assert(crate::reactor::invariants::register_io_in_cycle::find_last_inbound_register_io_begin(l, 2) == 1);
        assert(crate::reactor::invariants::register_io_in_cycle::no_inbound_register_io_end_between(l, 1, 2));
      }
    }
  }
  let pi = crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(pi, l)) by {
    assert forall |i: int| #[trigger] (pi.acceptance)(l, i) implies (pi.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 3 {
        assert(crate::reactor::invariants::inbound_register_io_result::find_register_io_cycle_begin(l, 2) == 1);
        assert(crate::reactor::invariants::inbound_register_io_result::find_register_io_cycle_begin(l, 3) == 1);
        assert(crate::reactor::invariants::inbound_register_io_result::has_matching_outbound_register(
          l, 1, 3, SRC(), READABLE(), IoResultView::Ok(RIO()))) by {
          assert(crate::reactor::invariants::inbound_register_io_result::inbound_result_matches_outbound_register(
            IoResultView::Ok(RIO()), IoResultView::Ok(()), RIO()));
        }
      }
    }
  }
  let ps = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert(crate::framework::action_safety::action_safety_satisfied(ps, l)) by {
    assert forall |i: int| #[trigger] (ps.acceptance)(l, i) implies (ps.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 4 {
        assert(crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, RIO(), 3) == 2);
        assert(crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, RIO(), 4) == 2);
        bioreac2_io_active_from2(4);
      }
    }
  }
  let pk = crate::reactor::invariants::io_ready_in_park::io_ready_in_park();
  assert(crate::framework::action_safety::action_safety_satisfied(pk, l)) by {
    assert forall |i: int| #[trigger] (pk.acceptance)(l, i) implies (pk.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 7 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(rl::current_park_start(l, 4) == 0);
        assert(rl::current_park_start(l, 5) == 0);
        assert(rl::current_park_start(l, 6) == 0);
        assert(rl::current_park_start(l, 7) == 0);
      }
    }
  }
  let pw = crate::reactor::invariants::io_waker_validity::io_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(pw, l)) by {
    assert forall |i: int| #[trigger] (pw.acceptance)(l, i) implies (pw.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 8 {
        assert(crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, RIO(), 3) == 2);
        assert(crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, RIO(), 4) == 2);
        bioreac2_io_active_from2(4);
        assert(crate::reactor::invariants::io_waker_validity::io_syscall_active_at_set_waker(l, RIO(), 4));
        assert(rl::is_succ_set_waker_at(l, 4) && re::get_set_waker_rid(l[4]) == RIO() &&
          re::get_set_waker_waker(l[4]) == WK());
      }
    }
  }
  let ph = crate::reactor::invariants::wake_has_registration::wake_has_registration();
  assert(crate::framework::action_safety::action_safety_satisfied(ph, l)) by {
    assert forall |i: int| #[trigger] (ph.acceptance)(l, i) implies (ph.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 8 {
        bioreac2_io_active_from2(8);
        assert(crate::reactor::invariants::io_waker_validity::is_io_syscall_wake_at(l, 8));
      }
    }
  }
}

pub proof fn bioreac2_reac_inv()
  ensures
    crate::reactor::invariants::reactor_inv(bioreac2()),
{
  let l = bioreac2();
  bioreac2_idx();

  // park_has_timestamp: park ends @9 (GCT@5) and @13 (GCT@11).
  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 9 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(rl::current_park_start(l, 4) == 0);
        assert(rl::current_park_start(l, 5) == 0);
        assert(rl::current_park_start(l, 6) == 0);
        assert(rl::current_park_start(l, 7) == 0);
        assert(rl::current_park_start(l, 8) == 0);
        assert(rl::current_park_start(l, 9) == 0);
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 9));
      } else if i == 13 {
        assert(rl::current_park_start(l, 11) == 10);
        assert(rl::current_park_start(l, 12) == 10);
        assert(rl::current_park_start(l, 13) == 10);
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 13));
      }
    }
  }
  // park_poll_once: PollEvents @6 and @12.
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      bioreac2_flags(i);
      if i == 9 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(rl::current_park_start(l, 4) == 0);
        assert(rl::current_park_start(l, 5) == 0);
        assert(rl::current_park_start(l, 6) == 0);
        assert(rl::current_park_start(l, 7) == 0);
        assert(rl::current_park_start(l, 8) == 0);
        assert(rl::current_park_start(l, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 9, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 8, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 7, 9) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 6, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 5, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 4, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 3, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 2, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 1, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 0, 9) == 1);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, 9));
      } else if i == 13 {
        assert(rl::current_park_start(l, 11) == 10);
        assert(rl::current_park_start(l, 12) == 10);
        assert(rl::current_park_start(l, 13) == 10);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 13, 13) == 0);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 12, 13) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 11, 13) == 1);
        assert(crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, 10, 13) == 1);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, 13));
      }
    }
  }
  bioreac2_vacuous_as();
  bioreac2_io_fires();

  // local liveness: wake_on_io_ready_readable fires @7 (wake@8); others vacuous.
  let q1 = crate::reactor::invariants::wake_on_expired::wake_on_expired();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q1, l)) by {
    assert forall |i: int| #[trigger] (q1.acceptance)(l, i) implies
      exists |j: int| #![trigger (q1.fulfillment)(l, i, j)]
        j > i && (q1.fulfillment)(l, i, j) && (q1.timely)(l, i, j) by { bioreac2_flags(i); } }
  let q2 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_readable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q2, l)) by {
    assert forall |i: int| #[trigger] (q2.acceptance)(l, i) implies
      exists |j: int| #![trigger (q2.fulfillment)(l, i, j)]
        j > i && (q2.fulfillment)(l, i, j) && (q2.timely)(l, i, j) by {
      bioreac2_flags(i);
      if i == 7 {
        assert(crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(l, RIO(), 5) == 4);
        assert(crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(l, RIO(), 6) == 4);
        assert(crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(l, RIO(), 7) == 4);
        assert((q2.fulfillment)(l, 7, 8) && (q2.timely)(l, 7, 8)) by {
          assert(rl::is_wake_task_at(l, 8));
          assert(re::get_wake_task_source_rid(l[8]) == RIO());
          assert(re::get_wake_task_waker(l[8]) == WK());
          assert(re::get_set_waker_waker(l[4]) == WK());
          assert forall |k: int| 7 < k < 8 implies
            !(rl::is_park_end_at(l, k) || rl::is_poll_events_at(l, k)) by { bioreac2_flags(k); }
        }
        assert(8 > 7 && (q2.fulfillment)(l, 7, 8) && (q2.timely)(l, 7, 8));
      }
    }
  }
  let q3 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_writable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q3, l)) by {
    assert forall |i: int| #[trigger] (q3.acceptance)(l, i) implies
      exists |j: int| #![trigger (q3.fulfillment)(l, i, j)]
        j > i && (q3.fulfillment)(l, i, j) && (q3.timely)(l, i, j) by { bioreac2_flags(i); } }
}

// reactor_progress ∅ → bioreac1: the whole log is one complete park cycle [0, 10).
pub proof fn bioreac1_reac_progress()
  ensures
    crate::reactor::reactor_progress(Seq::<re::ReactorEvent>::empty(), bioreac1()),
{
  let l = bioreac1();
  bioreac1_idx();
  bioreac1_reac_inv();
  assert(Seq::<re::ReactorEvent>::empty() =~= l.subrange(0, 0));
  assert(crate::reactor::is_complete_park_cycle(l, 0, 10)) by {
    assert(rl::is_park_begin_at(l, 0));
    assert(rl::is_park_end_at(l, 9));
    assert forall |k: int| 0 < k < 9 implies
      !#[trigger] rl::is_park_begin_at(l, k) && !rl::is_park_end_at(l, k) by { bioreac1_flags(k); }
  }
  assert(exists |ps: int, pe: int|
    0 <= ps && ps < pe && pe <= l.len() &&
    crate::reactor::is_complete_park_cycle(l, ps, pe) &&
    (forall |i: int| 0 <= i < ps ==> re::is_inbound_non_park(#[trigger] l[i])) &&
    (forall |i: int| pe <= i < l.len() ==> re::is_inbound_non_park(#[trigger] l[i]))) by {
    assert(crate::reactor::is_complete_park_cycle(l, 0, 10));
  }
}

// reactor_progress bioreac1 → bioreac2: append the complete park cycle [10, 14).
pub proof fn bioreac2_reac_progress()
  ensures
    crate::reactor::reactor_progress(bioreac1(), bioreac2()),
{
  let l1 = bioreac1();
  let l2 = bioreac2();
  bioreac2_idx();
  bioreac1_idx();
  bioreac2_reac_inv();
  assert(l1 =~= l2.subrange(0, 10));
  assert(crate::reactor::is_complete_park_cycle(l2, 10, 14)) by {
    assert(rl::is_park_begin_at(l2, 10));
    assert(rl::is_park_end_at(l2, 13));
    assert forall |k: int| 10 < k < 13 implies
      !#[trigger] rl::is_park_begin_at(l2, k) && !rl::is_park_end_at(l2, k) by { bioreac2_flags(k); }
  }
  assert(exists |ps: int, pe: int|
    10 <= ps && ps < pe && pe <= l2.len() &&
    crate::reactor::is_complete_park_cycle(l2, ps, pe) &&
    (forall |i: int| 10 <= i < ps ==> re::is_inbound_non_park(#[trigger] l2[i])) &&
    (forall |i: int| pe <= i < l2.len() ==> re::is_inbound_non_park(#[trigger] l2[i]))) by {
    assert(crate::reactor::is_complete_park_cycle(l2, 10, 14));
  }
}

// ============================================================================
// Task log (io): Poll(begin), RegisterIo(RIO), SetWaker(RIO), Poll(Pending/Ready).
// Two reactor ops: RegisterIo@1 (→ reactor@2), SetWaker@2 (→ reactor@4).
// ============================================================================

pub open spec fn biotask_pending() -> ul::Log {
  seq![
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    ue::UtilityEvent::Outbound(ue::OutboundCall::RegisterIo {
      resource_id: RIO(), interest: ue::Interest::Readable,
    }),
    ue::UtilityEvent::Outbound(ue::OutboundCall::SetWaker {
      resource_id: RIO(), interest: ue::Interest::Readable, result: Some(()),
    }),
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll {
      result: Some(ue::PollResult::Pending),
    }),
  ]
}

pub open spec fn biotask_ready() -> ul::Log {
  biotask_pending() + seq![
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll {
      result: Some(ue::PollResult::Ready),
    }),
  ]
}

pub proof fn biotask_idx()
  ensures
    biotask_pending().len() == 4,
    biotask_ready().len() == 6,
    forall |i: int| 0 <= i < 4 ==> biotask_ready()[i] == biotask_pending()[i],
    ue::is_poll_begin(biotask_pending()[0]),
    ue::is_register_io(biotask_pending()[1]),
    ue::get_resource_id(biotask_pending()[1]) == Some(RIO()),
    ue::is_succ_set_waker(biotask_pending()[2]),
    ue::get_resource_id(biotask_pending()[2]) == Some(RIO()),
    ue::is_poll_end_pending(biotask_pending()[3]),
    ue::is_poll_begin(biotask_ready()[4]),
    ue::is_poll_end(biotask_ready()[5]),
    !ue::is_poll_end_pending(biotask_ready()[5]),
{
}

// is_reactor_operation(biotask[i]) <==> i == 1 (RegisterIo) || i == 2 (SetWaker).
pub proof fn biotask_op_facts()
  ensures
    forall |i: int| #![trigger biotask_ready()[i]] 0 <= i < biotask_ready().len() ==>
      (crate::composed::spec::alignment::is_reactor_operation(biotask_ready()[i]) <==> (i == 1 || i == 2)),
    forall |i: int| #![trigger biotask_pending()[i]] 0 <= i < biotask_pending().len() ==>
      (crate::composed::spec::alignment::is_reactor_operation(biotask_pending()[i]) <==> (i == 1 || i == 2)),
    crate::composed::spec::alignment::is_reactor_operation(biotask_pending()[1]),
    crate::composed::spec::alignment::is_reactor_operation(biotask_pending()[2]),
    ue::is_register_io(biotask_pending()[1]) && !ue::is_succ_set_waker(biotask_pending()[1]) &&
      !ue::is_deregister_io(biotask_pending()[1]),
    ue::is_succ_set_waker(biotask_pending()[2]) && !ue::is_register_io(biotask_pending()[2]) &&
      !ue::is_deregister_io(biotask_pending()[2]),
{
  biotask_idx();
  assert forall |i: int| #![trigger biotask_ready()[i]] 0 <= i < biotask_ready().len() implies
    (crate::composed::spec::alignment::is_reactor_operation(biotask_ready()[i]) <==> (i == 1 || i == 2)) by {
    if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {}
  }
  assert forall |i: int| #![trigger biotask_pending()[i]] 0 <= i < biotask_pending().len() implies
    (crate::composed::spec::alignment::is_reactor_operation(biotask_pending()[i]) <==> (i == 1 || i == 2)) by {
    if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {}
  }
}

// reactor@2 (RegisterIo) matches biotask[1]; reactor@4 (SetWaker) matches biotask[2].
pub proof fn bioreg_matches(tid: TID)
  ensures
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      bioreac1()[2], biotask_pending()[1]),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      bioreac1()[4], biotask_pending()[2]),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      bioreac2()[2], biotask_ready()[1]),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      bioreac2()[4], biotask_ready()[2]),
{
  bioreac1_idx(); bioreac2_idx(); biotask_idx();
}

// ============================================================================
// Composed states (reuse the generic executor logs bexec1/bexec2)
// ============================================================================

pub open spec fn bios1(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: bexec1(tid),
    reactor_log: bioreac1(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, biotask_pending()),
    injection_schedule: bsched(tid),
  }
}

pub open spec fn bios2(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: bexec2(tid),
    reactor_log: bioreac2(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, biotask_ready()),
    injection_schedule: bsched(tid),
  }
}

// utilities_inv for the io task logs: PollEnd(Pending)@3 has an active io wakeup
// source (RegisterIo@1 + SetWaker@2 in the current poll); resource_ownership at
// SetWaker@2 targets an io resource registered earlier in the same log.
pub proof fn biotask_utilities_inv()
  ensures
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(biotask_pending()),
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(biotask_ready()),
{
  biotask_idx();
  use crate::utilities::invariants::wakeup_guarantee::*;
  let wg = wakeup_guarantee();
  let ro = crate::utilities::invariants::resource_ownership::resource_ownership();

  assert(crate::framework::action_safety::action_safety_satisfied(wg, biotask_pending())) by {
    assert forall |i: int| #[trigger] (wg.acceptance)(biotask_pending(), i) implies (wg.validity)(biotask_pending(), i) by {
      if i == 3 {
        assert(crate::utilities::spec::log::current_poll_start(biotask_pending(), 3) == 0) by {
          assert(ue::is_poll_begin(biotask_pending()[0]));
          assert(crate::utilities::spec::log::find_last_poll_begin(biotask_pending(), 0) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(biotask_pending(), 1) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(biotask_pending(), 2) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(biotask_pending(), 3) == 0);
        }
        assert(crate::utilities::spec::log::has_active_io_with_waker(biotask_pending(), 3)) by {
          assert(crate::utilities::spec::log::is_io_active(biotask_pending(), RIO(), 3)) by {
            assert(crate::utilities::spec::log::is_io_registered_before(biotask_pending(), RIO(), 3)) by {
              assert(ue::is_register_io(biotask_pending()[1]) && ue::get_resource_id(biotask_pending()[1]) == Some(RIO()));
            }
            assert(!crate::utilities::spec::log::is_io_deregistered_before(biotask_pending(), RIO(), 3)) by {
              assert forall |j: int| #![trigger biotask_pending()[j]] 0 <= j < 3 implies
                !(ue::is_deregister_io(biotask_pending()[j]) && ue::get_resource_id(biotask_pending()[j]) == Some(RIO())) by {}
            }
          }
          assert(crate::utilities::spec::log::has_waker_set_in_current_poll(biotask_pending(), RIO(), 3)) by {
            assert(crate::utilities::spec::log::in_current_poll_cycle(biotask_pending(), 2, 3));
            assert(ue::is_succ_set_waker(biotask_pending()[2]) && ue::get_resource_id(biotask_pending()[2]) == Some(RIO()));
          }
        }
        assert(crate::utilities::spec::log::has_active_wakeup_source(biotask_pending(), 3));
      }
    }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(ro, biotask_pending())) by {
    assert forall |i: int| #[trigger] (ro.acceptance)(biotask_pending(), i) implies (ro.validity)(biotask_pending(), i) by {
      if i == 2 {
        assert(crate::utilities::invariants::resource_ownership::io_active_before(biotask_pending(), RIO(), 2)) by {
          assert(ue::is_register_io(biotask_pending()[1]) && ue::get_resource_id(biotask_pending()[1]) == Some(RIO()));
        }
      }
    }
  }
  // biotask_ready: same current poll for @3; the extra poll [4,6) adds no reactor op.
  assert(crate::framework::action_safety::action_safety_satisfied(wg, biotask_ready())) by {
    assert forall |i: int| #[trigger] (wg.acceptance)(biotask_ready(), i) implies (wg.validity)(biotask_ready(), i) by {
      if i == 3 {
        assert(crate::utilities::spec::log::current_poll_start(biotask_ready(), 3) == 0) by {
          assert(ue::is_poll_begin(biotask_ready()[0]));
          assert(crate::utilities::spec::log::find_last_poll_begin(biotask_ready(), 0) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(biotask_ready(), 1) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(biotask_ready(), 2) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(biotask_ready(), 3) == 0);
        }
        assert(crate::utilities::spec::log::has_active_io_with_waker(biotask_ready(), 3)) by {
          assert(crate::utilities::spec::log::is_io_active(biotask_ready(), RIO(), 3)) by {
            assert(crate::utilities::spec::log::is_io_registered_before(biotask_ready(), RIO(), 3)) by {
              assert(ue::is_register_io(biotask_ready()[1]) && ue::get_resource_id(biotask_ready()[1]) == Some(RIO()));
            }
            assert(!crate::utilities::spec::log::is_io_deregistered_before(biotask_ready(), RIO(), 3)) by {
              assert forall |j: int| #![trigger biotask_ready()[j]] 0 <= j < 3 implies
                !(ue::is_deregister_io(biotask_ready()[j]) && ue::get_resource_id(biotask_ready()[j]) == Some(RIO())) by {}
            }
          }
          assert(crate::utilities::spec::log::has_waker_set_in_current_poll(biotask_ready(), RIO(), 3)) by {
            assert(crate::utilities::spec::log::in_current_poll_cycle(biotask_ready(), 2, 3));
            assert(ue::is_succ_set_waker(biotask_ready()[2]) && ue::get_resource_id(biotask_ready()[2]) == Some(RIO()));
          }
        }
        assert(crate::utilities::spec::log::has_active_wakeup_source(biotask_ready(), 3));
      }
    }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(ro, biotask_ready())) by {
    assert forall |i: int| #[trigger] (ro.acceptance)(biotask_ready(), i) implies (ro.validity)(biotask_ready(), i) by {
      if i == 2 {
        assert(crate::utilities::invariants::resource_ownership::io_active_before(biotask_ready(), RIO(), 2)) by {
          assert(ue::is_register_io(biotask_ready()[1]) && ue::get_resource_id(biotask_ready()[1]) == Some(RIO()));
        }
      }
    }
  }
}

// monotonic_task_reactor_alignment for the io witness (two ordered reactor ops:
// RegisterIo@task1 → reactor@2, SetWaker@task2 → reactor@4).
proof fn bio_monotonic(s: ComposedState, tid: TID)
  requires
    s.task_logs.contains_key(tid),
    s.task_logs[tid] == biotask_pending() || s.task_logs[tid] == biotask_ready(),
    forall |t2: TaskId| s.task_logs.contains_key(t2) ==> t2 == tid,
    s.reactor_log == bioreac1() || s.reactor_log == bioreac2(),
  ensures
    crate::composed::spec::alignment::monotonic_task_reactor_alignment(s),
{
  biotask_idx(); biotask_op_facts(); bioreac1_idx(); bioreac2_idx();
  use crate::composed::spec::alignment::*;
  let is1 = s.reactor_log == bioreac1();
  assert forall |t2: TaskId, a: int, b: int, ra: int, rb: int|
    #![trigger succ_reactor_event_matches_task_operation(s.reactor_log[ra], s.task_logs[t2][a]),
               succ_reactor_event_matches_task_operation(s.reactor_log[rb], s.task_logs[t2][b])]
    s.task_logs.contains_key(t2) &&
    0 <= a < b && b < s.task_logs[t2].len() &&
    is_reactor_operation(s.task_logs[t2][a]) &&
    is_reactor_operation(s.task_logs[t2][b]) &&
    0 <= ra < s.reactor_log.len() &&
    0 <= rb < s.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(s.reactor_log[ra], s.task_logs[t2][a]) &&
    succ_reactor_event_matches_task_operation(s.reactor_log[rb], s.task_logs[t2][b])
    implies ra < rb by {
    assert(t2 == tid);
    assert(a == 1 && b == 2);
    // task[1] = RegisterIo(RIO) matches only reactor@2; task[2] = SetWaker(RIO) only reactor@4.
    if is1 { bioreac1_flags(ra); bioreac1_flags(rb); } else { bioreac2_flags(ra); bioreac2_flags(rb); }
    assert(ra == 2);
    assert(rb == 4);
  }
  intro_monotonic_task_reactor_alignment(s);
}

// action_mediation_state for the io witness.
#[verifier::rlimit(100)]
proof fn bio_am_state(s: ComposedState, tid: TID)
  requires
    s.task_logs.contains_key(tid),
    (s.reactor_log == bioreac1() && s.task_logs[tid] == biotask_pending()) ||
    (s.reactor_log == bioreac2() && s.task_logs[tid] == biotask_ready()),
    forall |t2: TaskId| s.task_logs.contains_key(t2) ==> t2 == tid,
  ensures
    crate::composed::spec::alignment::action_mediation_state(s),
{
  bioreac1_idx(); bioreac2_idx(); biotask_idx(); biotask_op_facts(); bioreg_matches(tid);
  use crate::composed::spec::alignment::*;
  let is1 = s.reactor_log == bioreac1();

  // operation_to_reactor_exists: task op @1 → reactor@2, @2 → reactor@4.
  assert(operation_to_reactor_exists(s)) by {
    assert forall |t2: TaskId, i: int|
      s.task_logs.contains_key(t2) && 0 <= i < s.task_logs[t2].len() &&
      is_reactor_operation(#[trigger] s.task_logs[t2][i])
      implies exists |j: int| 0 <= j < s.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][i]) by {
      assert(t2 == tid);
      assert(i == 1 || i == 2);
      if i == 1 {
        assert(0 <= 2 < s.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s.reactor_log[2], s.task_logs[t2][1]));
      } else {
        assert(0 <= 4 < s.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s.reactor_log[4], s.task_logs[t2][2]));
      }
    }
  }
  // reactor_registration_to_task_exists: succ_register@2 (io) → biotask[1].
  assert(reactor_registration_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() &&
      (re::is_succ_register_timer(s.reactor_log[j]) || re::is_succ_io_syscall_register(s.reactor_log[j]))
      implies exists |t2: TaskId, ti: int| s.task_logs.contains_key(t2) &&
        0 <= ti < s.task_logs[t2].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][ti]) by {
      if is1 { bioreac1_flags(j); } else { bioreac2_flags(j); }
      assert(j == 2);
      assert(s.task_logs.contains_key(tid) && 0 <= 1 < s.task_logs[tid].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[2], s.task_logs[tid][1]));
    }
  }
  // reactor_outbound_to_task_exists: task-initiated @2 (io reg) → biotask[1], @4 (setwaker) → biotask[2].
  assert(reactor_outbound_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() && is_task_initiated_reactor_event(s.reactor_log[j])
      implies exists |t2: TaskId, ti: int| s.task_logs.contains_key(t2) &&
        0 <= ti < s.task_logs[t2].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][ti]) by {
      if is1 { bioreac1_flags(j); } else { bioreac2_flags(j); }
      assert(j == 2 || j == 4);
      if j == 2 {
        assert(s.task_logs.contains_key(tid) && 0 <= 1 < s.task_logs[tid].len() &&
          succ_reactor_event_matches_task_operation(s.reactor_log[2], s.task_logs[tid][1]));
      } else {
        assert(s.task_logs.contains_key(tid) && 0 <= 2 < s.task_logs[tid].len() &&
          succ_reactor_event_matches_task_operation(s.reactor_log[4], s.task_logs[tid][2]));
      }
    }
  }
  // reactor_to_operation_unique: RegisterIo matches only @2, SetWaker only @4 ⟹ same op.
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
      assert(t1 == tid && t2 == tid);
      assert(ti1 == 1 || ti1 == 2);
      assert(ti2 == 1 || ti2 == 2);
      if is1 { bioreac1_flags(ri); } else { bioreac2_flags(ri); }
      // ri is 2 or 4; RegisterIo op (ti==1) matches only @2, SetWaker op (ti==2) only @4.
      assert(ti1 == ti2);
    }
  }
  bio_monotonic(s, tid);
  assert(succ_deregister_by_owner(s)) by { reveal(succ_deregister_by_owner); }
  assert(deregister_matches_own_registration(s)) by { reveal(deregister_matches_own_registration); }
  assert(deregister_io_matches_own_registration(s)) by { reveal(deregister_io_matches_own_registration); }
  assert(succ_deregister_io_by_owner(s)) by { reveal(succ_deregister_io_by_owner); }
}

// ============================================================================
// Observation consistency + park alignment
// ============================================================================

proof fn bio1_obs_consistency(tid: TID)
  ensures
    crate::composed::spec::alignment::observation_consistency_state(bios1(tid)),
    crate::composed::spec::alignment::observation_consistency_step(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bios1(tid)),
{
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = bios1(tid);
  bexec1_idx(tid); biotask_idx();
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
        assert(s2.task_logs[tid] == biotask_pending());
        assert(ue::is_poll_end_pending(biotask_pending()[3]));
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
        assert(s2.task_logs[tid] == biotask_pending());
        assert(ue::is_poll_end_pending(biotask_pending()[3]));
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

proof fn bio2_obs_consistency(tid: TID)
  ensures
    crate::composed::spec::alignment::observation_consistency_state(bios2(tid)),
    crate::composed::spec::alignment::observation_consistency_step(bios1(tid), bios2(tid)),
{
  let s = bios1(tid);
  let s2 = bios2(tid);
  bexec2_idx(tid); bexec1_idx(tid); biotask_idx();
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
        bexec2_flags(tid, i);
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
        assert(s.task_logs[tid] == biotask_pending() && s2.task_logs[tid] == biotask_ready());
      }
    }
  }
}

proof fn bio1_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bios1(tid)),
{
  bexec1_idx(tid); bioreac1_idx();
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
  let r = bioreac1();
  assert(count_park_cycles_in(r, 10, 10) == 0);
  assert(count_park_cycles_in(r, 9, 10) == 1) by { bioreac1_flags(9); }
  assert(count_park_cycles_in(r, 8, 10) == 1) by { bioreac1_flags(8); }
  assert(count_park_cycles_in(r, 7, 10) == 1) by { bioreac1_flags(7); }
  assert(count_park_cycles_in(r, 6, 10) == 1) by { bioreac1_flags(6); }
  assert(count_park_cycles_in(r, 5, 10) == 1) by { bioreac1_flags(5); }
  assert(count_park_cycles_in(r, 4, 10) == 1) by { bioreac1_flags(4); }
  assert(count_park_cycles_in(r, 3, 10) == 1) by { bioreac1_flags(3); }
  assert(count_park_cycles_in(r, 2, 10) == 1) by { bioreac1_flags(2); }
  assert(count_park_cycles_in(r, 1, 10) == 1) by { bioreac1_flags(1); }
  assert(count_park_cycles_in(r, 0, 10) == 1) by { bioreac1_flags(0); }
}

proof fn bio2_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(bios1(tid), bios2(tid)),
{
  bexec2_idx(tid); bioreac2_idx();
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
  let r = bioreac2();
  assert(count_park_cycles_in(r, 14, 14) == 0);
  assert(count_park_cycles_in(r, 13, 14) == 1) by { bioreac2_flags(13); }
  assert(count_park_cycles_in(r, 12, 14) == 1) by { bioreac2_flags(12); }
  assert(count_park_cycles_in(r, 11, 14) == 1) by { bioreac2_flags(11); }
  assert(count_park_cycles_in(r, 10, 14) == 1) by { bioreac2_flags(10); }
}

// ============================================================================
// io env facts: the io-readiness assumption io_ready_forward_here holds for EVERY
// bound n (in particular the uninterpreted get_io_ready_bound used by env_N),
// NON-VACUOUSLY for RIO: the CONSEQUENT is concrete — IoEventReady@7 follows
// SetWaker@4 in tick 1 of both bios logs. Other rids have no SetWaker (vacuous).
// ============================================================================
#[verifier::rlimit(100)]
proof fn bio_reac_env_facts(s: ComposedState, tid: TID)
  requires
    (s.reactor_log == bioreac1() && s.executor_log == bexec1(tid) &&
     s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, biotask_pending()) &&
     s.injection_schedule == bsched(tid)) ||
    (s.reactor_log == bioreac2() && s.executor_log == bexec2(tid) &&
     s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, biotask_ready()) &&
     s.injection_schedule == bsched(tid)),
  ensures
    crate::composed::spec::assumptions::timestamps_strictly_increasing(s.reactor_log),
    crate::reactor::timestamps_positive(s.reactor_log),
    timer_deadline_gap_bounded(s, tid),
    timer_resources_remain_active(s),
    crate::composed::proof::assumption_satisfiable::contract_io_assumption_here(s),
    forall |rid: ResourceIdView, n: nat|
      #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
      io_ready_forward_here(s.reactor_log, rid, n),
{
  bioreac1_idx(); bioreac2_idx();
  let l = s.reactor_log;
  let is1 = l == bioreac1();
  use crate::reactor::contracts::bounded_io_wakeup::{find_last_set_waker_for_rid,
    has_io_event_ready_matching_interest_after, io_remains_active_assumption};

  assert(crate::composed::spec::assumptions::timestamps_strictly_increasing(l)) by {
    assert forall |a: int, b: int| 0 <= a < b < l.len() &&
      rl::is_get_current_time_at(l, a) && rl::is_get_current_time_at(l, b)
      implies re::get_current_timestamp(l[a]) < re::get_current_timestamp(l[b]) by {
      if is1 { bioreac1_flags(a); bioreac1_flags(b); } else { bioreac2_flags(a); bioreac2_flags(b); }
    }
  }
  assert(crate::reactor::timestamps_positive(l)) by {
    assert forall |a: int| 0 <= a < l.len() && rl::is_get_current_time_at(l, a)
      implies re::get_current_timestamp(l[a]) >= 1 by {
      if is1 { bioreac1_flags(a); } else { bioreac2_flags(a); }
    }
  }
  assert(timer_deadline_gap_bounded(s, tid)) by {
    reveal(timer_deadline_gap_bounded);
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < l.len() && rl::is_succ_register_timer_at(l, reg_idx) implies false by {
      if is1 { bioreac1_flags(reg_idx); } else { bioreac2_flags(reg_idx); }
    }
  }
  assert(timer_resources_remain_active(s)) by {
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < l.len() && rl::is_succ_register_timer_at(l, reg_idx) implies false by {
      if is1 { bioreac1_flags(reg_idx); } else { bioreac2_flags(reg_idx); }
    }
  }
  // contract_io_assumption_here: io_remains_active (no deregister).
  assert(crate::composed::proof::assumption_satisfiable::contract_io_assumption_here(s)) by {
    assert forall |rid: ResourceIdView|
      #![trigger crate::composed::proof::assumption_satisfiable::io_assumption_here(s.reactor_log, rid)]
      crate::composed::proof::assumption_satisfiable::io_assumption_here(s.reactor_log, rid) by {
      assert(io_remains_active_assumption(l, rid)) by {
        let sw = find_last_set_waker_for_rid(l, rid, l.len() as int);
        assert forall |j: int| 0 <= j < l.len() implies !rl::io_syscall_deregistered_at(l, j) by {
          if is1 { bioreac1_flags(j); } else { bioreac2_flags(j); }
        }
      }
    }
  }
  // io_ready_forward_here for EVERY n: for RIO the consequent holds concretely
  // (IoEventReady@7 after SetWaker@4); other rids have no SetWaker (sw = -1).
  assert forall |rid: ResourceIdView, n: nat|
    #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
    io_ready_forward_here(s.reactor_log, rid, n) by {
    if rid == RIO() {
      assert(find_last_set_waker_for_rid(l, RIO(), 5) == 4) by {
        if is1 { bioreac1_flags(4); } else { bioreac2_flags(4); } }
      assert(find_last_set_waker_for_rid(l, RIO(), 6) == 4) by {
        if is1 { bioreac1_flags(5); } else { bioreac2_flags(5); } }
      assert(find_last_set_waker_for_rid(l, RIO(), 7) == 4) by {
        if is1 { bioreac1_flags(6); } else { bioreac2_flags(6); } }
      assert(find_last_set_waker_for_rid(l, RIO(), 8) == 4) by {
        if is1 { bioreac1_flags(7); } else { bioreac2_flags(7); } }
      assert(find_last_set_waker_for_rid(l, RIO(), 9) == 4) by {
        if is1 { bioreac1_flags(8); } else { bioreac2_flags(8); } }
      assert(find_last_set_waker_for_rid(l, RIO(), 10) == 4) by {
        if is1 { bioreac1_flags(9); } else { bioreac2_flags(9); } }
      if !is1 {
        assert(find_last_set_waker_for_rid(l, RIO(), 11) == 4) by { bioreac2_flags(10); }
        assert(find_last_set_waker_for_rid(l, RIO(), 12) == 4) by { bioreac2_flags(11); }
        assert(find_last_set_waker_for_rid(l, RIO(), 13) == 4) by { bioreac2_flags(12); }
        assert(find_last_set_waker_for_rid(l, RIO(), 14) == 4) by { bioreac2_flags(13); }
      }
      assert(has_io_event_ready_matching_interest_after(l, RIO(), re::get_set_waker_interest(l[4]), 4)) by {
        if is1 { bioreac1_flags(4); bioreac1_flags(7); } else { bioreac2_flags(4); bioreac2_flags(7); }
        assert(4 <= 7 < l.len() && rl::is_io_event_ready_at(l, 7) &&
          re::get_io_event(l[7]).resource_id == RIO() &&
          re::get_set_waker_interest(l[4]).0 && re::get_io_event(l[7]).readable);
      }
    } else {
      assert(find_last_set_waker_for_rid(l, rid, 0) == -1);
      assert(find_last_set_waker_for_rid(l, rid, 1) == -1) by {
        if is1 { bioreac1_flags(0); } else { bioreac2_flags(0); } }
      assert(find_last_set_waker_for_rid(l, rid, 2) == -1) by {
        if is1 { bioreac1_flags(1); } else { bioreac2_flags(1); } }
      assert(find_last_set_waker_for_rid(l, rid, 3) == -1) by {
        if is1 { bioreac1_flags(2); } else { bioreac2_flags(2); } }
      assert(find_last_set_waker_for_rid(l, rid, 4) == -1) by {
        if is1 { bioreac1_flags(3); } else { bioreac2_flags(3); } }
      assert(find_last_set_waker_for_rid(l, rid, 5) == -1) by {
        if is1 { bioreac1_flags(4); } else { bioreac2_flags(4); } }
      assert(find_last_set_waker_for_rid(l, rid, 6) == -1) by {
        if is1 { bioreac1_flags(5); } else { bioreac2_flags(5); } }
      assert(find_last_set_waker_for_rid(l, rid, 7) == -1) by {
        if is1 { bioreac1_flags(6); } else { bioreac2_flags(6); } }
      assert(find_last_set_waker_for_rid(l, rid, 8) == -1) by {
        if is1 { bioreac1_flags(7); } else { bioreac2_flags(7); } }
      assert(find_last_set_waker_for_rid(l, rid, 9) == -1) by {
        if is1 { bioreac1_flags(8); } else { bioreac2_flags(8); } }
      assert(find_last_set_waker_for_rid(l, rid, 10) == -1) by {
        if is1 { bioreac1_flags(9); } else { bioreac2_flags(9); } }
      if !is1 {
        assert(find_last_set_waker_for_rid(l, rid, 11) == -1) by { bioreac2_flags(10); }
        assert(find_last_set_waker_for_rid(l, rid, 12) == -1) by { bioreac2_flags(11); }
        assert(find_last_set_waker_for_rid(l, rid, 13) == -1) by { bioreac2_flags(12); }
        assert(find_last_set_waker_for_rid(l, rid, 14) == -1) by { bioreac2_flags(13); }
      }
    }
  }
}

// Executor/queue env facts (reuse the generic bexec queue lemmas).
proof fn bio_common_env_facts(s: ComposedState, tid: TID)
  requires
    (s.reactor_log == bioreac1() && s.executor_log == bexec1(tid) &&
     s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, biotask_pending()) &&
     s.injection_schedule == bsched(tid)) ||
    (s.reactor_log == bioreac2() && s.executor_log == bexec2(tid) &&
     s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, biotask_ready()) &&
     s.injection_schedule == bsched(tid)),
    get_max_queue_length(s) >= 1,
  ensures
    el::tid_unique(s.executor_log, tid),
    queue_length_bounded(s),
{
  let is1 = s.executor_log == bexec1(tid);
  bexec1_idx(tid); bexec2_idx(tid); biotask_idx();
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

#[verifier::rlimit(100)]
proof fn bios1_env(tid: TID)
  requires
    get_max_queue_length(bios1(tid)) >= 1,
  ensures
    env_N(bios1(tid), tid, 2nat),
{
  let s = bios1(tid);
  bexec1_idx(tid); bioreac1_idx(); biotask_idx();
  bio_reac_env_facts(s, tid);
  bio_common_env_facts(s, tid);
  assert(bounded_poll_count_here_with_bound(s, tid, 2nat)) by { bpoll_count_bexec1(tid); }
  assert(env_holds_at_state_core(s, tid));
  assert(end_to_end_env(s, tid));
  assert(!crate::utilities::spec::log::has_pass_waker_in_current_poll(
    s.task_logs[tid], (s.task_logs[tid].len() - 1) as int)) by {
    let tl = s.task_logs[tid];
    assert(tl == biotask_pending());
    assert forall |j: int| #![trigger tl[j]] 0 <= j < tl.len() implies !ue::is_pass_waker(tl[j]) by {}
  }
  crate::composed::proof::assumption_satisfiable::taskwake_arrival_within_vacuous(s, tid, 2nat);
}

#[verifier::rlimit(100)]
proof fn bios2_env(tid: TID)
  requires
    get_max_queue_length(bios2(tid)) >= 1,
  ensures
    env_N(bios2(tid), tid, 2nat),
{
  let s = bios2(tid);
  bexec2_idx(tid); bioreac2_idx(); biotask_idx();
  bio_reac_env_facts(s, tid);
  bio_common_env_facts(s, tid);
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

// ============================================================================
// cross_module_alignment for both steps
// ============================================================================

#[verifier::rlimit(100)]
pub proof fn bios1_cross(tid: TID)
  ensures
    cross_module_alignment(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bios1(tid)),
{
  reveal(cross_module_alignment);
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = bios1(tid);
  bexec1_idx(tid); bioreac1_idx(); biotask_idx(); biotask_op_facts(); bioreg_matches(tid);
  use crate::composed::spec::alignment::*;

  bio_am_state(s2, tid);
  assert(is_new_task_operation(s, s2, tid, 1));
  assert(is_new_task_operation(s, s2, tid, 2));
  assert(action_mediation_step(s, s2)) by {
    assert(new_operation_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int|
        is_new_task_operation(s, s2, t2, i) && is_reactor_operation(#[trigger] s2.task_logs[t2][i])
        implies exists |j: int| s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][i]) by {
        assert(t2 == tid && (i == 1 || i == 2));
        if i == 1 {
          assert(0 <= 2 < s2.reactor_log.len() &&
            succ_reactor_event_matches_task_operation(s2.reactor_log[2], s2.task_logs[tid][1]));
        } else {
          assert(0 <= 4 < s2.reactor_log.len() &&
            succ_reactor_event_matches_task_operation(s2.reactor_log[4], s2.task_logs[tid][2]));
        }
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
        assert(t1 == tid && t2 == tid && (a1 == 1 || a1 == 2) && (a2 == 1 || a2 == 2));
        bioreac1_flags(ri);
        assert(a1 == a2);
      }
    }
    assert(new_op_matches_only_new_reactor(s, s2)) by {
      assert forall |t2: TaskId, ti: int, ri: int|
        is_new_task_operation(s, s2, t2, ti) && is_reactor_operation(#[trigger] s2.task_logs[t2][ti]) &&
        0 <= ri < s2.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(#[trigger] s2.reactor_log[ri], s2.task_logs[t2][ti])
        implies ri >= s.reactor_log.len() by { }
    }
    assert(reactor_outbound_has_task_operation(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          0 <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by {
        bioreac1_flags(j);
        assert(j == 2 || j == 4);
        if j == 2 {
          assert(s2.task_logs.contains_key(tid) && 0 <= 1 < s2.task_logs[tid].len() &&
            succ_reactor_event_matches_task_operation(s2.reactor_log[2], s2.task_logs[tid][1]));
        } else {
          assert(s2.task_logs.contains_key(tid) && 0 <= 2 < s2.task_logs[tid].len() &&
            succ_reactor_event_matches_task_operation(s2.reactor_log[4], s2.task_logs[tid][2]));
        }
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
        bioreac1_flags(j);
        assert(!s.task_logs.contains_key(tid));
        assert(j == 2 || j == 4);
        if j == 2 {
          assert(s2.task_logs.contains_key(tid) && 0int <= 1 < s2.task_logs[tid].len() &&
            succ_reactor_event_matches_task_operation(s2.reactor_log[2], s2.task_logs[tid][1]));
        } else {
          assert(s2.task_logs.contains_key(tid) && 0int <= 2 < s2.task_logs[tid].len() &&
            succ_reactor_event_matches_task_operation(s2.reactor_log[4], s2.task_logs[tid][2]));
        }
      }
    }
  }
  bio1_obs_consistency(tid);
  bio1_park_alignment(tid);
}

#[verifier::rlimit(100)]
pub proof fn bios2_cross(tid: TID)
  ensures
    cross_module_alignment(bios1(tid), bios2(tid)),
{
  reveal(cross_module_alignment);
  let s = bios1(tid);
  let s2 = bios2(tid);
  bexec2_idx(tid); bioreac2_idx(); biotask_idx(); biotask_op_facts(); bioreg_matches(tid);
  use crate::composed::spec::alignment::*;

  bio_am_state(s2, tid);
  // No new task-initiated reactor events (10≤j<14: Park/GCT/PollEvents/Park),
  // and the new task ops (biotask[4,5]) are poll markers, not reactor ops.
  assert(action_mediation_step(s, s2)) by {
    assert(new_operation_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int|
        is_new_task_operation(s, s2, t2, i) && is_reactor_operation(#[trigger] s2.task_logs[t2][i])
        implies exists |j: int| s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][i]) by {
        assert(t2 == tid);
        assert(i == 4 || i == 5);
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
        implies t1 == t2 && a1 == a2 by { assert(t1 == tid && (a1 == 4 || a1 == 5)); }
    }
    assert(new_op_matches_only_new_reactor(s, s2)) by {
      assert forall |t2: TaskId, ti: int, ri: int|
        is_new_task_operation(s, s2, t2, ti) && is_reactor_operation(#[trigger] s2.task_logs[t2][ti]) &&
        0 <= ri < s2.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(#[trigger] s2.reactor_log[ri], s2.task_logs[t2][ti])
        implies ri >= s.reactor_log.len() by { assert(t2 == tid && (ti == 4 || ti == 5)); }
    }
    assert(reactor_outbound_has_task_operation(s, s2)) by {
      assert forall |j: int| #![trigger s2.reactor_log[j]]
        s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
        is_task_initiated_reactor_event(s2.reactor_log[j])
        implies exists |t2: TaskId, ti: int| s2.task_logs.contains_key(t2) &&
          0 <= ti < s2.task_logs[t2].len() &&
          succ_reactor_event_matches_task_operation(s2.reactor_log[j], s2.task_logs[t2][ti]) by {
        bioreac2_flags(j);  // 10≤j<14: none task-initiated
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
        bioreac2_flags(j);
      }
    }
  }
  bio2_obs_consistency(tid);
  bio2_park_alignment(tid);
}

// ============================================================================
// composed_progress + the domain-inhabitation theorem
// ============================================================================

pub proof fn bios1_composed_progress(tid: TID)
  ensures
    composed_progress(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bios1(tid)),
{
  reveal(composed_progress);
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = bios1(tid);
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 0)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 0)); }
  assert(is_extension_of(s, s2));
  bexec1_exec_progress(tid);
  assert(s.executor_log =~= Seq::<ee::ExecutorEvent>::empty());
  bioreac1_reac_progress();
  assert(s.reactor_log =~= Seq::<re::ReactorEvent>::empty());
  bios1_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    biotask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(t2 == tid && s2.task_logs[t2] == biotask_pending());
    }
  }
  bio_monotonic(s2, tid);
  bpops_deliver(tid);
  crate::composed::proof::assumption_satisfiable::no_reactor_wake_pending_no_waketask(s);
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2));
  crate::composed::proof::assumption_satisfiable::no_taskwake_pending_no_woken(s);
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2));
}

pub proof fn bios2_composed_progress(tid: TID)
  ensures
    composed_progress(bios1(tid), bios2(tid)),
{
  reveal(composed_progress);
  let s = bios1(tid);
  let s2 = bios2(tid);
  bexec2_idx(tid); bioreac2_idx(); biotask_idx();
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 8)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 10)); }
  assert(is_extension_of(s, s2)) by {
    assert(s.task_logs[tid] == biotask_pending() && s2.task_logs[tid] == biotask_ready());
    assert(crate::composed::spec::state::is_task_log_prefix(biotask_pending(), biotask_ready()));
  }
  bexec2_exec_progress(tid);
  bioreac2_reac_progress();
  bios2_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    biotask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(t2 == tid && s2.task_logs[t2] == biotask_ready());
    }
  }
  bio_monotonic(s2, tid);
  bpops_deliver(tid);
  // reactor_wake_drain_step NON-VACUOUS: the io wake fired in tick 1 (WakeTask@8 in
  // bioreac1), so tid may be reactor-wake-pending at bios1; the step's only
  // Drain{ReactorWake} (@13) carries [tid].
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2)) by {
    assert forall |t2: TaskId, d: int|
      crate::composed::spec::wake_queues::reactor_wake_pending(s, t2) &&
      s.executor_log.len() as int <= d < s2.executor_log.len() &&
      el::is_drain_reactor_wake_at(s2.executor_log, d)
      implies el::task_id_in_drain_at(s2.executor_log, d, t2) by {
      reveal(crate::composed::spec::wake_queues::reactor_wake_pending);
      assert(t2 == tid);  // only tid has a task log ⟹ only tid can be pending
      assert(d == 13) by {
        if d == 8 {} else if d == 9 {} else if d == 10 {} else if d == 11 {}
        else if d == 12 {} else if d == 13 {} else if d == 14 {} else if d == 15 {}
      }
      assert(el::task_id_in_drain_at(s2.executor_log, 13, tid)) by {
        let ids = ee::get_drain_task_ids(s2.executor_log[13]);
        assert(ids =~= seq![tid]);
        assert(ids[0] == tid);
      }
    }
  }
  // taskwake_drain_step vacuous: biotask_pending has no Woken.
  assert forall |tid2: TID| #[trigger] s.task_logs.contains_key(tid2) implies
    (forall |j: int| 0 <= j < s.task_logs[tid2].len() ==> !ue::is_woken(s.task_logs[tid2][j])) by {
    assert(tid2 == tid && s.task_logs[tid2] == biotask_pending());
    assert forall |j: int| #![trigger biotask_pending()[j]] 0 <= j < biotask_pending().len() implies
      !ue::is_woken(biotask_pending()[j]) by { biotask_idx(); }
  }
  crate::composed::proof::assumption_satisfiable::no_taskwake_pending_no_woken(s);
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2));
}

// The io analog of b_domain_inhabited: a real IO-wait → io-ready → wake → Ready
// execution inhabits the goal's reachability domain non-vacuously.
pub proof fn bio_domain_inhabited(tid: TaskId)
  requires
    get_max_queue_length(bios1(tid)) >= 1,
  ensures
    crate::composed::proof::assumption_satisfiable::ete_reachable_N(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), bios2(tid), 2nat, 2nat, tid),
    crate::composed::spec::contract::end_to_end_response(bios2(tid), tid),
    !crate::composed::spec::contract::end_to_end_trigger(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), tid),
    !crate::composed::spec::contract::end_to_end_response(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), tid),
{
  let s0 = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s1 = bios1(tid);
  let s2 = bios2(tid);
  bexec2_idx(tid);
  assert(get_max_queue_length(s2) == get_max_queue_length(s1));
  assert(get_max_queue_length(s0) == get_max_queue_length(s1));
  crate::composed::proof::inhabitation_goal_wake::bs0_env(tid);
  bios1_env(tid); bios2_env(tid);
  bios1_composed_progress(tid); bios2_composed_progress(tid);
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
