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
use crate::composed::proof::inhabitation_goal_wake::{bexec1, bsched,
  bexec1_idx, bexec1_flags, bexec1_exec_progress, bexec1_queue, bexec1_queue_len,
  bpoll_count_bexec1, bexec_injected};
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
// DEFER witness: a task that self-defers (poll Pending after a Defer), then is
// redelivered by the executor Deferred queue and polled Ready. The wake is purely
// executor-side (Deferred queue) — the reactor does empty park cycles, so every
// reactor io/timer/wake family stays vacuous, and the task has NO reactor op.
// cap = 2. Anti-vacuity witness for the DEFER wake path.
// ============================================================================

// --- Reactor log: park cycles only, no registration (tick 1) ---
pub open spec fn dreac1() -> rl::Log {
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

pub open spec fn dreac2() -> rl::Log {
  dreac1() + seq![
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

pub proof fn dreac1_idx()
  ensures
    dreac1().len() == 4,
    rl::is_park_begin_at(dreac1(), 0),
    rl::is_get_current_time_at(dreac1(), 1),
    rl::is_park_end_at(dreac1(), 3),
{
}

pub proof fn dreac2_idx()
  ensures
    dreac2().len() == 8,
    forall |j: int| 0 <= j < 4 ==> dreac2()[j] == dreac1()[j],
    rl::is_park_begin_at(dreac2(), 4),
    rl::is_get_current_time_at(dreac2(), 5),
    rl::is_park_end_at(dreac2(), 7),
{
  dreac1_idx();
}

// per-index flags: only park/gct/pollevents fire; every register/wake/io family false.
pub proof fn dreac1_flags(j: int)
  ensures
    !rl::is_succ_register_timer_at(dreac1(), j),
    !rl::is_deregister_timer_at(dreac1(), j),
    !rl::io_syscall_registered_at(dreac1(), j),
    !rl::io_syscall_register_at(dreac1(), j),
    !rl::io_syscall_deregistered_at(dreac1(), j),
    !rl::is_succ_set_waker_at(dreac1(), j),
    !rl::is_set_waker_at(dreac1(), j),
    !rl::is_wake_task_at(dreac1(), j),
    !rl::is_io_event_ready_at(dreac1(), j),
    j != 0 ==> !rl::is_park_begin_at(dreac1(), j),
    j != 3 ==> !rl::is_park_end_at(dreac1(), j),
    j != 1 ==> !rl::is_get_current_time_at(dreac1(), j),
{
  dreac1_idx();
  if j == 0 {} else if j == 1 {} else if j == 2 {} else if j == 3 {} else {}
}

pub proof fn dreac2_flags(j: int)
  ensures
    !rl::is_succ_register_timer_at(dreac2(), j),
    !rl::is_deregister_timer_at(dreac2(), j),
    !rl::io_syscall_registered_at(dreac2(), j),
    !rl::io_syscall_register_at(dreac2(), j),
    !rl::io_syscall_deregistered_at(dreac2(), j),
    !rl::is_succ_set_waker_at(dreac2(), j),
    !rl::is_set_waker_at(dreac2(), j),
    !rl::is_wake_task_at(dreac2(), j),
    !rl::is_io_event_ready_at(dreac2(), j),
    (j != 0 && j != 4) ==> !rl::is_park_begin_at(dreac2(), j),
    (j != 3 && j != 7) ==> !rl::is_park_end_at(dreac2(), j),
    (j != 1 && j != 5) ==> !rl::is_get_current_time_at(dreac2(), j),
{
  dreac2_idx(); dreac1_idx();
  if 0 <= j < 4 { assert(dreac2()[j] == dreac1()[j]); dreac1_flags(j); }
  else if j == 4 {} else if j == 5 {} else if j == 6 {} else if j == 7 {} else {}
}

// reactor_inv: park_has_timestamp + park_poll_once fire at each park end; all other
// families are vacuous (no register/wake/io anywhere).
#[verifier::rlimit(50)]
proof fn dreac_vacuous_families(l: rl::Log)
  requires l == dreac1() || l == dreac2(),
  ensures
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::timer_deadline_future::timer_deadline_future(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::io_ready_in_park::io_ready_in_park(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::timer_waker_validity::timer_waker_validity(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::io_waker_validity::io_waker_validity(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::wake_has_registration::wake_has_registration(), l),
    crate::framework::action_safety::action_safety_satisfied(crate::reactor::invariants::set_waker_active_io::set_waker_active_io(), l),
{
  let is1 = l == dreac1();
  let p1 = crate::reactor::invariants::timer_deadline_future::timer_deadline_future();
  assert(crate::framework::action_safety::action_safety_satisfied(p1, l)) by {
    assert forall |i: int| #[trigger] (p1.acceptance)(l, i) implies (p1.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p2 = crate::reactor::invariants::io_ready_in_park::io_ready_in_park();
  assert(crate::framework::action_safety::action_safety_satisfied(p2, l)) by {
    assert forall |i: int| #[trigger] (p2.acceptance)(l, i) implies (p2.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p3 = crate::reactor::invariants::timer_waker_validity::timer_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p3, l)) by {
    assert forall |i: int| #[trigger] (p3.acceptance)(l, i) implies (p3.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p4 = crate::reactor::invariants::io_waker_validity::io_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p4, l)) by {
    assert forall |i: int| #[trigger] (p4.acceptance)(l, i) implies (p4.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p5 = crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p5, l)) by {
    assert forall |i: int| #[trigger] (p5.acceptance)(l, i) implies (p5.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p6 = crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p6, l)) by {
    assert forall |i: int| #[trigger] (p6.acceptance)(l, i) implies (p6.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p7 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer();
  assert(crate::framework::action_safety::action_safety_satisfied(p7, l)) by {
    assert forall |i: int| #[trigger] (p7.acceptance)(l, i) implies (p7.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p8 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p8, l)) by {
    assert forall |i: int| #[trigger] (p8.acceptance)(l, i) implies (p8.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p9 = crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p9, l)) by {
    assert forall |i: int| #[trigger] (p9.acceptance)(l, i) implies (p9.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p10 = crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p10, l)) by {
    assert forall |i: int| #[trigger] (p10.acceptance)(l, i) implies (p10.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p11 = crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p11, l)) by {
    assert forall |i: int| #[trigger] (p11.acceptance)(l, i) implies (p11.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p12 = crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p12, l)) by {
    assert forall |i: int| #[trigger] (p12.acceptance)(l, i) implies (p12.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p13 = crate::reactor::invariants::wake_has_registration::wake_has_registration();
  assert(crate::framework::action_safety::action_safety_satisfied(p13, l)) by {
    assert forall |i: int| #[trigger] (p13.acceptance)(l, i) implies (p13.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
  let p14 = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p14, l)) by {
    assert forall |i: int| #[trigger] (p14.acceptance)(l, i) implies (p14.validity)(l, i) by { if is1 { dreac1_flags(i); } else { dreac2_flags(i); } } }
}

pub proof fn dreac1_reac_inv()
  ensures crate::reactor::invariants::reactor_inv(dreac1()),
{
  let l = dreac1();
  dreac1_idx();
  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      dreac1_flags(i);
      if i == 3 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 3));
      }
    }
  }
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      dreac1_flags(i);
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
  dreac_vacuous_families(l);
  let q1 = crate::reactor::invariants::wake_on_expired::wake_on_expired();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q1, l)) by {
    assert forall |i: int| #[trigger] (q1.acceptance)(l, i) implies
      exists |j: int| #![trigger (q1.fulfillment)(l, i, j)] j > i && (q1.fulfillment)(l, i, j) && (q1.timely)(l, i, j) by { dreac1_flags(i); } }
  let q2 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_readable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q2, l)) by {
    assert forall |i: int| #[trigger] (q2.acceptance)(l, i) implies
      exists |j: int| #![trigger (q2.fulfillment)(l, i, j)] j > i && (q2.fulfillment)(l, i, j) && (q2.timely)(l, i, j) by { dreac1_flags(i); } }
  let q3 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_writable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q3, l)) by {
    assert forall |i: int| #[trigger] (q3.acceptance)(l, i) implies
      exists |j: int| #![trigger (q3.fulfillment)(l, i, j)] j > i && (q3.fulfillment)(l, i, j) && (q3.timely)(l, i, j) by { dreac1_flags(i); } }
}

pub proof fn dreac2_reac_inv()
  ensures crate::reactor::invariants::reactor_inv(dreac2()),
{
  let l = dreac2();
  dreac2_idx();
  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      dreac2_flags(i);
      if i == 3 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 3));
      } else if i == 7 {
        assert(rl::current_park_start(l, 5) == 4);
        assert(rl::current_park_start(l, 6) == 4);
        assert(rl::current_park_start(l, 7) == 4);
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 7));
      }
    }
  }
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      dreac2_flags(i);
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
  dreac_vacuous_families(l);
  let q1 = crate::reactor::invariants::wake_on_expired::wake_on_expired();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q1, l)) by {
    assert forall |i: int| #[trigger] (q1.acceptance)(l, i) implies
      exists |j: int| #![trigger (q1.fulfillment)(l, i, j)] j > i && (q1.fulfillment)(l, i, j) && (q1.timely)(l, i, j) by { dreac2_flags(i); } }
  let q2 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_readable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q2, l)) by {
    assert forall |i: int| #[trigger] (q2.acceptance)(l, i) implies
      exists |j: int| #![trigger (q2.fulfillment)(l, i, j)] j > i && (q2.fulfillment)(l, i, j) && (q2.timely)(l, i, j) by { dreac2_flags(i); } }
  let q3 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_writable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q3, l)) by {
    assert forall |i: int| #[trigger] (q3.acceptance)(l, i) implies
      exists |j: int| #![trigger (q3.fulfillment)(l, i, j)] j > i && (q3.fulfillment)(l, i, j) && (q3.timely)(l, i, j) by { dreac2_flags(i); } }
}

pub proof fn dreac1_reac_progress()
  ensures crate::reactor::reactor_progress(Seq::<re::ReactorEvent>::empty(), dreac1()),
{
  let l = dreac1();
  dreac1_idx();
  dreac1_reac_inv();
  assert(Seq::<re::ReactorEvent>::empty() =~= l.subrange(0, 0));
  assert(crate::reactor::is_complete_park_cycle(l, 0, 4)) by {
    assert(rl::is_park_begin_at(l, 0));
    assert(rl::is_park_end_at(l, 3));
    assert forall |k: int| 0 < k < 3 implies
      !#[trigger] rl::is_park_begin_at(l, k) && !rl::is_park_end_at(l, k) by { dreac1_flags(k); }
  }
  assert(exists |ps: int, pe: int|
    0 <= ps && ps < pe && pe <= l.len() &&
    crate::reactor::is_complete_park_cycle(l, ps, pe) &&
    (forall |i: int| 0 <= i < ps ==> re::is_inbound_non_park(#[trigger] l[i])) &&
    (forall |i: int| pe <= i < l.len() ==> re::is_inbound_non_park(#[trigger] l[i]))) by {
    assert(crate::reactor::is_complete_park_cycle(l, 0, 4));
  }
}

pub proof fn dreac2_reac_progress()
  ensures crate::reactor::reactor_progress(dreac1(), dreac2()),
{
  let l1 = dreac1();
  let l2 = dreac2();
  dreac2_idx(); dreac1_idx();
  dreac2_reac_inv();
  assert(l1 =~= l2.subrange(0, 4));
  assert(crate::reactor::is_complete_park_cycle(l2, 4, 8)) by {
    assert(rl::is_park_begin_at(l2, 4));
    assert(rl::is_park_end_at(l2, 7));
    assert forall |k: int| 4 < k < 7 implies
      !#[trigger] rl::is_park_begin_at(l2, k) && !rl::is_park_end_at(l2, k) by { dreac2_flags(k); }
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
// Executor log (defer): dexec1 = bexec1 (tick1 polls Pending). dexec2's tick2
// delivers tid via Drain{Deferred}[tid]@10 (instead of ReactorWake), matching the
// defer wake path; the ReactorWake drain@13 is empty.
// ============================================================================

pub open spec fn dexec2(tid: TID) -> el::Log {
  bexec1(tid) + seq![
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection { task: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: seq![tid],
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: Seq::<TID>::empty(),
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

pub proof fn dexec2_idx(tid: TID)
  ensures
    dexec2(tid).len() == 16,
    forall |k: int| 0 <= k < 8 ==> dexec2(tid)[k] == bexec1(tid)[k],
    dexec2(tid)[8] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    dexec2(tid)[10] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: seq![tid] }),
    dexec2(tid)[12] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    dexec2(tid)[13] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: Seq::<TID>::empty() }),
    dexec2(tid)[14] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PollTask {
      task_id: tid, task: None, result: crate::executor::spec::types::PollResult::Ready(()) }),
    dexec2(tid)[15] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
{
  bexec1_idx(tid);
}

pub proof fn dexec2_flags(tid: TID, k: int)
  ensures
    (k != 0 && k != 8) ==> !el::is_tick_begin_at(dexec2(tid), k),
    (k != 7 && k != 15) ==> !el::is_tick_end_at(dexec2(tid), k),
    (k != 4 && k != 12) ==> !el::is_park_at(dexec2(tid), k),
    (k != 1 && k != 9) ==> !el::is_pop_injection_at(dexec2(tid), k),
    (k != 6 && k != 14) ==> !el::is_poll_task_at(dexec2(tid), k),
{
  dexec2_idx(tid);
  if 0 <= k < 8 { bexec1_idx(tid); }
}

// Queue: Deferred[tid]@10 pushes tid; it stays through 11,12,13; poll@14 removes it.
pub proof fn dexec2_queue(tid: TID)
  ensures
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(dexec2(tid), 0) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(dexec2(tid), 6) =~= seq![tid],
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(dexec2(tid), 14) =~= seq![tid],
    forall |i: int| 2 <= i <= 6 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(dexec2(tid), i) =~= seq![tid],
    forall |i: int| 7 <= i <= 10 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(dexec2(tid), i) =~= Seq::<TID>::empty(),
    forall |i: int| 11 <= i <= 14 ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(dexec2(tid), i) =~= seq![tid],
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(dexec2(tid), 15) =~= Seq::<TID>::empty(),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(dexec2(tid), 16) =~= Seq::<TID>::empty(),
{
  let l = dexec2(tid);
  dexec2_idx(tid); bexec1_idx(tid);
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
  assert(fifo_queue_at(l, 11) =~= seq![tid]);
  assert(fifo_queue_at(l, 12) =~= seq![tid]);
  assert(fifo_queue_at(l, 13) =~= seq![tid]);
  assert(fifo_queue_at(l, 14) =~= seq![tid]);
  assert(fifo_queue_at(l, 15) =~= Seq::<TID>::empty());
  assert(fifo_queue_at(l, 16) =~= Seq::<TID>::empty());
  assert forall |i: int| 2 <= i <= 6 implies #[trigger] fifo_queue_at(l, i) =~= seq![tid] by {
    if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {}
  }
  assert forall |i: int| 7 <= i <= 10 implies #[trigger] fifo_queue_at(l, i) =~= Seq::<TID>::empty() by {
    if i == 7 {} else if i == 8 {} else if i == 9 {} else if i == 10 {}
  }
  assert forall |i: int| 11 <= i <= 14 implies #[trigger] fifo_queue_at(l, i) =~= seq![tid] by {
    if i == 11 {} else if i == 12 {} else if i == 13 {} else if i == 14 {}
  }
}

pub proof fn dexec2_queue_len(tid: TID)
  ensures
    forall |i: int| 0 <= i <= dexec2(tid).len() ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(dexec2(tid), i).len() <= 1,
    forall |i: int| 0 <= i <= dexec2(tid).len() ==>
      #[trigger] el::fifo_queue_at_for_persistent(dexec2(tid), i).len() <= 1,
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  dexec2_idx(tid);
  let l = dexec2(tid);
  dexec2_queue(tid);
  assert forall |i: int| 0 <= i <= l.len() implies #[trigger] fifo_queue_at(l, i).len() <= 1 by {
    dexec2_queue(tid);
    if 2 <= i <= 6 { } else if 7 <= i <= 10 { } else if 11 <= i <= 14 { }
    else if i == 15 || i == 16 { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
  }
  assert forall |i: int| 0 <= i <= l.len() implies #[trigger] el::fifo_queue_at_for_persistent(l, i).len() <= 1 by {
    dexec2_queue(tid);
    if 2 <= i <= 6 { } else if 7 <= i <= 10 { } else if 11 <= i <= 14 { }
    else if i == 15 || i == 16 { assert(fifo_queue_at(l, i) =~= Seq::<TID>::empty()); }
  }
}

proof fn dexec2_tick_structure(tid: TID)
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_park::tick_has_park(), dexec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection(), dexec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred(), dexec2(tid)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake(), dexec2(tid)),
{
  let l = dexec2(tid);
  dexec2_idx(tid);
  let pk = crate::executor::invariants::tick_has_park::tick_has_park();
  assert(crate::framework::action_safety::action_safety_satisfied(pk, l)) by {
    assert forall |i: int| #[trigger] (pk.acceptance)(l, i) implies (pk.validity)(l, i) by {
      dexec2_flags(tid, i);
      if i == 7 { assert(el::is_park_at(l, 4)); assert forall |k: int| 4 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { dexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_park_at(l, 12)); assert forall |k: int| 12 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { dexec2_flags(tid, k); } }
    } }
  let pp = crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection();
  assert(crate::framework::action_safety::action_safety_satisfied(pp, l)) by {
    assert forall |i: int| #[trigger] (pp.acceptance)(l, i) implies (pp.validity)(l, i) by {
      dexec2_flags(tid, i);
      if i == 7 { assert(el::is_pop_injection_at(l, 1)); assert forall |k: int| 1 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { dexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_pop_injection_at(l, 9)); assert forall |k: int| 9 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { dexec2_flags(tid, k); } }
    } }
  let dd = crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred();
  assert(crate::framework::action_safety::action_safety_satisfied(dd, l)) by {
    assert forall |i: int| #[trigger] (dd.acceptance)(l, i) implies (dd.validity)(l, i) by {
      dexec2_flags(tid, i);
      if i == 7 { assert(el::is_drain_deferred_at(l, 2)); assert forall |k: int| 2 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { dexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_drain_deferred_at(l, 10)); assert forall |k: int| 10 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { dexec2_flags(tid, k); } }
    } }
  let dt = crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake();
  assert(crate::framework::action_safety::action_safety_satisfied(dt, l)) by {
    assert forall |i: int| #[trigger] (dt.acceptance)(l, i) implies (dt.validity)(l, i) by {
      dexec2_flags(tid, i);
      if i == 7 { assert(el::is_drain_task_wake_at(l, 3)); assert forall |k: int| 3 < k < 7 implies !#[trigger] el::is_tick_begin_at(l, k) by { dexec2_flags(tid, k); } }
      else if i == 15 { assert(el::is_drain_task_wake_at(l, 11)); assert forall |k: int| 11 < k < 15 implies !#[trigger] el::is_tick_begin_at(l, k) by { dexec2_flags(tid, k); } }
    } }
}

pub proof fn dexec2_exec_inv(tid: TID)
  ensures
    crate::executor::invariants::executor_inv(dexec2(tid)),
{
  let l = dexec2(tid);
  dexec2_idx(tid);
  dexec2_queue(tid);
  let p_fifo = crate::executor::invariants::fifo_task_selection::fifo_task_selection();
  assert(crate::framework::action_safety::action_safety_satisfied(p_fifo, l)) by {
    assert forall |i: int| #[trigger] (p_fifo.acceptance)(l, i) implies (p_fifo.validity)(l, i) by {
      dexec2_flags(tid, i);
      if i == 6 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 6, tid)); }
      else if i == 14 { assert(crate::executor::invariants::fifo_task_selection::is_fifo_head_at(l, 14, tid)); }
    }
  }
  let p_vtp = crate::executor::invariants::valid_task_polling::valid_task_polling();
  assert(crate::framework::action_safety::action_safety_satisfied(p_vtp, l)) by {
    assert forall |i: int| #[trigger] (p_vtp.acceptance)(l, i) implies (p_vtp.validity)(l, i) by {
      dexec2_flags(tid, i);
      if i == 6 || i == 14 {
        assert(el::is_pop_injection_at(l, 1) && ee::get_pop_injection_task(l[1]).unwrap().id == tid);
        assert(crate::executor::invariants::valid_task_polling::tid_was_injected_before(l, i, tid));
        assert(!crate::executor::invariants::valid_task_polling::tid_returned_ready_before(l, i, tid)) by {
          assert forall |j: int| 0 <= j < i implies
            !(el::is_poll_task_at(l, j) && ee::get_poll_task_id(l[j]) == tid
              && ee::get_poll_result(l[j]) == crate::executor::spec::types::PollResult::Ready(())) by { dexec2_flags(tid, j); }
        }
        assert(!crate::executor::invariants::valid_task_polling::tid_is_invalid(l, i, tid));
      }
    }
  }
  dexec2_tick_structure(tid);
  let p_pdrw = crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_pdrw, l)) by {
    assert forall |i: int| #[trigger] (p_pdrw.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_pdrw.fulfillment)(l, i, j)]
        j > i && (p_pdrw.fulfillment)(l, i, j) && (p_pdrw.timely)(l, i, j) by {
      dexec2_flags(tid, i);
      if i == 4 {
        assert(el::is_drain_reactor_wake_at(l, 5));
        assert forall |k: int| 4 < k < 5 implies !#[trigger] el::is_tick_end_at(l, k) by { dexec2_flags(tid, k); }
        assert(5 > 4 && (p_pdrw.fulfillment)(l, 4, 5) && (p_pdrw.timely)(l, 4, 5));
      } else if i == 12 {
        assert(el::is_drain_reactor_wake_at(l, 13));
        assert forall |k: int| 12 < k < 13 implies !#[trigger] el::is_tick_end_at(l, k) by { dexec2_flags(tid, k); }
        assert(13 > 12 && (p_pdrw.fulfillment)(l, 12, 13) && (p_pdrw.timely)(l, 12, 13));
      }
    }
  }
  let p_tpr = crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_tpr, l)) by {
    assert forall |i: int| #[trigger] (p_tpr.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_tpr.fulfillment)(l, i, j)]
        j > i && (p_tpr.fulfillment)(l, i, j) && (p_tpr.timely)(l, i, j) by {
      dexec2_flags(tid, i);
      if i == 0 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 0) =~= Seq::<TID>::empty());
      } else if i == 8 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 8) =~= Seq::<TID>::empty());
      }
    }
  }
}

pub proof fn dexec2_exec_progress(tid: TID)
  ensures
    crate::executor::executor_progress(bexec1(tid), dexec2(tid)),
{
  let l1 = bexec1(tid);
  let l2 = dexec2(tid);
  dexec2_idx(tid);
  dexec2_exec_inv(tid);
  assert(l1 =~= l2.subrange(0, 8));
  assert(crate::executor::is_complete_tick_cycle(l2, 8, 16)) by {
    assert(el::is_tick_begin_at(l2, 8));
    assert(el::is_tick_end_at(l2, 15));
    assert forall |k: int| 8 < k < 15 implies
      !#[trigger] el::is_tick_begin_at(l2, k) && !el::is_tick_end_at(l2, k) by { dexec2_flags(tid, k); }
  }
}

// ============================================================================
// Task log (defer): Poll(begin), Defer, Poll(Pending), [Poll(begin), Poll(Ready)].
// The Defer op is NOT a reactor operation, so the task has ZERO reactor ops and
// alignment is entirely vacuous.
// ============================================================================

pub open spec fn dtask_pending() -> ul::Log {
  seq![
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    ue::UtilityEvent::Outbound(ue::OutboundCall::Defer),
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: Some(ue::PollResult::Pending) }),
  ]
}

pub open spec fn dtask_ready() -> ul::Log {
  dtask_pending() + seq![
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: None }),
    ue::UtilityEvent::Inbound(ue::InboundCall::Poll { result: Some(ue::PollResult::Ready) }),
  ]
}

pub proof fn dtask_idx()
  ensures
    dtask_pending().len() == 3,
    dtask_ready().len() == 5,
    forall |i: int| 0 <= i < 3 ==> dtask_ready()[i] == dtask_pending()[i],
    ue::is_poll_begin(dtask_pending()[0]),
    ue::is_defer(dtask_pending()[1]),
    ue::is_poll_end_pending(dtask_pending()[2]),
    ue::is_poll_begin(dtask_ready()[3]),
    ue::is_poll_end(dtask_ready()[4]),
    !ue::is_poll_end_pending(dtask_ready()[4]),
    forall |i: int| #![trigger dtask_ready()[i]] 0 <= i < dtask_ready().len() ==>
      !crate::composed::spec::alignment::is_reactor_operation(dtask_ready()[i]),
    forall |i: int| #![trigger dtask_pending()[i]] 0 <= i < dtask_pending().len() ==>
      !crate::composed::spec::alignment::is_reactor_operation(dtask_pending()[i]),
{
  assert forall |i: int| #![trigger dtask_ready()[i]] 0 <= i < dtask_ready().len() implies
    !crate::composed::spec::alignment::is_reactor_operation(dtask_ready()[i]) by {
    if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {}
  }
  assert forall |i: int| #![trigger dtask_pending()[i]] 0 <= i < dtask_pending().len() implies
    !crate::composed::spec::alignment::is_reactor_operation(dtask_pending()[i]) by {
    if i == 0 {} else if i == 1 {} else if i == 2 {}
  }
}

pub proof fn dtask_utilities_inv()
  ensures
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(dtask_pending()),
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(dtask_ready()),
{
  dtask_idx();
  use crate::utilities::invariants::wakeup_guarantee::*;
  let wg = wakeup_guarantee();
  let ro = crate::utilities::invariants::resource_ownership::resource_ownership();
  // wakeup_guarantee @2 (PollEnd Pending): has_defer_in_current_poll (Defer@1).
  assert(crate::framework::action_safety::action_safety_satisfied(wg, dtask_pending())) by {
    assert forall |i: int| #[trigger] (wg.acceptance)(dtask_pending(), i) implies (wg.validity)(dtask_pending(), i) by {
      if i == 2 {
        assert(crate::utilities::spec::log::current_poll_start(dtask_pending(), 2) == 0) by {
          assert(ue::is_poll_begin(dtask_pending()[0]));
          assert(crate::utilities::spec::log::find_last_poll_begin(dtask_pending(), 0) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(dtask_pending(), 1) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(dtask_pending(), 2) == 0);
        }
        assert(crate::utilities::spec::log::has_defer_in_current_poll(dtask_pending(), 2)) by {
          assert(crate::utilities::spec::log::in_current_poll_cycle(dtask_pending(), 1, 2));
          assert(ue::is_defer(dtask_pending()[1]));
        }
        assert(crate::utilities::spec::log::has_active_wakeup_source(dtask_pending(), 2));
      }
    }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(ro, dtask_pending())) by {
    assert forall |i: int| #[trigger] (ro.acceptance)(dtask_pending(), i) implies (ro.validity)(dtask_pending(), i) by { }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(wg, dtask_ready())) by {
    assert forall |i: int| #[trigger] (wg.acceptance)(dtask_ready(), i) implies (wg.validity)(dtask_ready(), i) by {
      if i == 2 {
        assert(crate::utilities::spec::log::current_poll_start(dtask_ready(), 2) == 0) by {
          assert(ue::is_poll_begin(dtask_ready()[0]));
          assert(crate::utilities::spec::log::find_last_poll_begin(dtask_ready(), 0) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(dtask_ready(), 1) == 0);
          assert(crate::utilities::spec::log::find_last_poll_begin(dtask_ready(), 2) == 0);
        }
        assert(crate::utilities::spec::log::has_defer_in_current_poll(dtask_ready(), 2)) by {
          assert(crate::utilities::spec::log::in_current_poll_cycle(dtask_ready(), 1, 2));
          assert(ue::is_defer(dtask_ready()[1]));
        }
        assert(crate::utilities::spec::log::has_active_wakeup_source(dtask_ready(), 2));
      }
    }
  }
  assert(crate::framework::action_safety::action_safety_satisfied(ro, dtask_ready())) by {
    assert forall |i: int| #[trigger] (ro.acceptance)(dtask_ready(), i) implies (ro.validity)(dtask_ready(), i) by { }
  }
}

pub open spec fn ds1(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: bexec1(tid),
    reactor_log: dreac1(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, dtask_pending()),
    injection_schedule: bsched(tid),
  }
}

pub open spec fn ds2(tid: TID) -> ComposedState {
  ComposedState {
    executor_log: dexec2(tid),
    reactor_log: dreac2(),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, dtask_ready()),
    injection_schedule: bsched(tid),
  }
}

// action_mediation_state: ZERO reactor ops in the task log and NO task-initiated
// reactor events (dreac is park-only) ⟹ every mediation clause is vacuous.
#[verifier::rlimit(50)]
proof fn ds_am_state(s: ComposedState, tid: TID)
  requires
    s.task_logs.contains_key(tid),
    (s.reactor_log == dreac1() && s.task_logs[tid] == dtask_pending()) ||
    (s.reactor_log == dreac2() && s.task_logs[tid] == dtask_ready()),
    forall |t2: TaskId| s.task_logs.contains_key(t2) ==> t2 == tid,
  ensures
    crate::composed::spec::alignment::action_mediation_state(s),
{
  dreac1_idx(); dreac2_idx(); dtask_idx();
  use crate::composed::spec::alignment::*;
  let is1 = s.reactor_log == dreac1();
  assert(operation_to_reactor_exists(s)) by {
    assert forall |t2: TaskId, i: int|
      s.task_logs.contains_key(t2) && 0 <= i < s.task_logs[t2].len() &&
      is_reactor_operation(#[trigger] s.task_logs[t2][i])
      implies exists |j: int| 0 <= j < s.reactor_log.len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][i]) by {
      assert(t2 == tid);  // no reactor op in dtask
    }
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
      implies t1 == t2 && ti1 == ti2 by {
      assert(t1 == tid);  // no reactor op
    }
  }
  // monotonic: no two reactor ops (there are none).
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

// ============================================================================
// obs consistency + park alignment
// ============================================================================

proof fn ds1_obs_consistency(tid: TID)
  ensures
    crate::composed::spec::alignment::observation_consistency_state(ds1(tid)),
    crate::composed::spec::alignment::observation_consistency_step(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ds1(tid)),
{
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = ds1(tid);
  bexec1_idx(tid); dtask_idx();
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
        assert(ue::is_poll_end_pending(dtask_pending()[2]));
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
        assert(ue::is_poll_end_pending(dtask_pending()[2]));
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

proof fn ds2_obs_consistency(tid: TID)
  ensures
    crate::composed::spec::alignment::observation_consistency_state(ds2(tid)),
    crate::composed::spec::alignment::observation_consistency_step(ds1(tid), ds2(tid)),
{
  let s = ds1(tid);
  let s2 = ds2(tid);
  dexec2_idx(tid); bexec1_idx(tid); dtask_idx();
  use crate::composed::spec::alignment::*;
  assert(observation_consistency_state(s2)) by {
    assert(polled_task_has_log_inv(s2)) by {
      assert forall |t2: TaskId| el::has_poll_for_id(s2.executor_log, t2) implies s2.task_logs.contains_key(t2) by {
        if !s2.task_logs.contains_key(t2) {
          assert forall |i: int| #![trigger s2.executor_log[i]] 0 <= i < s2.executor_log.len()
            implies !el::is_poll_task_for_id_at(s2.executor_log, i, t2) by { dexec2_flags(tid, i); }
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
        implies task_log_ends_with_pending(s2.task_logs[t2]) by { dexec2_flags(tid, i); }
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
        assert(s.task_logs[tid] == dtask_pending() && s2.task_logs[tid] == dtask_ready());
      }
    }
  }
}

proof fn ds1_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ds1(tid)),
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

proof fn ds2_park_alignment(tid: TID)
  ensures
    crate::composed::spec::alignment::park_alignment(ds1(tid), ds2(tid)),
{
  dexec2_idx(tid); dreac2_idx();
  use crate::composed::spec::alignment::*;
  let e = dexec2(tid);
  assert(count_park_events_in(e, 16, 16) == 0);
  assert(count_park_events_in(e, 15, 16) == 0) by { dexec2_flags(tid, 15); }
  assert(count_park_events_in(e, 14, 16) == 0) by { dexec2_flags(tid, 14); }
  assert(count_park_events_in(e, 13, 16) == 0) by { dexec2_flags(tid, 13); }
  assert(count_park_events_in(e, 12, 16) == 1) by { dexec2_flags(tid, 12); }
  assert(count_park_events_in(e, 11, 16) == 1) by { dexec2_flags(tid, 11); }
  assert(count_park_events_in(e, 10, 16) == 1) by { dexec2_flags(tid, 10); }
  assert(count_park_events_in(e, 9, 16) == 1) by { dexec2_flags(tid, 9); }
  assert(count_park_events_in(e, 8, 16) == 1) by { dexec2_flags(tid, 8); }
  let r = dreac2();
  assert(count_park_cycles_in(r, 8, 8) == 0);
  assert(count_park_cycles_in(r, 7, 8) == 1) by { dreac2_flags(7); }
  assert(count_park_cycles_in(r, 6, 8) == 1) by { dreac2_flags(6); }
  assert(count_park_cycles_in(r, 5, 8) == 1) by { dreac2_flags(5); }
  assert(count_park_cycles_in(r, 4, 8) == 1) by { dreac2_flags(4); }
}

pub proof fn ds1_cross(tid: TID)
  ensures
    cross_module_alignment(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ds1(tid)),
{
  reveal(cross_module_alignment);
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = ds1(tid);
  bexec1_idx(tid); dreac1_idx(); dtask_idx();
  use crate::composed::spec::alignment::*;
  ds_am_state(s2, tid);
  // No new reactor ops (dtask has none) and no new task-initiated reactor events.
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
  ds1_obs_consistency(tid);
  ds1_park_alignment(tid);
}

pub proof fn ds2_cross(tid: TID)
  ensures
    cross_module_alignment(ds1(tid), ds2(tid)),
{
  reveal(cross_module_alignment);
  let s = ds1(tid);
  let s2 = ds2(tid);
  dexec2_idx(tid); dreac2_idx(); dtask_idx();
  use crate::composed::spec::alignment::*;
  ds_am_state(s2, tid);
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
  ds2_obs_consistency(tid);
  ds2_park_alignment(tid);
}

// ============================================================================
// env facts (all io/timer assumptions vacuous — no register/setwaker anywhere)
// ============================================================================
// Reactor-side env facts for a park-only (dreac) reactor: all io/timer assumptions
// vacuous. Depends only on s.reactor_log, so it is reused by the taskwake witness.
#[verifier::rlimit(100)]
pub proof fn d_reac_env_facts(s: ComposedState, tid: TID)
  requires
    s.reactor_log == dreac1() || s.reactor_log == dreac2(),
  ensures
    crate::composed::spec::assumptions::timestamps_strictly_increasing(s.reactor_log),
    crate::reactor::timestamps_positive(s.reactor_log),
    timer_deadline_gap_bounded(s, tid),
    timer_resources_remain_active(s),
    crate::composed::proof::assumption_satisfiable::contract_io_assumption_here(s),
    // bound-generic (no SetWaker ⟹ vacuous for every n, in particular the
    // uninterpreted get_io_ready_bound used by env_N)
    forall |rid: ResourceIdView, n: nat|
      #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
      io_ready_forward_here(s.reactor_log, rid, n),
{
  dreac1_idx(); dreac2_idx();
  let l = s.reactor_log;
  let is1 = l == dreac1();
  use crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid;
  assert(crate::composed::spec::assumptions::timestamps_strictly_increasing(l)) by {
    assert forall |a: int, b: int| 0 <= a < b < l.len() &&
      rl::is_get_current_time_at(l, a) && rl::is_get_current_time_at(l, b)
      implies re::get_current_timestamp(l[a]) < re::get_current_timestamp(l[b]) by {
      if is1 { dreac1_flags(a); dreac1_flags(b); } else { dreac2_flags(a); dreac2_flags(b); }
    }
  }
  assert(crate::reactor::timestamps_positive(l)) by {
    assert forall |a: int| 0 <= a < l.len() && rl::is_get_current_time_at(l, a)
      implies re::get_current_timestamp(l[a]) >= 1 by {
      if is1 { dreac1_flags(a); } else { dreac2_flags(a); }
    }
  }
  assert(timer_deadline_gap_bounded(s, tid)) by {
    reveal(timer_deadline_gap_bounded);
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < l.len() && rl::is_succ_register_timer_at(l, reg_idx) implies false by {
      if is1 { dreac1_flags(reg_idx); } else { dreac2_flags(reg_idx); }
    }
  }
  assert(timer_resources_remain_active(s)) by {
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < l.len() && rl::is_succ_register_timer_at(l, reg_idx) implies false by {
      if is1 { dreac1_flags(reg_idx); } else { dreac2_flags(reg_idx); }
    }
  }
  assert(crate::composed::proof::assumption_satisfiable::contract_io_assumption_here(s)) by {
    assert forall |rid: ResourceIdView|
      #![trigger crate::composed::proof::assumption_satisfiable::io_assumption_here(s.reactor_log, rid)]
      crate::composed::proof::assumption_satisfiable::io_assumption_here(s.reactor_log, rid) by {
      assert(crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(l, rid)) by {
        assert forall |j: int| 0 <= j < l.len() implies !rl::io_syscall_deregistered_at(l, j) by {
          if is1 { dreac1_flags(j); } else { dreac2_flags(j); }
        }
      }
    }
  }
  // io_ready_forward: no setwaker anywhere ⟹ find_last == -1 ⟹ vacuous (any n).
  assert forall |rid: ResourceIdView, n: nat|
    #![trigger io_ready_forward_here(s.reactor_log, rid, n)]
    io_ready_forward_here(s.reactor_log, rid, n) by {
    assert(find_last_set_waker_for_rid(l, rid, 0) == -1);
    assert(find_last_set_waker_for_rid(l, rid, 1) == -1) by { if is1 { dreac1_flags(0); } else { dreac2_flags(0); } }
    assert(find_last_set_waker_for_rid(l, rid, 2) == -1) by { if is1 { dreac1_flags(1); } else { dreac2_flags(1); } }
    assert(find_last_set_waker_for_rid(l, rid, 3) == -1) by { if is1 { dreac1_flags(2); } else { dreac2_flags(2); } }
    assert(find_last_set_waker_for_rid(l, rid, 4) == -1) by { if is1 { dreac1_flags(3); } else { dreac2_flags(3); } }
    if !is1 {
      assert(find_last_set_waker_for_rid(l, rid, 5) == -1) by { dreac2_flags(4); }
      assert(find_last_set_waker_for_rid(l, rid, 6) == -1) by { dreac2_flags(5); }
      assert(find_last_set_waker_for_rid(l, rid, 7) == -1) by { dreac2_flags(6); }
      assert(find_last_set_waker_for_rid(l, rid, 8) == -1) by { dreac2_flags(7); }
    }
  }
}

proof fn d_common_env_facts(s: ComposedState, tid: TID)
  requires
    (s.reactor_log == dreac1() && s.executor_log == bexec1(tid) &&
     s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, dtask_pending()) &&
     s.injection_schedule == bsched(tid)) ||
    (s.reactor_log == dreac2() && s.executor_log == dexec2(tid) &&
     s.task_logs == Map::<TaskId, ul::Log>::empty().insert(tid, dtask_ready()) &&
     s.injection_schedule == bsched(tid)),
    get_max_queue_length(s) >= 1,
  ensures
    el::tid_unique(s.executor_log, tid),
    queue_length_bounded(s),
{
  let is1 = s.executor_log == bexec1(tid);
  bexec1_idx(tid); dexec2_idx(tid); dtask_idx();
  let l = s.executor_log;
  // both bexec1 and dexec2 share tick1 [0,8); pops of tid only at index 1.
  assert(el::tid_unique(l, tid)) by {
    assert forall |a: int, b: int| 0 <= a < b < l.len() &&
      el::is_pop_injection_at(l, a) && ee::get_pop_injection_task(l[a]) == Some(crate::executor::spec::types::TaskView { id: tid }) &&
      el::is_pop_injection_at(l, b) && ee::get_pop_injection_task(l[b]) == Some(crate::executor::spec::types::TaskView { id: tid })
      implies false by {
      if is1 { bexec1_flags(tid, a); bexec1_flags(tid, b); } else { dexec2_flags(tid, a); dexec2_flags(tid, b); }
    }
  }
  if is1 { bexec1_queue_len(tid); } else { dexec2_queue_len(tid); }
  assert(queue_length_bounded(s)) by {
    assert forall |i: int|
      #![trigger crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i)]
      0 <= i <= l.len() implies
      crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i).len() <= get_max_queue_length(s) by {
      if is1 { bexec1_queue_len(tid); } else { dexec2_queue_len(tid); }
    }
  }
}

// injected_tasks(dexec2) == [tid] (pops: Some(tid)@1, None@9).
pub proof fn dexec2_pops(tid: TID)
  ensures
    crate::executor::spec::injection_schedule::pops_deliver_schedule(dexec2(tid), bsched(tid)),
{
  use crate::executor::spec::injection_schedule::*;
  dexec2_idx(tid); bexec1_idx(tid); bexec_injected(tid);
  let l = dexec2(tid);
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

proof fn ds1_env(tid: TID)
  requires get_max_queue_length(ds1(tid)) >= 1,
  ensures env_N(ds1(tid), tid, 2nat),
{
  let s = ds1(tid);
  bexec1_idx(tid); dreac1_idx(); dtask_idx();
  d_reac_env_facts(s, tid);
  d_common_env_facts(s, tid);
  assert(bounded_poll_count_here_with_bound(s, tid, 2nat)) by { bpoll_count_bexec1(tid); }
  assert(env_holds_at_state_core(s, tid));
  assert(end_to_end_env(s, tid));
  assert(!crate::utilities::spec::log::has_pass_waker_in_current_poll(
    s.task_logs[tid], (s.task_logs[tid].len() - 1) as int)) by {
    let tl = s.task_logs[tid];
    assert(tl == dtask_pending());
    assert forall |j: int| #![trigger tl[j]] 0 <= j < tl.len() implies !ue::is_pass_waker(tl[j]) by {}
  }
  crate::composed::proof::assumption_satisfiable::taskwake_arrival_within_vacuous(s, tid, 2nat);
}

proof fn ds2_env(tid: TID)
  requires get_max_queue_length(ds2(tid)) >= 1,
  ensures env_N(ds2(tid), tid, 2nat),
{
  let s = ds2(tid);
  dexec2_idx(tid); dreac2_idx(); dtask_idx();
  d_reac_env_facts(s, tid);
  d_common_env_facts(s, tid);
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

pub proof fn ds1_composed_progress(tid: TID)
  ensures
    composed_progress(crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ds1(tid)),
{
  reveal(composed_progress);
  let s = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s2 = ds1(tid);
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 0)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 0)); }
  assert(is_extension_of(s, s2));
  bexec1_exec_progress(tid);
  dreac1_reac_progress();
  ds1_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    dtask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(t2 == tid && s2.task_logs[t2] == dtask_pending());
    }
  }
  crate::composed::spec::alignment::monotonic_alignment_holds_no_two_ops(s2);
  ds_am_state(s2, tid);
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
      // arrival_witness has empty task_logs ⟹ in_deferred_queue false ⟹ vacuous.
      assert(!s.task_logs.contains_key(t2));
    }
  }
}

pub proof fn ds2_composed_progress(tid: TID)
  ensures
    composed_progress(ds1(tid), ds2(tid)),
{
  reveal(composed_progress);
  let s = ds1(tid);
  let s2 = ds2(tid);
  dexec2_idx(tid); dreac2_idx(); dtask_idx(); bexec1_idx(tid);
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by { assert(s.executor_log =~= s2.executor_log.subrange(0, 8)); }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by { assert(s.reactor_log =~= s2.reactor_log.subrange(0, 4)); }
  assert(is_extension_of(s, s2)) by {
    assert(s.task_logs[tid] == dtask_pending() && s2.task_logs[tid] == dtask_ready());
    assert(crate::composed::spec::state::is_task_log_prefix(dtask_pending(), dtask_ready()));
  }
  dexec2_exec_progress(tid);
  dreac2_reac_progress();
  ds2_cross(tid);
  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s2)) by {
    dtask_utilities_inv();
    assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
      crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
      assert(t2 == tid && s2.task_logs[t2] == dtask_ready());
    }
  }
  crate::composed::spec::alignment::monotonic_alignment_holds_no_two_ops(s2);
  ds_am_state(s2, tid);
  dexec2_pops(tid);
  // reactor_wake vacuous (dreac1 no waketask), taskwake vacuous (dtask_pending no woken).
  crate::composed::proof::assumption_satisfiable::no_reactor_wake_pending_no_waketask(s);
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2));
  crate::composed::proof::assumption_satisfiable::no_taskwake_pending_no_woken(s);
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2));
  // deferred_drain_step NON-VACUOUS: tid is in the deferred queue at ds1 (pending +
  // Defer), and the step's Drain{Deferred}@10 carries [tid].
  assert(crate::composed::spec::wake_queues::in_deferred_queue(s, tid)) by {
    assert(el::last_poll_is_pending(s.executor_log, tid)) by {
      crate::composed::proof::end_to_end::last_poll_idx_properties(s.executor_log, tid);
      assert(el::is_poll_task_for_id_at(s.executor_log, 6, tid));
      assert(el::is_poll_pending_for_id_at(s.executor_log, 6, tid));
    }
    assert(crate::utilities::spec::log::has_defer_in_current_poll(
      s.task_logs[tid], (s.task_logs[tid].len() - 1) as int)) by {
      assert(s.task_logs[tid] == dtask_pending());
      assert(crate::utilities::spec::log::current_poll_start(dtask_pending(), 2) == 0) by {
        assert(crate::utilities::spec::log::find_last_poll_begin(dtask_pending(), 0) == 0);
        assert(crate::utilities::spec::log::find_last_poll_begin(dtask_pending(), 1) == 0);
        assert(crate::utilities::spec::log::find_last_poll_begin(dtask_pending(), 2) == 0);
      }
      assert(crate::utilities::spec::log::in_current_poll_cycle(dtask_pending(), 1, 2));
      assert(ue::is_defer(dtask_pending()[1]));
    }
    assert(!crate::composed::spec::wake_queues::deferred_drained_after(
      s.executor_log, tid, el::last_poll_idx_for_id(s.executor_log, tid))) by {
      crate::composed::proof::end_to_end::last_poll_idx_properties(s.executor_log, tid);
      assert(el::last_poll_idx_for_id(s.executor_log, tid) == 6);
      assert forall |d: int| 6 < d < s.executor_log.len() implies
        !(el::is_drain_deferred_at(s.executor_log, d) && el::task_id_in_drain_at(s.executor_log, d, tid)) by {
        bexec1_flags(tid, d);
      }
    }
  }
  reveal(crate::composed::spec::wake_queues::deferred_drain_step);
  assert(crate::composed::spec::wake_queues::deferred_drain_step(s, s2)) by {
    assert forall |t2: TaskId, d: int|
      crate::composed::spec::wake_queues::in_deferred_queue(s, t2) &&
      s.executor_log.len() as int <= d < s2.executor_log.len() &&
      el::is_drain_deferred_at(s2.executor_log, d)
      implies el::task_id_in_drain_at(s2.executor_log, d, t2) by {
      assert(t2 == tid);  // only tid has a task log ⟹ only tid can be in the deferred queue
      // the only Drain{Deferred} in [8,16) is @10, carrying [tid].
      dexec2_flags(tid, d);
      assert(d == 10);
      assert(el::task_id_in_drain_at(s2.executor_log, 10, tid)) by {
        let ids = ee::get_drain_task_ids(s2.executor_log[10]);
        assert(ids =~= seq![tid]);
        assert(ids[0] == tid);
      }
    }
  }
}

pub proof fn d_domain_inhabited(tid: TaskId)
  requires
    get_max_queue_length(ds1(tid)) >= 1,
  ensures
    crate::composed::proof::assumption_satisfiable::ete_reachable_N(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), ds2(tid), 2nat, 2nat, tid),
    crate::composed::spec::contract::end_to_end_response(ds2(tid), tid),
    !crate::composed::spec::contract::end_to_end_trigger(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), tid),
    !crate::composed::spec::contract::end_to_end_response(
      crate::composed::proof::assumption_satisfiable::arrival_witness(tid), tid),
{
  let s0 = crate::composed::proof::assumption_satisfiable::arrival_witness(tid);
  let s1 = ds1(tid);
  let s2 = ds2(tid);
  dexec2_idx(tid);
  assert(get_max_queue_length(s2) == get_max_queue_length(s1));
  assert(get_max_queue_length(s0) == get_max_queue_length(s1));
  crate::composed::proof::inhabitation_goal_wake::bs0_env(tid);
  ds1_env(tid); ds2_env(tid);
  ds1_composed_progress(tid); ds2_composed_progress(tid);
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
