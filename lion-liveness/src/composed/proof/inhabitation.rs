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
use crate::reactor::spec::types::IoResultView;

verus! {

// ============================================================================
// The witness sequences and state
// ============================================================================

pub open spec fn wexec() -> el::Log {
  seq![
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection { task: None }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred,
      task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake,
      task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake,
      task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
  ]
}

pub open spec fn wreac() -> rl::Log {
  seq![
    re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 0int }),
    re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None,
      result: IoResultView::Ok(0nat),
    }),
    re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None,
      result: Some(IoResultView::Ok(())),
    }),
  ]
}

pub open spec fn wstate() -> ComposedState {
  ComposedState {
    executor_log: wexec(),
    reactor_log: wreac(),
    task_logs: Map::empty(),
    injection_schedule: Seq::empty(),
  }
}

// ============================================================================
// Content helpers
// ============================================================================

proof fn wexec_idx()
  ensures
    wexec().len() == 7,
    wexec()[0] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    wexec()[1] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection { task: None }),
    wexec()[2] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty() }),
    wexec()[3] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: Seq::<TID>::empty() }),
    wexec()[4] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    wexec()[5] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: Seq::<TID>::empty() }),
    wexec()[6] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
{
}

pub proof fn wreac_idx()
  ensures
    wreac().len() == 4,
    wreac()[0] == re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    wreac()[1] == re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: 0int }),
    wreac()[2] == re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat) }),
    wreac()[3] == re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())) }),
{
}

// For any index k, the executor tick/park/poll flags of the witness.
proof fn wexec_flags(k: int)
  ensures
    k != 0 ==> !el::is_tick_begin_at(wexec(), k),
    k != 6 ==> !el::is_tick_end_at(wexec(), k),
    k != 4 ==> !el::is_park_at(wexec(), k),
    !el::is_poll_task_at(wexec(), k),
{
  wexec_idx();
  if k == 0 {
  } else if k == 1 {
  } else if k == 2 {
  } else if k == 3 {
  } else if k == 4 {
  } else if k == 5 {
  } else if k == 6 {
  } else {
  }
}

// For any index j, the witness reactor log has none of the task-initiated /
// wake / register / set-waker events, and its only park boundaries are 0 / 3.
pub proof fn wreac_flags(j: int)
  ensures
    !rl::is_succ_register_timer_at(wreac(), j),
    !rl::is_deregister_timer_at(wreac(), j),
    !rl::io_syscall_registered_at(wreac(), j),
    !rl::io_syscall_register_at(wreac(), j),
    !rl::io_syscall_deregistered_at(wreac(), j),
    !rl::is_succ_set_waker_at(wreac(), j),
    !rl::is_set_waker_at(wreac(), j),
    !rl::is_wake_task_at(wreac(), j),
    !rl::is_io_event_ready_at(wreac(), j),
    !crate::reactor::invariants::inbound_register_io_result::is_inbound_register_io_end_at(wreac(), j),
    !crate::reactor::invariants::inbound_deregister_io_result::is_inbound_deregister_io_end_at(wreac(), j),
    j != 0 ==> !rl::is_park_begin_at(wreac(), j),
    j != 3 ==> !rl::is_park_end_at(wreac(), j),
    (0 <= j < 4) ==> !is_task_initiated_reactor_event(wreac()[j]),
{
  wreac_idx();
  if j == 0 {
  } else if j == 1 {
  } else if j == 2 {
  } else if j == 3 {
  } else {
  }
}

// ============================================================================
// Executor obligation
// ============================================================================

#[verifier::rlimit(50)]
proof fn exec_action_safety_holds()
  ensures
    crate::executor::invariants::executor_action_safety_inv(wexec()),
{
  let l = wexec();
  wexec_idx();

  // fifo_task_selection: acceptance is_poll_task_at — never fires.
  let p_fifo = crate::executor::invariants::fifo_task_selection::fifo_task_selection();
  assert(crate::framework::action_safety::action_safety_satisfied(p_fifo, l)) by {
    assert forall |i: int| #[trigger] (p_fifo.acceptance)(l, i) implies (p_fifo.validity)(l, i) by {
      wexec_flags(i);
    }
  }

  // valid_task_polling: acceptance is_poll_task_at — never fires.
  let p_vtp = crate::executor::invariants::valid_task_polling::valid_task_polling();
  assert(crate::framework::action_safety::action_safety_satisfied(p_vtp, l)) by {
    assert forall |i: int| #[trigger] (p_vtp.acceptance)(l, i) implies (p_vtp.validity)(l, i) by {
      wexec_flags(i);
    }
  }

  // tick_has_park: acceptance is_tick_end_at fires at i=6, witness park at 4.
  let p_park = crate::executor::invariants::tick_has_park::tick_has_park();
  assert(crate::framework::action_safety::action_safety_satisfied(p_park, l)) by {
    assert forall |i: int| #[trigger] (p_park.acceptance)(l, i) implies (p_park.validity)(l, i) by {
      wexec_flags(i);
      if i == 6 {
        assert(el::is_park_at(l, 4));
        assert forall |k: int| 4 < k < 6 implies !#[trigger] el::is_tick_begin_at(l, k) by {
          wexec_flags(k);
        }
      }
    }
  }

  // tick_has_pop_injection: witness PopInjection at 1.
  let p_pop = crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pop, l)) by {
    assert forall |i: int| #[trigger] (p_pop.acceptance)(l, i) implies (p_pop.validity)(l, i) by {
      wexec_flags(i);
      if i == 6 {
        assert(el::is_pop_injection_at(l, 1));
        assert forall |k: int| 1 < k < 6 implies !#[trigger] el::is_tick_begin_at(l, k) by {
          wexec_flags(k);
        }
      }
    }
  }

  // tick_has_drain_deferred: witness Drain(Deferred) at 2.
  let p_dd = crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred();
  assert(crate::framework::action_safety::action_safety_satisfied(p_dd, l)) by {
    assert forall |i: int| #[trigger] (p_dd.acceptance)(l, i) implies (p_dd.validity)(l, i) by {
      wexec_flags(i);
      if i == 6 {
        assert(el::is_drain_deferred_at(l, 2));
        assert forall |k: int| 2 < k < 6 implies !#[trigger] el::is_tick_begin_at(l, k) by {
          wexec_flags(k);
        }
      }
    }
  }

  // tick_has_drain_task_wake: witness Drain(TaskWake) at 3.
  let p_dt = crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake();
  assert(crate::framework::action_safety::action_safety_satisfied(p_dt, l)) by {
    assert forall |i: int| #[trigger] (p_dt.acceptance)(l, i) implies (p_dt.validity)(l, i) by {
      wexec_flags(i);
      if i == 6 {
        assert(el::is_drain_task_wake_at(l, 3));
        assert forall |k: int| 3 < k < 6 implies !#[trigger] el::is_tick_begin_at(l, k) by {
          wexec_flags(k);
        }
      }
    }
  }
}

#[verifier::rlimit(50)]
proof fn exec_local_liveness_holds()
  ensures
    crate::executor::invariants::executor_local_liveness_inv(wexec()),
{
  let l = wexec();
  wexec_idx();

  // park_drain_reactor_wake: acceptance is_park_at fires at i=4, witness j=5.
  let p_pdrw = crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_pdrw, l)) by {
    assert forall |i: int| #[trigger] (p_pdrw.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_pdrw.fulfillment)(l, i, j)]
        j > i && (p_pdrw.fulfillment)(l, i, j) && (p_pdrw.timely)(l, i, j) by {
      wexec_flags(i);
      if i == 4 {
        assert(el::is_drain_reactor_wake_at(l, 5));
        assert((p_pdrw.fulfillment)(l, 4, 5));
        assert((p_pdrw.timely)(l, 4, 5));
        assert(5 > 4 && (p_pdrw.fulfillment)(l, 4, 5) && (p_pdrw.timely)(l, 4, 5));
      }
    }
  }

  // tick_polls_if_runnable: acceptance requires tick_begin AND non-empty queue.
  // The only tick_begin is at 0 where the queue is empty, so acceptance never fires.
  let p_tpr = crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(p_tpr, l)) by {
    assert forall |i: int| #[trigger] (p_tpr.acceptance)(l, i) implies
      exists |j: int| #![trigger (p_tpr.fulfillment)(l, i, j)]
        j > i && (p_tpr.fulfillment)(l, i, j) && (p_tpr.timely)(l, i, j) by {
      wexec_flags(i);
      if i == 0 {
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, 0)
          =~= Seq::<TID>::empty());
      }
    }
  }
}

proof fn exec_progress_holds()
  ensures
    crate::executor::executor_progress(Seq::<ee::ExecutorEvent>::empty(), wexec()),
{
  let l = wexec();
  wexec_idx();
  exec_action_safety_holds();
  exec_local_liveness_holds();
  assert(crate::executor::invariants::executor_inv(l));

  assert(Seq::<ee::ExecutorEvent>::empty() =~= l.subrange(0, 0));

  // is_complete_tick_cycle(l, 0, 7)
  assert(crate::executor::is_complete_tick_cycle(l, 0, 7)) by {
    assert(el::is_tick_begin_at(l, 0));
    assert(el::is_tick_end_at(l, 6));
    assert forall |k: int| 0 < k < 6 implies
      !#[trigger] el::is_tick_begin_at(l, k) && !el::is_tick_end_at(l, k) by {
      wexec_flags(k);
    }
  }
}

// ============================================================================
// Reactor obligation
// ============================================================================

#[verifier::rlimit(50)]
proof fn reac_action_safety_holds()
  ensures
    crate::reactor::invariants::reactor_action_safety_inv(wreac()),
{
  let l = wreac();
  wreac_idx();

  // park_has_timestamp: fires at park_end i=3, witness GetCurrentTime at 1.
  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      wreac_flags(i);
      if i == 3 {
        assert(rl::current_park_start(l, 1) == 0);
        assert(rl::current_park_start(l, 2) == 0);
        assert(rl::current_park_start(l, 3) == 0);
        assert(rl::is_get_current_time_at(l, 1));
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, 3));
      }
    }
  }

  // park_poll_once: fires at park_end i=3, exactly one PollEvents (at 2) in cycle.
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      wreac_flags(i);
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

  reac_vacuous_action_safety_holds();
}

// The 14 action-safety properties whose acceptance never fires on the witness.
#[verifier::rlimit(50)]
proof fn reac_vacuous_action_safety_holds()
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_deadline_future::timer_deadline_future(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_ready_in_park::io_ready_in_park(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_waker_validity::timer_waker_validity(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_waker_validity::io_waker_validity(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::wake_has_registration::wake_has_registration(), wreac()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::set_waker_active_io::set_waker_active_io(), wreac()),
{
  let l = wreac();

  let p1 = crate::reactor::invariants::timer_deadline_future::timer_deadline_future();
  assert(crate::framework::action_safety::action_safety_satisfied(p1, l)) by {
    assert forall |i: int| #[trigger] (p1.acceptance)(l, i) implies (p1.validity)(l, i) by { wreac_flags(i); }
  }
  let p2 = crate::reactor::invariants::io_ready_in_park::io_ready_in_park();
  assert(crate::framework::action_safety::action_safety_satisfied(p2, l)) by {
    assert forall |i: int| #[trigger] (p2.acceptance)(l, i) implies (p2.validity)(l, i) by { wreac_flags(i); }
  }
  let p3 = crate::reactor::invariants::timer_waker_validity::timer_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p3, l)) by {
    assert forall |i: int| #[trigger] (p3.acceptance)(l, i) implies (p3.validity)(l, i) by { wreac_flags(i); }
  }
  let p4 = crate::reactor::invariants::io_waker_validity::io_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p4, l)) by {
    assert forall |i: int| #[trigger] (p4.acceptance)(l, i) implies (p4.validity)(l, i) by { wreac_flags(i); }
  }
  let p5 = crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p5, l)) by {
    assert forall |i: int| #[trigger] (p5.acceptance)(l, i) implies (p5.validity)(l, i) by { wreac_flags(i); }
  }
  let p6 = crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p6, l)) by {
    assert forall |i: int| #[trigger] (p6.acceptance)(l, i) implies (p6.validity)(l, i) by { wreac_flags(i); }
  }
  let p7 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer();
  assert(crate::framework::action_safety::action_safety_satisfied(p7, l)) by {
    assert forall |i: int| #[trigger] (p7.acceptance)(l, i) implies (p7.validity)(l, i) by { wreac_flags(i); }
  }
  let p8 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p8, l)) by {
    assert forall |i: int| #[trigger] (p8.acceptance)(l, i) implies (p8.validity)(l, i) by { wreac_flags(i); }
  }
  let p9 = crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p9, l)) by {
    assert forall |i: int| #[trigger] (p9.acceptance)(l, i) implies (p9.validity)(l, i) by { wreac_flags(i); }
  }
  let p10 = crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p10, l)) by {
    assert forall |i: int| #[trigger] (p10.acceptance)(l, i) implies (p10.validity)(l, i) by { wreac_flags(i); }
  }
  let p11 = crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p11, l)) by {
    assert forall |i: int| #[trigger] (p11.acceptance)(l, i) implies (p11.validity)(l, i) by { wreac_flags(i); }
  }
  let p12 = crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p12, l)) by {
    assert forall |i: int| #[trigger] (p12.acceptance)(l, i) implies (p12.validity)(l, i) by { wreac_flags(i); }
  }
  let p13 = crate::reactor::invariants::wake_has_registration::wake_has_registration();
  assert(crate::framework::action_safety::action_safety_satisfied(p13, l)) by {
    assert forall |i: int| #[trigger] (p13.acceptance)(l, i) implies (p13.validity)(l, i) by { wreac_flags(i); }
  }
  let p14 = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p14, l)) by {
    assert forall |i: int| #[trigger] (p14.acceptance)(l, i) implies (p14.validity)(l, i) by { wreac_flags(i); }
  }
}

#[verifier::rlimit(50)]
proof fn reac_local_liveness_holds()
  ensures
    crate::reactor::invariants::reactor_local_liveness_inv(wreac()),
{
  let l = wreac();

  let q1 = crate::reactor::invariants::wake_on_expired::wake_on_expired();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q1, l)) by {
    assert forall |i: int| #[trigger] (q1.acceptance)(l, i) implies
      exists |j: int| #![trigger (q1.fulfillment)(l, i, j)]
        j > i && (q1.fulfillment)(l, i, j) && (q1.timely)(l, i, j) by {
      wreac_flags(i);
    }
  }
  let q2 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_readable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q2, l)) by {
    assert forall |i: int| #[trigger] (q2.acceptance)(l, i) implies
      exists |j: int| #![trigger (q2.fulfillment)(l, i, j)]
        j > i && (q2.fulfillment)(l, i, j) && (q2.timely)(l, i, j) by {
      wreac_flags(i);
    }
  }
  let q3 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_writable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q3, l)) by {
    assert forall |i: int| #[trigger] (q3.acceptance)(l, i) implies
      exists |j: int| #![trigger (q3.fulfillment)(l, i, j)]
        j > i && (q3.fulfillment)(l, i, j) && (q3.timely)(l, i, j) by {
      wreac_flags(i);
    }
  }
}

pub proof fn reac_progress_holds()
  ensures
    crate::reactor::reactor_progress(Seq::<re::ReactorEvent>::empty(), wreac()),
{
  let l = wreac();
  wreac_idx();
  reac_action_safety_holds();
  reac_local_liveness_holds();
  assert(crate::reactor::invariants::reactor_inv(l));

  assert(Seq::<re::ReactorEvent>::empty() =~= l.subrange(0, 0));

  // is_complete_park_cycle(l, 0, 4)
  assert(crate::reactor::is_complete_park_cycle(l, 0, 4)) by {
    assert(rl::is_park_begin_at(l, 0));
    assert(rl::is_park_end_at(l, 3));
    assert forall |k: int| 0 < k < 3 implies
      !#[trigger] rl::is_park_begin_at(l, k) && !rl::is_park_end_at(l, k) by {
      wreac_flags(k);
    }
  }

  // witness park_start=0, park_end=4; surrounding foralls vacuous.
  assert(exists |ps: int, pe: int|
    0 <= ps && ps < pe && pe <= l.len() &&
    crate::reactor::is_complete_park_cycle(l, ps, pe) &&
    (forall |i: int| 0 <= i < ps ==> re::is_inbound_non_park(#[trigger] l[i])) &&
    (forall |i: int| pe <= i < l.len() ==> re::is_inbound_non_park(#[trigger] l[i]))) by {
    assert(crate::reactor::is_complete_park_cycle(l, 0, 4));
  }
}

// ============================================================================
// Cross-module alignment obligation
// ============================================================================

#[verifier::rlimit(50)]
proof fn am_state_holds()
  ensures
    action_mediation_state(wstate()),
{
  let s = wstate();
  wreac_idx();

  assert(reactor_outbound_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() && is_task_initiated_reactor_event(s.reactor_log[j])
      implies false by {
      wreac_flags(j);
    }
  }
  assert(reactor_registration_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() &&
      (re::is_succ_register_timer(s.reactor_log[j]) || re::is_succ_io_syscall_register(s.reactor_log[j]))
      implies false by {
      wreac_flags(j);
    }
  }
  monotonic_alignment_holds_empty(s);
  assert(succ_deregister_by_owner(s)) by { reveal(succ_deregister_by_owner); }
  assert(deregister_matches_own_registration(s)) by { reveal(deregister_matches_own_registration); }
  assert(deregister_io_matches_own_registration(s)) by { reveal(deregister_io_matches_own_registration); }
  assert(succ_deregister_io_by_owner(s)) by { reveal(succ_deregister_io_by_owner); }
}

proof fn am_step_holds()
  ensures
    action_mediation_step(empty_composed_state(), wstate()),
{
  let s = empty_composed_state();
  let s2 = wstate();
  wreac_idx();
  assert(reactor_outbound_has_task_operation(s, s2)) by {
    assert forall |j: int| #![trigger s2.reactor_log[j]]
      s.reactor_log.len() as int <= j < s2.reactor_log.len() &&
      is_task_initiated_reactor_event(s2.reactor_log[j])
      implies false by {
      wreac_flags(j);
    }
  }
}

proof fn oc_state_holds()
  ensures
    observation_consistency_state(wstate()),
{
  let s = wstate();
  wexec_idx();
  assert(polled_task_has_log_inv(s)) by {
    assert forall |tid: TaskId|
      el::has_poll_for_id(s.executor_log, tid) implies s.task_logs.contains_key(tid) by {
      assert forall |i: int| #![trigger s.executor_log[i]]
        0 <= i < s.executor_log.len() implies !el::is_poll_task_for_id_at(s.executor_log, i, tid) by {
        wexec_flags(i);
      }
    }
  }
}

proof fn wr_step_holds()
  ensures
    wakeup_routing_step(empty_composed_state(), wstate()),
{
  let s = empty_composed_state();
  let s2 = wstate();
  wexec_idx();
  wreac_idx();

  assert(count_park_events_in(wexec(), 7, 7) == 0);
  assert(count_park_events_in(wexec(), 6, 7) == 0) by { wexec_flags(6); }
  assert(count_park_events_in(wexec(), 5, 7) == 0) by { wexec_flags(5); }
  assert(count_park_events_in(wexec(), 4, 7) == 1) by { wexec_flags(4); }
  assert(count_park_events_in(wexec(), 3, 7) == 1) by { wexec_flags(3); }
  assert(count_park_events_in(wexec(), 2, 7) == 1) by { wexec_flags(2); }
  assert(count_park_events_in(wexec(), 1, 7) == 1) by { wexec_flags(1); }
  assert(count_park_events_in(wexec(), 0, 7) == 1) by { wexec_flags(0); }

  assert(count_park_cycles_in(wreac(), 4, 4) == 0);
  assert(count_park_cycles_in(wreac(), 3, 4) == 1) by { wreac_flags(3); }
  assert(count_park_cycles_in(wreac(), 2, 4) == 1) by { wreac_flags(2); }
  assert(count_park_cycles_in(wreac(), 1, 4) == 1) by { wreac_flags(1); }
  assert(count_park_cycles_in(wreac(), 0, 4) == 1) by { wreac_flags(0); }

  assert(park_alignment(s, s2));
}

#[verifier::rlimit(50)]
proof fn cross_holds()
  ensures
    cross_module_alignment(empty_composed_state(), wstate()),
{
  reveal(cross_module_alignment);
  let s = empty_composed_state();
  let s2 = wstate();

  am_state_holds();
  am_step_holds();
  oc_state_holds();
  // observation_consistency_step: all conjuncts quantify over new polls / task
  // log growth; wexec has no PollTask and task_logs is empty, so all vacuous.
  assert(observation_consistency_step(s, s2)) by {
    wexec_idx();
    assert(pending_poll_alignment(s, s2)) by {
      assert forall |tid: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[tid]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_pending_for_id_at(s2.executor_log, i, tid) &&
        s2.task_logs.contains_key(tid)
        implies task_log_ends_with_pending(s2.task_logs[tid]) by {
        wexec_flags(i);
      }
    }
    assert(new_poll_has_task_log(s, s2)) by {
      assert forall |tid: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[tid]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, tid)
        implies s2.task_logs.contains_key(tid) by {
        wexec_flags(i);
      }
    }
    assert(new_poll_changes_task_log(s, s2)) by {
      assert forall |tid: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[tid]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, tid) &&
        s2.task_logs.contains_key(tid)
        implies s.task_logs[tid].len() < s2.task_logs[tid].len() by {
        wexec_flags(i);
      }
    }
  }
  wr_step_holds();
}

// ============================================================================
// Assembly
// ============================================================================

proof fn ext_holds()
  ensures
    is_extension_of(empty_composed_state(), wstate()),
{
  let s = empty_composed_state();
  let s2 = wstate();
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by {
    assert(s.executor_log =~= s2.executor_log.subrange(0, 0));
  }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by {
    assert(s.reactor_log =~= s2.reactor_log.subrange(0, 0));
  }
}

// INTENTIONAL UNCALLED ROOT (audit): the minimal anti-vacuity
// witness for the transition relation itself — composed_progress is satisfiable
// on a bare idle tick from the empty state, independently of the four wake-path
// witnesses (whose traces also exhibit composed_progress on richer states).
// This file's wstate/wexec/wreac apparatus exists to support this root.
#[verifier::rlimit(50)]
pub proof fn composed_progress_witness()
  ensures
    composed_progress(empty_composed_state(), wstate()),
{
  reveal(composed_progress);
  let s = empty_composed_state();
  let s2 = wstate();

  ext_holds();
  exec_progress_holds();
  reac_progress_holds();
  cross_holds();
  monotonic_alignment_holds_empty(s2);
  // Phase B: reactor_wake_drain_step vacuous — empty_composed_state's reactor log is empty.
  crate::composed::proof::assumption_satisfiable::no_reactor_wake_pending_no_waketask(s);
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2));
  // Phase C: taskwake_drain_step vacuous — empty_composed_state has empty task_logs.
  crate::composed::proof::assumption_satisfiable::no_taskwake_pending_no_woken(s);
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2));
}

}
