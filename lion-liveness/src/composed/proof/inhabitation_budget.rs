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
#[allow(unused_imports)]
use crate::utilities::spec::events as ue;
use crate::utilities::spec::log as ul;
#[cfg(verus_keep_ghost)]
use crate::composed::proof::inhabitation_goal_wake::*;
#[cfg(verus_keep_ghost)]
use crate::composed::proof::assumption_satisfiable::{env_N,
  bounded_poll_count_here_with_bound, io_ready_forward_here,
  contract_io_assumption_here, io_assumption_here,
  env_holds_at_state_core, end_to_end_env, arrival_witness, ete_reachable_N,
  taskwake_arrival_within_vacuous};
#[cfg(verus_keep_ghost)]
use crate::composed::spec::assumptions::{
  timer_deadline_gap_bounded, timer_resources_remain_active,
  queue_length_bounded, get_max_timer_deadline_gap, get_max_queue_length};

verus! {

// ============================================================================
// Budget-gap witness family (closes the budget gap: the base witnesses inhabit only n=2, while the theorem instantiates n* = chunk + cap·chunk).
//
// The wake witness (inhabitation_goal_wake.rs) inhabits the top theorem's
// response-filter domain at budget n = 2 only, while the theorem's proof
// instantiates its ∃n at the symbolic n* = chunk + cap·chunk. This file closes
// the gap: the reached state bs2 is extended by k IDLE scheduler ticks
// (executor: TickBegin / Pop(None) / empty Drains / Park / TickEnd; reactor:
// one empty park cycle per tick with a fresh timestamp), giving an env_N-good
// (k+2)-step trace for EVERY k — i.e. the ∀-trace domain is inhabited at every
// budget n >= 2, in particular at any proof-instantiated n* >= 2.
//
//   bext(tid, 0)   == bs2(tid)
//   bext(tid, k+1) == bext(tid, k) + one idle executor tick
//                                  + one empty reactor park cycle (ts = 3+k)
// ============================================================================

// --- one idle executor tick (no pop delivery, no polls, empty drains) ---
pub open spec fn bidle_tick() -> el::Log {
  seq![
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
      source: ee::DrainSource::ReactorWake, task_ids: Seq::<TID>::empty(),
    }),
    ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
  ]
}

// --- one empty reactor park cycle sampling timestamp ts ---
pub open spec fn bpark_cycle(ts: int) -> rl::Log {
  seq![
    re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: ts }),
    re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat),
    }),
    re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())),
    }),
  ]
}

pub open spec fn bextexec(tid: TID, k: nat) -> el::Log
  decreases k
{
  if k == 0 { bexec2(tid) } else { bextexec(tid, (k - 1) as nat) + bidle_tick() }
}

pub open spec fn bextreac(k: nat) -> rl::Log
  decreases k
{
  if k == 0 { breac2() } else { bextreac((k - 1) as nat) + bpark_cycle(2 + k as int) }
}

pub open spec fn bext(tid: TID, k: nat) -> ComposedState {
  ComposedState {
    executor_log: bextexec(tid, k),
    reactor_log: bextreac(k),
    task_logs: Map::<TaskId, ul::Log>::empty().insert(tid, btask_ready()),
    injection_schedule: bsched(tid),
  }
}

// ============================================================================
// Index / length lemmas
// ============================================================================

pub proof fn bidle_tick_idx()
  ensures
    bidle_tick().len() == 7,
    bidle_tick()[0] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: None }),
    bidle_tick()[1] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection { task: None }),
    bidle_tick()[2] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::Deferred, task_ids: Seq::<TID>::empty() }),
    bidle_tick()[3] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::TaskWake, task_ids: Seq::<TID>::empty() }),
    bidle_tick()[4] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Park),
    bidle_tick()[5] == ee::ExecutorEvent::Outbound(ee::OutboundCall::Drain {
      source: ee::DrainSource::ReactorWake, task_ids: Seq::<TID>::empty() }),
    bidle_tick()[6] == ee::ExecutorEvent::Inbound(ee::InboundCall::Tick { result: Some(()) }),
{
}

pub proof fn bpark_cycle_idx(ts: int)
  ensures
    bpark_cycle(ts).len() == 4,
    bpark_cycle(ts)[0] == re::ReactorEvent::Inbound(re::InboundCall::Park { timeout: None, result: None }),
    bpark_cycle(ts)[1] == re::ReactorEvent::Outbound(re::OutboundCall::GetCurrentTime { timestamp: ts }),
    bpark_cycle(ts)[2] == re::ReactorEvent::Outbound(re::OutboundCall::PollEvents {
      timeout: None, result: IoResultView::Ok(0nat) }),
    bpark_cycle(ts)[3] == re::ReactorEvent::Inbound(re::InboundCall::Park {
      timeout: None, result: Some(IoResultView::Ok(())) }),
{
}

pub proof fn bextexec_len(tid: TID, k: nat)
  ensures
    bextexec(tid, k).len() == 16 + 7 * k,
  decreases k
{
  bexec2_idx(tid);
  bidle_tick_idx();
  if k > 0 { bextexec_len(tid, (k - 1) as nat); }
}

pub proof fn bextreac_len(k: nat)
  ensures
    bextreac(k).len() == 10 + 4 * k,
  decreases k
{
  breac2_idx();
  bpark_cycle_idx(2 + k as int);
  if k > 0 { bextreac_len((k - 1) as nat); }
}

// ============================================================================
// Flags (forall-form): the family-wide per-index facts
// ============================================================================

// Executor: polls only at {6, 14}; the only Some-pop is at 1; base region
// coincides with bexec2.
pub proof fn bextexec_flags(tid: TID, k: nat)
  ensures
    bextexec(tid, k).len() == 16 + 7 * k,
    forall |q: int| #![trigger bextexec(tid, k)[q]]
      0 <= q < 16 ==> bextexec(tid, k)[q] == bexec2(tid)[q],
    forall |p: int| (p != 6 && p != 14) ==> !#[trigger] el::is_poll_task_at(bextexec(tid, k), p),
    forall |p: int| p != 1 ==>
      !(#[trigger] el::is_pop_injection_at(bextexec(tid, k), p) &&
        ee::get_pop_injection_task(bextexec(tid, k)[p]).is_some()),
  decreases k
{
  bextexec_len(tid, k);
  bexec2_idx(tid);
  bexec1_idx(tid);
  if k == 0 {
    let l = bexec2(tid);
    assert forall |p: int| (p != 6 && p != 14) implies !el::is_poll_task_at(l, p) by {
      bexec2_flags(tid, p);
    }
    assert forall |p: int| p != 1 implies
      !(el::is_pop_injection_at(l, p) && ee::get_pop_injection_task(l[p]).is_some()) by {
      bexec2_flags(tid, p);
      if p == 9 {
        assert(l[9] == ee::ExecutorEvent::Outbound(ee::OutboundCall::PopInjection { task: None }));
      }
    }
  } else {
    let l1 = bextexec(tid, (k - 1) as nat);
    let l = bextexec(tid, k);
    let len1 = l1.len() as int;
    bextexec_flags(tid, (k - 1) as nat);
    bidle_tick_idx();
    assert(len1 >= 16);
    assert forall |q: int| 0 <= q < 16 implies l[q] == bexec2(tid)[q] by {
      assert(l[q] == l1[q]);
    }
    assert forall |p: int| (p != 6 && p != 14) implies !el::is_poll_task_at(l, p) by {
      if 0 <= p < len1 {
        assert(l[p] == l1[p]);
        assert(!el::is_poll_task_at(l1, p));
      } else if len1 <= p < l.len() {
        let off = p - len1;
        assert(l[p] == bidle_tick()[off]);
        if off == 0 {} else if off == 1 {} else if off == 2 {} else if off == 3 {}
        else if off == 4 {} else if off == 5 {} else { assert(off == 6); }
      }
    }
    assert forall |p: int| p != 1 implies
      !(el::is_pop_injection_at(l, p) && ee::get_pop_injection_task(l[p]).is_some()) by {
      if 0 <= p < len1 {
        assert(l[p] == l1[p]);
        assert(!(el::is_pop_injection_at(l1, p) && ee::get_pop_injection_task(l1[p]).is_some()));
      } else if len1 <= p < l.len() {
        let off = p - len1;
        assert(l[p] == bidle_tick()[off]);
        if off == 0 {} else if off == 1 {} else if off == 2 {} else if off == 3 {}
        else if off == 4 {} else if off == 5 {} else { assert(off == 6); }
      }
    }
  }
}

// Reactor: the sole register is @0 (rid 7 / deadline 2 / waker 3), the sole
// WakeTask is @8; no deregisters / io registrations / set-wakers / io-ready
// anywhere; base region coincides with breac2.
pub proof fn bextreac_flags(k: nat)
  ensures
    bextreac(k).len() == 10 + 4 * k,
    forall |q: int| #![trigger bextreac(k)[q]]
      0 <= q < 10 ==> bextreac(k)[q] == breac2()[q],
    rl::is_succ_register_timer_at(bextreac(k), 0),
    re::get_register_timer_rid(bextreac(k)[0]) == RID(),
    re::get_register_timer_deadline(bextreac(k)[0]) == DL(),
    re::get_register_timer_waker(bextreac(k)[0]) == WK(),
    forall |j: int| j != 0 ==> !#[trigger] rl::is_succ_register_timer_at(bextreac(k), j),
    forall |j: int| !#[trigger] rl::is_deregister_timer_at(bextreac(k), j),
    forall |j: int| !#[trigger] rl::is_succ_deregister_timer_at(bextreac(k), j),
    forall |j: int| !#[trigger] rl::io_syscall_registered_at(bextreac(k), j),
    forall |j: int| !#[trigger] rl::io_syscall_register_at(bextreac(k), j),
    forall |j: int| !#[trigger] rl::io_syscall_deregistered_at(bextreac(k), j),
    forall |j: int| !#[trigger] rl::is_succ_set_waker_at(bextreac(k), j),
    forall |j: int| !#[trigger] rl::is_set_waker_at(bextreac(k), j),
    rl::is_wake_task_at(bextreac(k), 8),
    re::get_wake_task_source_rid(bextreac(k)[8]) == RID(),
    re::get_wake_task_waker(bextreac(k)[8]) == WK(),
    forall |j: int| j != 8 ==> !#[trigger] rl::is_wake_task_at(bextreac(k), j),
    forall |j: int| !#[trigger] rl::is_io_event_ready_at(bextreac(k), j),
    forall |j: int|
      !#[trigger] crate::reactor::invariants::inbound_register_io_result::is_inbound_register_io_end_at(bextreac(k), j),
    forall |j: int|
      !#[trigger] crate::reactor::invariants::inbound_deregister_io_result::is_inbound_deregister_io_end_at(bextreac(k), j),
  decreases k
{
  bextreac_len(k);
  breac2_idx();
  breac1_idx();
  if k == 0 {
    let l = breac2();
    assert forall |j: int| j != 0 implies !rl::is_succ_register_timer_at(l, j) by { breac2_flags(j); }
    assert forall |j: int| !rl::is_deregister_timer_at(l, j) by { breac2_flags(j); }
    assert forall |j: int| !rl::is_succ_deregister_timer_at(l, j) by { breac2_flags(j); }
    assert forall |j: int| !rl::io_syscall_registered_at(l, j) by { breac2_flags(j); }
    assert forall |j: int| !rl::io_syscall_register_at(l, j) by { breac2_flags(j); }
    assert forall |j: int| !rl::io_syscall_deregistered_at(l, j) by { breac2_flags(j); }
    assert forall |j: int| !rl::is_succ_set_waker_at(l, j) by { breac2_flags(j); }
    assert forall |j: int| !rl::is_set_waker_at(l, j) by { breac2_flags(j); }
    assert forall |j: int| j != 8 implies !rl::is_wake_task_at(l, j) by { breac2_flags(j); }
    assert forall |j: int| !rl::is_io_event_ready_at(l, j) by { breac2_flags(j); }
    breac2_flags(0);
    breac2_flags(8);
    assert forall |j: int|
      !crate::reactor::invariants::inbound_register_io_result::is_inbound_register_io_end_at(l, j) by {
      breac2_flags(j);
      if 0 <= j < 10 {
        if j == 0 {} else if j == 1 {} else if j == 2 {} else if j == 3 {} else if j == 4 {}
        else if j == 5 {} else if j == 6 {} else if j == 7 {} else if j == 8 {} else { assert(j == 9); }
      }
    }
    assert forall |j: int|
      !crate::reactor::invariants::inbound_deregister_io_result::is_inbound_deregister_io_end_at(l, j) by {
      breac2_flags(j);
      if 0 <= j < 10 {
        if j == 0 {} else if j == 1 {} else if j == 2 {} else if j == 3 {} else if j == 4 {}
        else if j == 5 {} else if j == 6 {} else if j == 7 {} else if j == 8 {} else { assert(j == 9); }
      }
    }
  } else {
    let l1 = bextreac((k - 1) as nat);
    let l = bextreac(k);
    let len1 = l1.len() as int;
    bextreac_flags((k - 1) as nat);
    bpark_cycle_idx(2 + k as int);
    assert(len1 >= 10);
    assert forall |q: int| 0 <= q < 10 implies l[q] == breac2()[q] by {
      assert(l[q] == l1[q]);
    }
    assert(l[0] == l1[0]);
    assert(l[8] == l1[8]);
    assert forall |j: int| j != 0 implies !rl::is_succ_register_timer_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::is_succ_register_timer_at(l1, j)); }
    }
    assert forall |j: int| !rl::is_deregister_timer_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::is_deregister_timer_at(l1, j)); }
    }
    assert forall |j: int| !rl::is_succ_deregister_timer_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::is_succ_deregister_timer_at(l1, j)); }
    }
    assert forall |j: int| !rl::io_syscall_registered_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::io_syscall_registered_at(l1, j)); }
    }
    assert forall |j: int| !rl::io_syscall_register_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::io_syscall_register_at(l1, j)); }
    }
    assert forall |j: int| !rl::io_syscall_deregistered_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::io_syscall_deregistered_at(l1, j)); }
    }
    assert forall |j: int| !rl::is_succ_set_waker_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::is_succ_set_waker_at(l1, j)); }
    }
    assert forall |j: int| !rl::is_set_waker_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::is_set_waker_at(l1, j)); }
    }
    assert forall |j: int| j != 8 implies !rl::is_wake_task_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::is_wake_task_at(l1, j)); }
    }
    assert forall |j: int| !rl::is_io_event_ready_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 { assert(!rl::is_io_event_ready_at(l1, j)); }
    }
    assert forall |j: int|
      !crate::reactor::invariants::inbound_register_io_result::is_inbound_register_io_end_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 {
        assert(!crate::reactor::invariants::inbound_register_io_result::is_inbound_register_io_end_at(l1, j));
      }
    }
    assert forall |j: int|
      !crate::reactor::invariants::inbound_deregister_io_result::is_inbound_deregister_io_end_at(l, j) by {
      bextreac_step_case(k, j);
      if 0 <= j < len1 {
        assert(!crate::reactor::invariants::inbound_deregister_io_result::is_inbound_deregister_io_end_at(l1, j));
      }
    }
  }
}

// Step-case index bridge: identifies l[j] for j in the base region (== l1[j])
// or the appended park cycle (== the concrete bpark_cycle event).
proof fn bextreac_step_case(k: nat, j: int)
  requires
    k >= 1,
  ensures
    0 <= j < bextreac((k - 1) as nat).len() ==> bextreac(k)[j] == bextreac((k - 1) as nat)[j],
    ({
      let len1 = bextreac((k - 1) as nat).len() as int;
      (len1 <= j < bextreac(k).len() ==> bextreac(k)[j] == bpark_cycle(2 + k as int)[j - len1])
    }),
    bextreac(k).len() == bextreac((k - 1) as nat).len() + 4,
{
  bpark_cycle_idx(2 + k as int);
}

// ============================================================================
// Generic append helpers
// ============================================================================

// injected_tasks is unchanged when the appended segment delivers no task.
proof fn injected_append_none(l1: el::Log, t: el::Log)
  requires
    forall |p: int| 0 <= p < t.len() ==>
      !(ee::is_pop_injection(#[trigger] t[p]) && ee::get_pop_injection_task(t[p]).is_some()),
  ensures
    crate::executor::spec::injection_schedule::injected_tasks(l1 + t) =~=
      crate::executor::spec::injection_schedule::injected_tasks(l1),
  decreases t.len()
{
  use crate::executor::spec::injection_schedule::injected_tasks;
  if t.len() == 0 {
    assert(l1 + t =~= l1);
  } else {
    let l = l1 + t;
    let t0 = t.subrange(0, t.len() - 1);
    assert(l.subrange(0, l.len() - 1) =~= l1 + t0);
    assert(l[l.len() - 1] == t[t.len() - 1]);
    assert forall |p: int| 0 <= p < t0.len() implies
      !(ee::is_pop_injection(#[trigger] t0[p]) && ee::get_pop_injection_task(t0[p]).is_some()) by {
      assert(t0[p] == t[p]);
    }
    injected_append_none(l1, t0);
    assert(injected_tasks(l) =~= injected_tasks(l1 + t0));
  }
}

// current_park_start only reads indices < i, so it is prefix-stable.
proof fn cps_prefix(l1: rl::Log, l: rl::Log, i: int)
  requires
    rl::is_prefix_of(l1, l),
    0 <= i <= l1.len(),
  ensures
    rl::current_park_start(l, i) == rl::current_park_start(l1, i),
  decreases i
{
  if i > 0 {
    assert(l[i - 1] == l1[i - 1]);
    if rl::is_park_begin_at(l1, i - 1) {
      assert(rl::is_park_begin_at(l, i - 1));
    } else if rl::is_park_end_at(l1, i - 1) {
      assert(rl::is_park_end_at(l, i - 1));
      assert(!rl::is_park_begin_at(l, i - 1));
    } else {
      assert(!rl::is_park_begin_at(l, i - 1));
      assert(!rl::is_park_end_at(l, i - 1));
      cps_prefix(l1, l, i - 1);
    }
  }
}

// count_poll_events_in_range over a range inside the prefix is prefix-stable.
proof fn cper_prefix(l1: rl::Log, l: rl::Log, start: int, end: int)
  requires
    rl::is_prefix_of(l1, l),
    0 <= start <= end,
    end <= l1.len(),
  ensures
    crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l, start, end) ==
      crate::reactor::invariants::park_poll_once::count_poll_events_in_range(l1, start, end),
  decreases (if end > start { end - start } else { 0 })
{
  if 0 <= start < end {
    assert(l[start] == l1[start]);
    assert(rl::is_poll_events_at(l, start) == rl::is_poll_events_at(l1, start));
    cper_prefix(l1, l, start + 1, end);
  }
}

// find_last_set_waker is -1 on a log with no SuccSetWaker anywhere.
proof fn no_sw_find_last_none(l: rl::Log, rid: ResourceIdView, m: int)
  requires
    forall |j: int| !#[trigger] rl::is_succ_set_waker_at(l, j),
  ensures
    crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(l, rid, m) == -1,
  decreases (if m > 0 { m } else { 0 })
{
  if m > 0 {
    assert(!rl::is_succ_set_waker_at(l, m - 1));
    no_sw_find_last_none(l, rid, m - 1);
  }
}

// ============================================================================
// Executor family: queue, polls, injection
// ============================================================================

pub proof fn bextexec_queue(tid: TID, k: nat)
  ensures
    forall |i: int| 0 <= i <= bextexec(tid, k).len() ==>
      #[trigger] crate::executor::invariants::fifo_task_selection::fifo_queue_at(bextexec(tid, k), i).len() <= 1,
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(
      bextexec(tid, k), bextexec(tid, k).len() as int) =~= Seq::<TID>::empty(),
  decreases k
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  if k == 0 {
    bexec2_idx(tid);
    bexec2_queue_len(tid);
    bexec2_queue(tid);
  } else {
    let l1 = bextexec(tid, (k - 1) as nat);
    let l = bextexec(tid, k);
    let len1 = l1.len() as int;
    bextexec_queue(tid, (k - 1) as nat);
    bidle_tick_idx();
    assert(el::is_prefix_of(l1, l)) by { assert(l1 =~= l.subrange(0, len1)); }
    crate::executor::proof::prefix_monotonicity::fifo_queue_at_prefix_equals(l1, l, len1);
    assert(fifo_queue_at(l, len1) =~= Seq::<TID>::empty());
    assert(l[len1] == bidle_tick()[0]);
    assert(l[len1 + 1] == bidle_tick()[1]);
    assert(l[len1 + 2] == bidle_tick()[2]);
    assert(l[len1 + 3] == bidle_tick()[3]);
    assert(l[len1 + 4] == bidle_tick()[4]);
    assert(l[len1 + 5] == bidle_tick()[5]);
    assert(l[len1 + 6] == bidle_tick()[6]);
    assert(fifo_queue_at(l, len1 + 1) =~= Seq::<TID>::empty());
    assert(fifo_queue_at(l, len1 + 2) =~= Seq::<TID>::empty());
    assert(fifo_queue_at(l, len1 + 3) =~= Seq::<TID>::empty());
    assert(fifo_queue_at(l, len1 + 4) =~= Seq::<TID>::empty());
    assert(fifo_queue_at(l, len1 + 5) =~= Seq::<TID>::empty());
    assert(fifo_queue_at(l, len1 + 6) =~= Seq::<TID>::empty());
    assert(fifo_queue_at(l, len1 + 7) =~= Seq::<TID>::empty());
    assert forall |i: int| 0 <= i <= l.len() implies
      #[trigger] fifo_queue_at(l, i).len() <= 1 by {
      if i <= len1 {
        crate::executor::proof::prefix_monotonicity::fifo_queue_at_prefix_equals(l1, l, i);
      } else {
        if i == len1 + 1 {} else if i == len1 + 2 {} else if i == len1 + 3 {}
        else if i == len1 + 4 {} else if i == len1 + 5 {} else if i == len1 + 6 {}
        else { assert(i == len1 + 7); }
      }
    }
  }
}

pub proof fn bext_poll_facts(tid: TID, k: nat)
  ensures
    el::has_poll_for_id(bextexec(tid, k), tid),
    el::is_poll_ready_for_id_at(bextexec(tid, k), 14, tid),
    !el::last_poll_is_pending(bextexec(tid, k), tid),
    forall |t2: TID| t2 != tid ==> !#[trigger] el::has_poll_for_id(bextexec(tid, k), t2),
{
  let l = bextexec(tid, k);
  bextexec_flags(tid, k);
  bexec2_idx(tid);
  bexec1_idx(tid);
  assert(l[14] == bexec2(tid)[14]);
  assert(l[6] == bexec2(tid)[6]);
  assert(el::is_poll_ready_for_id_at(l, 14, tid));
  assert(el::has_poll_for_id(l, tid)) by {
    assert(el::is_poll_task_for_id_at(l, 14, tid));
  }
  crate::composed::proof::end_to_end::last_poll_idx_properties(l, tid);
  let idx = el::last_poll_idx_for_id(l, tid);
  assert(idx == 14) by {
    if idx != 14 {
      if idx == 6 {
        assert(el::is_poll_task_for_id_at(l, 14, tid));
        assert(false);
      } else {
        assert(!el::is_poll_task_at(l, idx));
        assert(false);
      }
    }
  }
  assert(!el::is_poll_pending_for_id_at(l, 14, tid));
  assert forall |t2: TID| t2 != tid implies !el::has_poll_for_id(l, t2) by {
    if el::has_poll_for_id(l, t2) {
      let i = choose |i: int| 0 <= i < l.len() && el::is_poll_task_for_id_at(l, i, t2);
      assert(i == 6 || i == 14);
      assert(ee::get_poll_task_id(l[i]) == tid);
      assert(false);
    }
  }
}

pub proof fn bext_injected(tid: TID, k: nat)
  ensures
    crate::executor::spec::injection_schedule::injected_tasks(bextexec(tid, k))
      =~= seq![crate::executor::spec::types::TaskView { id: tid }],
    crate::executor::spec::injection_schedule::pops_deliver_schedule(bextexec(tid, k), bsched(tid)),
  decreases k
{
  use crate::executor::spec::injection_schedule::*;
  if k == 0 {
    bexec_injected(tid);
    bpops_deliver(tid);
  } else {
    bext_injected(tid, (k - 1) as nat);
    bidle_tick_idx();
    assert forall |p: int| 0 <= p < bidle_tick().len() implies
      !(ee::is_pop_injection(#[trigger] bidle_tick()[p]) &&
        ee::get_pop_injection_task(bidle_tick()[p]).is_some()) by {
      if p == 0 {} else if p == 1 {} else if p == 2 {} else if p == 3 {}
      else if p == 4 {} else if p == 5 {} else { assert(p == 6); }
    }
    injected_append_none(bextexec(tid, (k - 1) as nat), bidle_tick());
  }
  let q = bsched(tid);
  assert(injected_tasks(bextexec(tid, k)) =~= q.subrange(0, 1));
  assert(is_task_prefix(injected_tasks(bextexec(tid, k)), q));
  assert(injected_tasks(bextexec(tid, k)).len() >= 1);
}

pub proof fn bext_tid_unique(tid: TID, k: nat)
  ensures
    el::tid_unique(bextexec(tid, k), tid),
{
  let l = bextexec(tid, k);
  bextexec_flags(tid, k);
  assert forall |a: int, b: int|
    0 <= a < l.len() && 0 <= b < l.len() && a != b &&
    el::is_pop_injection_at(l, a) && ee::get_pop_injection_task(l[a]).is_some() &&
    ee::get_pop_injection_task(l[a]).unwrap().id == tid &&
    el::is_pop_injection_at(l, b) && ee::get_pop_injection_task(l[b]).is_some() &&
    ee::get_pop_injection_task(l[b]).unwrap().id == tid
    implies false by {
    assert(a == 1 && b == 1);
  }
}

// ============================================================================
// Generic: appending one idle tick preserves executor_inv
// ============================================================================

#[verifier::rlimit(50)]
proof fn exec_append_tick_reqs(l1: el::Log)
  requires
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_park::tick_has_park(), l1),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection(), l1),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred(), l1),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake(), l1),
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_park::tick_has_park(), l1 + bidle_tick()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection(), l1 + bidle_tick()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred(), l1 + bidle_tick()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake(), l1 + bidle_tick()),
{
  let l = l1 + bidle_tick();
  let len1 = l1.len() as int;
  bidle_tick_idx();
  assert(l[len1] == bidle_tick()[0]);
  assert(l[len1 + 1] == bidle_tick()[1]);
  assert(l[len1 + 2] == bidle_tick()[2]);
  assert(l[len1 + 3] == bidle_tick()[3]);
  assert(l[len1 + 4] == bidle_tick()[4]);
  assert(l[len1 + 5] == bidle_tick()[5]);
  assert(l[len1 + 6] == bidle_tick()[6]);

  let pk = crate::executor::invariants::tick_has_park::tick_has_park();
  assert forall |i: int| #[trigger] (pk.acceptance)(l, i) implies (pk.validity)(l, i) by {
    if i < len1 {
      assert(l[i] == l1[i]);
      assert((pk.acceptance)(l1, i));
      assert((pk.validity)(l1, i));
      let p0 = choose |p0: int| 0 <= p0 < i && el::is_park_at(l1, p0) &&
        (forall |kk: int| p0 < kk < i ==> !#[trigger] el::is_tick_begin_at(l1, kk));
      assert(l[p0] == l1[p0]);
      assert(el::is_park_at(l, p0));
      assert forall |kk: int| p0 < kk < i implies !#[trigger] el::is_tick_begin_at(l, kk) by {
        assert(!el::is_tick_begin_at(l1, kk));
        assert(l[kk] == l1[kk]);
      }
    } else {
      let off = i - len1;
      if off == 0 {} else if off == 1 {} else if off == 2 {} else if off == 3 {}
      else if off == 4 {} else if off == 5 {} else {
        assert(off == 6);
        assert(el::is_park_at(l, len1 + 4));
        assert forall |kk: int| len1 + 4 < kk < i implies !#[trigger] el::is_tick_begin_at(l, kk) by {
          assert(kk == len1 + 5);
        }
      }
    }
  }
  let pp = crate::executor::invariants::tick_has_pop_injection::tick_has_pop_injection();
  assert forall |i: int| #[trigger] (pp.acceptance)(l, i) implies (pp.validity)(l, i) by {
    if i < len1 {
      assert(l[i] == l1[i]);
      assert((pp.acceptance)(l1, i));
      assert((pp.validity)(l1, i));
      let p0 = choose |p0: int| 0 <= p0 < i && el::is_pop_injection_at(l1, p0) &&
        (forall |kk: int| p0 < kk < i ==> !#[trigger] el::is_tick_begin_at(l1, kk));
      assert(l[p0] == l1[p0]);
      assert(el::is_pop_injection_at(l, p0));
      assert forall |kk: int| p0 < kk < i implies !#[trigger] el::is_tick_begin_at(l, kk) by {
        assert(!el::is_tick_begin_at(l1, kk));
        assert(l[kk] == l1[kk]);
      }
    } else {
      let off = i - len1;
      if off == 0 {} else if off == 1 {} else if off == 2 {} else if off == 3 {}
      else if off == 4 {} else if off == 5 {} else {
        assert(off == 6);
        assert(el::is_pop_injection_at(l, len1 + 1));
        assert forall |kk: int| len1 + 1 < kk < i implies !#[trigger] el::is_tick_begin_at(l, kk) by {
          if kk == len1 + 2 {} else if kk == len1 + 3 {} else if kk == len1 + 4 {}
          else { assert(kk == len1 + 5); }
        }
      }
    }
  }
  let dd = crate::executor::invariants::tick_has_drain_deferred::tick_has_drain_deferred();
  assert forall |i: int| #[trigger] (dd.acceptance)(l, i) implies (dd.validity)(l, i) by {
    if i < len1 {
      assert(l[i] == l1[i]);
      assert((dd.acceptance)(l1, i));
      assert((dd.validity)(l1, i));
      let p0 = choose |p0: int| 0 <= p0 < i && el::is_drain_deferred_at(l1, p0) &&
        (forall |kk: int| p0 < kk < i ==> !#[trigger] el::is_tick_begin_at(l1, kk));
      assert(l[p0] == l1[p0]);
      assert(el::is_drain_deferred_at(l, p0));
      assert forall |kk: int| p0 < kk < i implies !#[trigger] el::is_tick_begin_at(l, kk) by {
        assert(!el::is_tick_begin_at(l1, kk));
        assert(l[kk] == l1[kk]);
      }
    } else {
      let off = i - len1;
      if off == 0 {} else if off == 1 {} else if off == 2 {} else if off == 3 {}
      else if off == 4 {} else if off == 5 {} else {
        assert(off == 6);
        assert(el::is_drain_deferred_at(l, len1 + 2));
        assert forall |kk: int| len1 + 2 < kk < i implies !#[trigger] el::is_tick_begin_at(l, kk) by {
          if kk == len1 + 3 {} else if kk == len1 + 4 {} else { assert(kk == len1 + 5); }
        }
      }
    }
  }
  let dt = crate::executor::invariants::tick_has_drain_task_wake::tick_has_drain_task_wake();
  assert forall |i: int| #[trigger] (dt.acceptance)(l, i) implies (dt.validity)(l, i) by {
    if i < len1 {
      assert(l[i] == l1[i]);
      assert((dt.acceptance)(l1, i));
      assert((dt.validity)(l1, i));
      let p0 = choose |p0: int| 0 <= p0 < i && el::is_drain_task_wake_at(l1, p0) &&
        (forall |kk: int| p0 < kk < i ==> !#[trigger] el::is_tick_begin_at(l1, kk));
      assert(l[p0] == l1[p0]);
      assert(el::is_drain_task_wake_at(l, p0));
      assert forall |kk: int| p0 < kk < i implies !#[trigger] el::is_tick_begin_at(l, kk) by {
        assert(!el::is_tick_begin_at(l1, kk));
        assert(l[kk] == l1[kk]);
      }
    } else {
      let off = i - len1;
      if off == 0 {} else if off == 1 {} else if off == 2 {} else if off == 3 {}
      else if off == 4 {} else if off == 5 {} else {
        assert(off == 6);
        assert(el::is_drain_task_wake_at(l, len1 + 3));
        assert forall |kk: int| len1 + 3 < kk < i implies !#[trigger] el::is_tick_begin_at(l, kk) by {
          if kk == len1 + 4 {} else { assert(kk == len1 + 5); }
        }
      }
    }
  }
}

#[verifier::rlimit(50)]
proof fn exec_append_poll_safety(l1: el::Log)
  requires
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::fifo_task_selection::fifo_task_selection(), l1),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::valid_task_polling::valid_task_polling(), l1),
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::fifo_task_selection::fifo_task_selection(), l1 + bidle_tick()),
    crate::framework::action_safety::action_safety_satisfied(
      crate::executor::invariants::valid_task_polling::valid_task_polling(), l1 + bidle_tick()),
{
  let l = l1 + bidle_tick();
  let len1 = l1.len() as int;
  bidle_tick_idx();
  assert(el::is_prefix_of(l1, l)) by { assert(l1 =~= l.subrange(0, len1)); }

  let pf = crate::executor::invariants::fifo_task_selection::fifo_task_selection();
  assert forall |i: int| #[trigger] (pf.acceptance)(l, i) implies (pf.validity)(l, i) by {
    if i < len1 {
      assert(l[i] == l1[i]);
      assert((pf.acceptance)(l1, i));
      assert((pf.validity)(l1, i));
      crate::executor::proof::prefix_monotonicity::fifo_queue_at_prefix_equals(l1, l, i);
    } else {
      let off = i - len1;
      assert(l[i] == bidle_tick()[off]);
      if off == 0 {} else if off == 1 {} else if off == 2 {} else if off == 3 {}
      else if off == 4 {} else if off == 5 {} else { assert(off == 6); }
    }
  }
  let pv = crate::executor::invariants::valid_task_polling::valid_task_polling();
  assert forall |i: int| #[trigger] (pv.acceptance)(l, i) implies (pv.validity)(l, i) by {
    use crate::executor::invariants::valid_task_polling::*;
    if i < len1 {
      assert(l[i] == l1[i]);
      assert((pv.acceptance)(l1, i));
      assert((pv.validity)(l1, i));
      let t = ee::get_poll_task_id(l1[i]);
      assert(tid_was_injected_before(l, i, t) <==> tid_was_injected_before(l1, i, t)) by {
        if tid_was_injected_before(l1, i, t) {
          let j = choose |j: int| #![trigger l1[j]] 0 <= j < i &&
            el::is_pop_injection_at(l1, j) &&
            ee::get_pop_injection_task(l1[j]).is_some() &&
            ee::get_pop_injection_task(l1[j]).unwrap().id == t;
          assert(l[j] == l1[j]);
          assert(el::is_pop_injection_at(l, j));
        }
        if tid_was_injected_before(l, i, t) {
          let j = choose |j: int| #![trigger l[j]] 0 <= j < i &&
            el::is_pop_injection_at(l, j) &&
            ee::get_pop_injection_task(l[j]).is_some() &&
            ee::get_pop_injection_task(l[j]).unwrap().id == t;
          assert(l1[j] == l[j]);
          assert(el::is_pop_injection_at(l1, j));
        }
      }
      assert(tid_returned_ready_before(l, i, t) <==> tid_returned_ready_before(l1, i, t)) by {
        if tid_returned_ready_before(l1, i, t) {
          let j = choose |j: int| #![trigger l1[j]] 0 <= j < i &&
            el::is_poll_task_at(l1, j) &&
            ee::get_poll_task_id(l1[j]) == t &&
            ee::get_poll_result(l1[j]) == crate::executor::spec::types::PollResult::Ready(());
          assert(l[j] == l1[j]);
          assert(el::is_poll_task_at(l, j));
        }
        if tid_returned_ready_before(l, i, t) {
          let j = choose |j: int| #![trigger l[j]] 0 <= j < i &&
            el::is_poll_task_at(l, j) &&
            ee::get_poll_task_id(l[j]) == t &&
            ee::get_poll_result(l[j]) == crate::executor::spec::types::PollResult::Ready(());
          assert(l1[j] == l[j]);
          assert(el::is_poll_task_at(l1, j));
        }
      }
    } else {
      let off = i - len1;
      assert(l[i] == bidle_tick()[off]);
      if off == 0 {} else if off == 1 {} else if off == 2 {} else if off == 3 {}
      else if off == 4 {} else if off == 5 {} else { assert(off == 6); }
    }
  }
}

#[verifier::rlimit(50)]
proof fn exec_append_liveness(l1: el::Log)
  requires
    crate::framework::local_liveness::local_liveness_satisfied(
      crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake(), l1),
    crate::framework::local_liveness::local_liveness_satisfied(
      crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable(), l1),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(l1, l1.len() as int)
      =~= Seq::<TID>::empty(),
  ensures
    crate::framework::local_liveness::local_liveness_satisfied(
      crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake(), l1 + bidle_tick()),
    crate::framework::local_liveness::local_liveness_satisfied(
      crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable(), l1 + bidle_tick()),
{
  let l = l1 + bidle_tick();
  let len1 = l1.len() as int;
  bidle_tick_idx();
  assert(el::is_prefix_of(l1, l)) by { assert(l1 =~= l.subrange(0, len1)); }
  assert(l[len1 + 4] == bidle_tick()[4]);
  assert(l[len1 + 5] == bidle_tick()[5]);

  let pw = crate::executor::invariants::park_drain_reactor_wake::park_drain_reactor_wake();
  assert forall |i: int| #[trigger] (pw.acceptance)(l, i) implies
    exists |j: int| #![trigger (pw.fulfillment)(l, i, j)]
      j > i && (pw.fulfillment)(l, i, j) && (pw.timely)(l, i, j) by {
    if i < len1 {
      assert(l[i] == l1[i]);
      assert((pw.acceptance)(l1, i));
      let j = choose |j: int| #![trigger (pw.fulfillment)(l1, i, j)]
        j > i && (pw.fulfillment)(l1, i, j) && (pw.timely)(l1, i, j);
      assert(l[j] == l1[j]);
      assert(el::is_drain_reactor_wake_at(l, j));
      assert forall |kk: int| i < kk < j implies !#[trigger] el::is_tick_end_at(l, kk) by {
        assert(!el::is_tick_end_at(l1, kk));
        assert(l[kk] == l1[kk]);
      }
      assert(j > i && (pw.fulfillment)(l, i, j) && (pw.timely)(l, i, j));
    } else {
      let off = i - len1;
      assert(l[i] == bidle_tick()[off]);
      if off == 0 {} else if off == 1 {} else if off == 2 {} else if off == 3 {}
      else if off == 5 {} else if off == 6 {} else {
        assert(off == 4);
        assert(el::is_drain_reactor_wake_at(l, len1 + 5));
        assert(len1 + 5 > i && (pw.fulfillment)(l, i, len1 + 5) && (pw.timely)(l, i, len1 + 5));
      }
    }
  }
  let pt = crate::executor::invariants::tick_polls_if_runnable::tick_polls_if_runnable();
  assert forall |i: int| #[trigger] (pt.acceptance)(l, i) implies
    exists |j: int| #![trigger (pt.fulfillment)(l, i, j)]
      j > i && (pt.fulfillment)(l, i, j) && (pt.timely)(l, i, j) by {
    if i < len1 {
      assert(l[i] == l1[i]);
      crate::executor::proof::prefix_monotonicity::fifo_queue_at_prefix_equals(l1, l, i);
      assert((pt.acceptance)(l1, i));
      let j = choose |j: int| #![trigger (pt.fulfillment)(l1, i, j)]
        j > i && (pt.fulfillment)(l1, i, j) && (pt.timely)(l1, i, j);
      assert(l[j] == l1[j]);
      assert(el::is_poll_task_at(l, j));
      assert forall |kk: int| i < kk < j implies !#[trigger] el::is_tick_end_at(l, kk) by {
        assert(!el::is_tick_end_at(l1, kk));
        assert(l[kk] == l1[kk]);
      }
      assert(j > i && (pt.fulfillment)(l, i, j) && (pt.timely)(l, i, j));
    } else {
      let off = i - len1;
      assert(l[i] == bidle_tick()[off]);
      if off == 0 {
        crate::executor::proof::prefix_monotonicity::fifo_queue_at_prefix_equals(l1, l, len1);
        assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i).len() == 0);
        assert(false);
      } else if off == 1 {} else if off == 2 {} else if off == 3 {}
      else if off == 4 {} else if off == 5 {} else { assert(off == 6); }
    }
  }
}

pub proof fn exec_inv_append_idle(l1: el::Log)
  requires
    crate::executor::invariants::executor_inv(l1),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(l1, l1.len() as int)
      =~= Seq::<TID>::empty(),
  ensures
    crate::executor::invariants::executor_inv(l1 + bidle_tick()),
{
  exec_append_tick_reqs(l1);
  exec_append_poll_safety(l1);
  exec_append_liveness(l1);
}

pub proof fn bextexec_inv(tid: TID, k: nat)
  ensures
    crate::executor::invariants::executor_inv(bextexec(tid, k)),
  decreases k
{
  if k == 0 {
    bexec2_exec_inv(tid);
  } else {
    bextexec_inv(tid, (k - 1) as nat);
    bextexec_queue(tid, (k - 1) as nat);
    exec_inv_append_idle(bextexec(tid, (k - 1) as nat));
  }
}

// ============================================================================
// Reactor family: timestamps, timer facts, invariant, progress
// ============================================================================

// GetCurrentTime characterization: base GCTs at 2 (ts 1) and 6 (ts 2); each
// appended cycle adds exactly one GCT with the fresh timestamp 2 + k.
pub proof fn bextreac_gct(k: nat)
  ensures
    crate::composed::spec::assumptions::timestamps_strictly_increasing(bextreac(k)),
    crate::reactor::timestamps_positive(bextreac(k)),
    forall |a: int| #![trigger bextreac(k)[a]]
      0 <= a < bextreac(k).len() && rl::is_get_current_time_at(bextreac(k), a) ==>
      re::get_current_timestamp(bextreac(k)[a]) <= 2 + k,
  decreases k
{
  breac2_idx();
  breac1_idx();
  if k == 0 {
    let l = breac2();
    assert forall |i: int, j: int|
      0 <= i < j < l.len() &&
      rl::is_get_current_time_at(l, i) && rl::is_get_current_time_at(l, j)
      implies re::get_current_timestamp(#[trigger] l[i]) < re::get_current_timestamp(#[trigger] l[j]) by {
      breac2_flags(i);
      breac2_flags(j);
    }
    assert forall |a: int| #![trigger l[a]]
      0 <= a < l.len() && rl::is_get_current_time_at(l, a)
      implies re::get_current_timestamp(l[a]) >= 1 && re::get_current_timestamp(l[a]) <= 2 by {
      breac2_flags(a);
    }
  } else {
    let l1 = bextreac((k - 1) as nat);
    let l = bextreac(k);
    let len1 = l1.len() as int;
    bextreac_gct((k - 1) as nat);
    bextreac_len((k - 1) as nat);
    bextreac_len(k);
    bpark_cycle_idx(2 + k as int);
    assert(l[len1] == bpark_cycle(2 + k as int)[0]);
    assert(l[len1 + 1] == bpark_cycle(2 + k as int)[1]);
    assert(l[len1 + 2] == bpark_cycle(2 + k as int)[2]);
    assert(l[len1 + 3] == bpark_cycle(2 + k as int)[3]);
    // the only appended GCT is at len1 + 1, with timestamp 2 + k
    assert forall |a: int| len1 <= a < l.len() && a != len1 + 1 implies
      !rl::is_get_current_time_at(l, a) by {
      if a == len1 {} else if a == len1 + 2 {} else { assert(a == len1 + 3); }
    }
    assert(rl::is_get_current_time_at(l, len1 + 1));
    assert(re::get_current_timestamp(l[len1 + 1]) == 2 + k);
    assert forall |i: int, j: int|
      0 <= i < j < l.len() &&
      rl::is_get_current_time_at(l, i) && rl::is_get_current_time_at(l, j)
      implies re::get_current_timestamp(#[trigger] l[i]) < re::get_current_timestamp(#[trigger] l[j]) by {
      if j < len1 {
        assert(l[i] == l1[i]);
        assert(l[j] == l1[j]);
        assert(rl::is_get_current_time_at(l1, i));
        assert(rl::is_get_current_time_at(l1, j));
      } else {
        assert(j == len1 + 1);
        if i < len1 {
          assert(l[i] == l1[i]);
          assert(rl::is_get_current_time_at(l1, i));
          assert(re::get_current_timestamp(l1[i]) <= 2 + (k - 1));
        } else {
          assert(i == len1 + 1);
          assert(false);
        }
      }
    }
    assert forall |a: int| #![trigger l[a]]
      0 <= a < l.len() && rl::is_get_current_time_at(l, a)
      implies re::get_current_timestamp(l[a]) >= 1 && re::get_current_timestamp(l[a]) <= 2 + k by {
      if a < len1 {
        assert(l[a] == l1[a]);
        assert(rl::is_get_current_time_at(l1, a));
      } else {
        assert(a == len1 + 1);
      }
    }
  }
}

// The registered timer stays active up to its wake at 8 (no retire in (0, 8)).
proof fn bextreac_timer_active(k: nat)
  ensures
    rl::timer_active_at(bextreac(k), 0, 8),
{
  let l = bextreac(k);
  bextreac_flags(k);
  assert forall |m: int| 0 < m < 8 implies !rl::timer_retired_at(l, RID(), m) by {
    if rl::timer_retired_at(l, RID(), m) {
      rl::reveal_timer_retired_implies(l, RID(), m);
      assert(!rl::is_succ_deregister_timer_at(l, m));
      assert(!rl::is_wake_task_at(l, m));
    }
  }
}

// The io/set-waker/ready action-safety families stay vacuous on the extension.
#[verifier::rlimit(50)]
proof fn bextreac_vacuous_as(k: nat)
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_ready_in_park::io_ready_in_park(), bextreac(k)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_waker_validity::io_waker_validity(), bextreac(k)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness(), bextreac(k)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io(), bextreac(k)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle(), bextreac(k)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle(), bextreac(k)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result(), bextreac(k)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result(), bextreac(k)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::set_waker_active_io::set_waker_active_io(), bextreac(k)),
{
  let l = bextreac(k);
  bextreac_flags(k);
  let p2 = crate::reactor::invariants::io_ready_in_park::io_ready_in_park();
  assert(crate::framework::action_safety::action_safety_satisfied(p2, l)) by {
    assert forall |i: int| #[trigger] (p2.acceptance)(l, i) implies (p2.validity)(l, i) by {
      assert(!rl::is_io_event_ready_at(l, i));
    } }
  let p4 = crate::reactor::invariants::io_waker_validity::io_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p4, l)) by {
    assert forall |i: int| #[trigger] (p4.acceptance)(l, i) implies (p4.validity)(l, i) by {
    } }
  let p6 = crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p6, l)) by {
    assert forall |i: int| #[trigger] (p6.acceptance)(l, i) implies (p6.validity)(l, i) by {
      assert(!rl::io_syscall_registered_at(l, i));
    } }
  let p8 = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p8, l)) by {
    assert forall |i: int| #[trigger] (p8.acceptance)(l, i) implies (p8.validity)(l, i) by {
      assert(!rl::io_syscall_registered_at(l, i));
    } }
  let p9 = crate::reactor::invariants::register_io_in_cycle::register_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p9, l)) by {
    assert forall |i: int| #[trigger] (p9.acceptance)(l, i) implies (p9.validity)(l, i) by {
      assert(!rl::io_syscall_register_at(l, i));
    } }
  let p10 = crate::reactor::invariants::deregister_io_in_cycle::deregister_io_in_cycle();
  assert(crate::framework::action_safety::action_safety_satisfied(p10, l)) by {
    assert forall |i: int| #[trigger] (p10.acceptance)(l, i) implies (p10.validity)(l, i) by {
      assert(!rl::io_syscall_deregistered_at(l, i));
    } }
  let p11 = crate::reactor::invariants::inbound_register_io_result::inbound_register_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p11, l)) by {
    assert forall |i: int| #[trigger] (p11.acceptance)(l, i) implies (p11.validity)(l, i) by {
      assert(!crate::reactor::invariants::inbound_register_io_result::is_inbound_register_io_end_at(l, i));
    } }
  let p12 = crate::reactor::invariants::inbound_deregister_io_result::inbound_deregister_io_result();
  assert(crate::framework::action_safety::action_safety_satisfied(p12, l)) by {
    assert forall |i: int| #[trigger] (p12.acceptance)(l, i) implies (p12.validity)(l, i) by {
      assert(!crate::reactor::invariants::inbound_deregister_io_result::is_inbound_deregister_io_end_at(l, i));
    } }
  let p14 = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert(crate::framework::action_safety::action_safety_satisfied(p14, l)) by {
    assert forall |i: int| #[trigger] (p14.acceptance)(l, i) implies (p14.validity)(l, i) by {
      assert(!rl::is_succ_set_waker_at(l, i));
    } }
}

// park_has_timestamp + park_poll_once on the extension: old park ends transfer
// from the previous state's reactor_inv; the appended empty cycle's park end is
// checked directly (GCT at len1+1, exactly one PollEvents at len1+2).
#[verifier::rlimit(100)]
proof fn bextreac_park_props(k: nat)
  requires
    k >= 1,
    crate::reactor::invariants::reactor_inv(bextreac((k - 1) as nat)),
  ensures
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::park_has_timestamp::park_has_timestamp(), bextreac(k)),
    crate::framework::action_safety::action_safety_satisfied(
      crate::reactor::invariants::park_poll_once::park_poll_once(), bextreac(k)),
{
  let l1 = bextreac((k - 1) as nat);
  let l = bextreac(k);
  let len1 = l1.len() as int;
  bextreac_len((k - 1) as nat);
  bextreac_len(k);
  bpark_cycle_idx(2 + k as int);
  assert(rl::is_prefix_of(l1, l)) by { assert(l1 =~= l.subrange(0, len1)); }
  assert(l[len1] == bpark_cycle(2 + k as int)[0]);
  assert(l[len1 + 1] == bpark_cycle(2 + k as int)[1]);
  assert(l[len1 + 2] == bpark_cycle(2 + k as int)[2]);
  assert(l[len1 + 3] == bpark_cycle(2 + k as int)[3]);
  // park anatomy of the appended cycle
  assert(rl::current_park_start(l, len1 + 1) == len1);
  assert(rl::current_park_start(l, len1 + 2) == len1);
  assert(rl::current_park_start(l, len1 + 3) == len1);

  let p_pht = crate::reactor::invariants::park_has_timestamp::park_has_timestamp();
  assert(crate::framework::action_safety::action_safety_satisfied(p_pht, l)) by {
    assert forall |i: int| #[trigger] (p_pht.acceptance)(l, i) implies (p_pht.validity)(l, i) by {
      if 0 <= i < len1 {
        assert(l[i] == l1[i]);
        assert(rl::is_park_end_at(l1, i));
        assert((p_pht.acceptance)(l1, i));
        assert((p_pht.validity)(l1, i));
        cps_prefix(l1, l, i);
        let ps = rl::current_park_start(l1, i);
        let j = choose |j: int| #![trigger l1[j]]
          ps < j < i && rl::is_get_current_time_at(l1, j);
        assert(l[j] == l1[j]);
        assert(rl::is_get_current_time_at(l, j));
        assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, i));
      } else if len1 <= i {
        if i == len1 {} else if i == len1 + 1 {} else if i == len1 + 2 {} else {
          assert(i == len1 + 3);
          assert(rl::is_get_current_time_at(l, len1 + 1));
          assert(crate::reactor::invariants::park_has_timestamp::has_get_current_time_in_park(l, i));
        }
      }
    }
  }
  let p_ppo = crate::reactor::invariants::park_poll_once::park_poll_once();
  assert(crate::framework::action_safety::action_safety_satisfied(p_ppo, l)) by {
    assert forall |i: int| #[trigger] (p_ppo.acceptance)(l, i) implies (p_ppo.validity)(l, i) by {
      use crate::reactor::invariants::park_poll_once::count_poll_events_in_range;
      if 0 <= i < len1 {
        assert(l[i] == l1[i]);
        assert(rl::is_park_end_at(l1, i));
        assert((p_ppo.acceptance)(l1, i));
        assert((p_ppo.validity)(l1, i));
        cps_prefix(l1, l, i);
        let ps = rl::current_park_start(l1, i);
        assert(0 <= ps <= i) by { cps_bounds(l1, i); }
        cper_prefix(l1, l, ps, i);
        assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, i));
      } else if len1 <= i {
        if i == len1 {} else if i == len1 + 1 {} else if i == len1 + 2 {} else {
          assert(i == len1 + 3);
          assert(count_poll_events_in_range(l, len1 + 3, len1 + 3) == 0);
          assert(count_poll_events_in_range(l, len1 + 2, len1 + 3) == 1);
          assert(count_poll_events_in_range(l, len1 + 1, len1 + 3) == 1);
          assert(count_poll_events_in_range(l, len1, len1 + 3) == 1);
          assert(crate::reactor::invariants::park_poll_once::has_exactly_one_poll_events_in_park(l, i));
        }
      }
    }
  }
}

// current_park_start is a valid position below i (when non-negative).
proof fn cps_bounds(l: rl::Log, i: int)
  requires
    0 <= i,
  ensures
    rl::current_park_start(l, i) <= i,
    rl::current_park_start(l, i) >= -1,
  decreases i
{
  if i > 0 {
    cps_bounds(l, i - 1);
  }
}

pub proof fn bextreac_reac_inv(k: nat)
  ensures
    crate::reactor::invariants::reactor_inv(bextreac(k)),
  decreases k
{
  if k == 0 {
    breac2_reac_inv();
    return;
  }
  bextreac_reac_inv((k - 1) as nat);
  let l = bextreac(k);
  bextreac_flags(k);
  bextreac_park_props(k);
  bextreac_vacuous_as(k);
  bextreac_timer_active(k);

  // timer_deadline_future @0: deadline 2 > max_timestamp_up_to(l, 0) == 0.
  let p_tdf = crate::reactor::invariants::timer_deadline_future::timer_deadline_future();
  assert(crate::framework::action_safety::action_safety_satisfied(p_tdf, l)) by {
    assert forall |i: int| #[trigger] (p_tdf.acceptance)(l, i) implies (p_tdf.validity)(l, i) by {
      assert(i == 0);
      assert(rl::max_timestamp_up_to(l, 0) == 0);
    }
  }
  // timer_reg_uniqueness @0: no prior registration (empty prefix).
  let p_tru = crate::reactor::invariants::timer_reg_uniqueness::timer_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(p_tru, l)) by {
    assert forall |i: int| #[trigger] (p_tru.acceptance)(l, i) implies (p_tru.validity)(l, i) by {
      assert(i == 0);
      crate::reactor::invariants::timer_reg_uniqueness::intro_no_prior_timer_registration(l, RID(), 0);
    }
  }
  // timer_io_disjoint_at_timer @0.
  let p_tid = crate::reactor::invariants::timer_io_disjoint::timer_io_disjoint_at_timer();
  assert(crate::framework::action_safety::action_safety_satisfied(p_tid, l)) by {
    assert forall |i: int| #[trigger] (p_tid.acceptance)(l, i) implies (p_tid.validity)(l, i) by {
      assert(i == 0);
      crate::reactor::invariants::timer_io_disjoint::intro_no_io_syscall_registration_with_rid(l, RID(), 0);
    }
  }
  // timer_waker_validity @8.
  let p_twv = crate::reactor::invariants::timer_waker_validity::timer_waker_validity();
  assert(crate::framework::action_safety::action_safety_satisfied(p_twv, l)) by {
    assert forall |i: int| #[trigger] (p_twv.acceptance)(l, i) implies (p_twv.validity)(l, i) by {
      assert(i == 8);
      assert(0 <= 0 < 8 && rl::is_succ_register_timer_at(l, 0) &&
        re::get_register_timer_rid(l[0]) == re::get_wake_task_source_rid(l[8]) &&
        re::get_register_timer_waker(l[0]) == re::get_wake_task_waker(l[8]) &&
        rl::timer_active_at(l, 0, 8));
    }
  }
  // wake_has_registration @8.
  let p_whr = crate::reactor::invariants::wake_has_registration::wake_has_registration();
  assert(crate::framework::action_safety::action_safety_satisfied(p_whr, l)) by {
    assert forall |i: int| #[trigger] (p_whr.acceptance)(l, i) implies (p_whr.validity)(l, i) by {
      assert(i == 8);
      assert(0 <= 0 < 8 && rl::is_succ_register_timer_at(l, 0) &&
        re::get_register_timer_rid(l[0]) == re::get_wake_task_source_rid(l[8]));
    }
  }
  // wake_on_expired: acceptance false at 0 — the wake at 8 retires the window.
  let q1 = crate::reactor::invariants::wake_on_expired::wake_on_expired();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q1, l)) by {
    assert forall |i: int| #[trigger] (q1.acceptance)(l, i) implies
      exists |j: int| #![trigger (q1.fulfillment)(l, i, j)]
        j > i && (q1.fulfillment)(l, i, j) && (q1.timely)(l, i, j) by {
      assert(i == 0);
      assert(rl::is_wake_task_at(l, 8) &&
        re::get_wake_task_source_rid(l[8]) == re::get_register_timer_rid(l[0]));
      assert(!crate::reactor::invariants::wake_on_expired::timer_awaiting_wake(l, 0));
    }
  }
  let q2 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_readable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q2, l)) by {
    assert forall |i: int| #[trigger] (q2.acceptance)(l, i) implies
      exists |j: int| #![trigger (q2.fulfillment)(l, i, j)]
        j > i && (q2.fulfillment)(l, i, j) && (q2.timely)(l, i, j) by {
      assert(!rl::is_io_event_ready_at(l, i));
    }
  }
  let q3 = crate::reactor::invariants::wake_on_io_ready::wake_on_io_ready_writable();
  assert(crate::framework::local_liveness::local_liveness_satisfied(q3, l)) by {
    assert forall |i: int| #[trigger] (q3.acceptance)(l, i) implies
      exists |j: int| #![trigger (q3.fulfillment)(l, i, j)]
        j > i && (q3.fulfillment)(l, i, j) && (q3.timely)(l, i, j) by {
      assert(!rl::is_io_event_ready_at(l, i));
    }
  }
}

pub proof fn bextreac_progress(k: nat)
  requires
    k >= 1,
  ensures
    crate::reactor::reactor_progress(bextreac((k - 1) as nat), bextreac(k)),
{
  let l1 = bextreac((k - 1) as nat);
  let l = bextreac(k);
  let len1 = l1.len() as int;
  bextreac_len((k - 1) as nat);
  bextreac_len(k);
  bextreac_reac_inv(k);
  bpark_cycle_idx(2 + k as int);
  assert(l1 =~= l.subrange(0, len1));
  assert(l[len1] == bpark_cycle(2 + k as int)[0]);
  assert(l[len1 + 1] == bpark_cycle(2 + k as int)[1]);
  assert(l[len1 + 2] == bpark_cycle(2 + k as int)[2]);
  assert(l[len1 + 3] == bpark_cycle(2 + k as int)[3]);
  assert(crate::reactor::is_complete_park_cycle(l, len1, len1 + 4)) by {
    assert(rl::is_park_begin_at(l, len1));
    assert(rl::is_park_end_at(l, len1 + 3));
    assert forall |kk: int| len1 < kk < len1 + 3 implies
      !#[trigger] rl::is_park_begin_at(l, kk) && !rl::is_park_end_at(l, kk) by {
      if kk == len1 + 1 {} else { assert(kk == len1 + 2); }
    }
  }
  assert(exists |ps: int, pe: int|
    len1 <= ps && ps < pe && pe <= l.len() &&
    crate::reactor::is_complete_park_cycle(l, ps, pe) &&
    (forall |i: int| len1 <= i < ps ==> re::is_inbound_non_park(#[trigger] l[i])) &&
    (forall |i: int| pe <= i < l.len() ==> re::is_inbound_non_park(#[trigger] l[i]))) by {
    assert(crate::reactor::is_complete_park_cycle(l, len1, len1 + 4));
    assert(l.len() == len1 + 4);
  }
}

pub proof fn bextexec_progress(tid: TID, k: nat)
  requires
    k >= 1,
  ensures
    crate::executor::executor_progress(bextexec(tid, (k - 1) as nat), bextexec(tid, k)),
{
  let l1 = bextexec(tid, (k - 1) as nat);
  let l = bextexec(tid, k);
  let len1 = l1.len() as int;
  bextexec_inv(tid, k);
  bidle_tick_idx();
  assert(l1 =~= l.subrange(0, len1));
  assert(l[len1] == bidle_tick()[0]);
  assert(l[len1 + 1] == bidle_tick()[1]);
  assert(l[len1 + 2] == bidle_tick()[2]);
  assert(l[len1 + 3] == bidle_tick()[3]);
  assert(l[len1 + 4] == bidle_tick()[4]);
  assert(l[len1 + 5] == bidle_tick()[5]);
  assert(l[len1 + 6] == bidle_tick()[6]);
  assert(crate::executor::is_complete_tick_cycle(l, len1, l.len() as int)) by {
    assert(el::is_tick_begin_at(l, len1));
    assert(el::is_tick_end_at(l, l.len() - 1));
    assert forall |kk: int| len1 < kk < l.len() - 1 implies
      !#[trigger] el::is_tick_begin_at(l, kk) && !el::is_tick_end_at(l, kk) by {
      if kk == len1 + 1 {} else if kk == len1 + 2 {} else if kk == len1 + 3 {}
      else if kk == len1 + 4 {} else { assert(kk == len1 + 5); }
    }
  }
}

// ============================================================================
// Composed layer: alignment state/step, composed_progress, env_N
// ============================================================================

// Action-mediation at any bext state: the single reactor op (btask_ready[1])
// matches the single task-initiated reactor event (register @0).
#[verifier::rlimit(100)]
proof fn bext_am_state(tid: TID, k: nat)
  ensures
    crate::composed::spec::alignment::action_mediation_state(bext(tid, k)),
{
  let s = bext(tid, k);
  let lr = bextreac(k);
  bextreac_flags(k);
  breac2_idx();
  btask_idx();
  btask_op_facts();
  breg_matches(tid);
  assert(lr[0] == breac2()[0]);
  assert(s.task_logs[tid] == btask_ready());
  assert(succ_reactor_event_matches_task_operation(s.reactor_log[0], s.task_logs[tid][1]));
  // only index 0 is a task-initiated reactor event
  assert forall |j: int| #![trigger s.reactor_log[j]]
    0 <= j < s.reactor_log.len() && j != 0 implies
    !is_task_initiated_reactor_event(s.reactor_log[j]) by {
    assert(!rl::is_succ_register_timer_at(lr, j));
    assert(!rl::is_deregister_timer_at(lr, j));
    assert(!rl::io_syscall_registered_at(lr, j));
    assert(!rl::io_syscall_deregistered_at(lr, j));
    assert(!rl::is_succ_set_waker_at(lr, j));
  }
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
  assert(reactor_registration_to_task_exists(s)) by {
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() &&
      (re::is_succ_register_timer(s.reactor_log[j]) || re::is_succ_io_syscall_register(s.reactor_log[j]))
      implies exists |t2: TaskId, ti: int| s.task_logs.contains_key(t2) &&
        0 <= ti < s.task_logs[t2].len() &&
        succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[t2][ti]) by {
      assert(!rl::io_syscall_registered_at(lr, j));
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
  crate::composed::proof::inhabitation_goal_wake::monotonic_alignment_holds_single(s, tid);
  assert(succ_deregister_by_owner(s)) by {
    reveal(succ_deregister_by_owner);
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() implies
      !re::is_succ_deregister_timer(s.reactor_log[j]) by {
      assert(!rl::is_succ_deregister_timer_at(lr, j));
    }
  }
  assert(deregister_matches_own_registration(s)) by {
    reveal(deregister_matches_own_registration);
  }
  assert(deregister_io_matches_own_registration(s)) by {
    reveal(deregister_io_matches_own_registration);
  }
  assert(succ_deregister_io_by_owner(s)) by {
    reveal(succ_deregister_io_by_owner);
    assert forall |j: int| #![trigger s.reactor_log[j]]
      0 <= j < s.reactor_log.len() implies
      !re::is_io_syscall_deregister(s.reactor_log[j]) by {
      assert(!rl::io_syscall_deregistered_at(lr, j));
    }
  }
}

proof fn bext_obs_state(tid: TID, k: nat)
  ensures
    crate::composed::spec::alignment::observation_consistency_state(bext(tid, k)),
{
  let s = bext(tid, k);
  bext_poll_facts(tid, k);
  assert(polled_task_has_log_inv(s)) by {
    assert forall |t2: TaskId| el::has_poll_for_id(s.executor_log, t2)
      implies s.task_logs.contains_key(t2) by {
      if t2 != tid {
        assert(!el::has_poll_for_id(s.executor_log, t2));
      }
    }
  }
  assert(pending_poll_inv(s)) by {
    assert forall |t2: TaskId| #![trigger s.task_logs[t2]]
      s.task_logs.contains_key(t2) && el::last_poll_is_pending(s.executor_log, t2)
      implies task_log_ends_with_pending(s.task_logs[t2]) by {
      assert(t2 == tid);
      assert(!el::last_poll_is_pending(s.executor_log, tid));
    }
  }
}

#[verifier::rlimit(100)]
proof fn bext_cross(tid: TID, k: nat)
  ensures
    cross_module_alignment(bext(tid, k), bext(tid, (k + 1) as nat)),
{
  reveal(cross_module_alignment);
  let s = bext(tid, k);
  let s2 = bext(tid, (k + 1) as nat);
  let le1 = bextexec(tid, k);
  let le2 = bextexec(tid, (k + 1) as nat);
  let lr1 = bextreac(k);
  let lr2 = bextreac((k + 1) as nat);
  let elen1 = le1.len() as int;
  let rlen1 = lr1.len() as int;
  bextexec_flags(tid, k);
  bextexec_flags(tid, (k + 1) as nat);
  bextreac_flags(k);
  bextreac_flags((k + 1) as nat);
  bidle_tick_idx();
  bpark_cycle_idx(2 + (k + 1) as int);

  bext_am_state(tid, (k + 1) as nat);
  bext_obs_state(tid, (k + 1) as nat);

  // A_step: no new task ops (task log unchanged), no new task-initiated
  // reactor events (the appended cycle is Park/GCT/PollEvents).
  assert forall |t2: TaskId, i: int|
    !#[trigger] is_new_task_operation(s, s2, t2, i) by {
    if s2.task_logs.contains_key(t2) {
      assert(t2 == tid);
      assert(s.task_logs.contains_key(tid));
      assert(s.task_logs[tid].len() == s2.task_logs[tid].len());
    }
  }
  assert forall |j: int| #![trigger s2.reactor_log[j]]
    rlen1 <= j < s2.reactor_log.len() implies
    !is_task_initiated_reactor_event(s2.reactor_log[j]) by {
    assert(!rl::is_succ_register_timer_at(lr2, j));
    assert(!rl::is_deregister_timer_at(lr2, j));
    assert(!rl::io_syscall_registered_at(lr2, j));
    assert(!rl::io_syscall_deregistered_at(lr2, j));
    assert(!rl::is_succ_set_waker_at(lr2, j));
    assert(j != 0);
  }
  assert(action_mediation_step(s, s2)) by {
    assert(new_operation_alignment(s, s2));
    assert(new_operation_uniqueness(s, s2));
    assert(new_op_matches_only_new_reactor(s, s2));
    assert(reactor_outbound_has_task_operation(s, s2));
    assert(new_reactor_event_has_new_op(s, s2));
  }

  // B_step: no new polls in the appended idle tick.
  assert forall |i: int| #![trigger s2.executor_log[i]]
    elen1 <= i < s2.executor_log.len() implies
    !el::is_poll_task_at(le2, i) by {
    assert(elen1 >= 16);
    assert(!el::is_poll_task_at(le2, i));
  }
  assert(observation_consistency_step(s, s2)) by {
    assert(poll_alignment(s, s2)) by {
      assert forall |t2: TaskId|
        #![trigger s2.task_logs[t2]]
        s2.task_logs.contains_key(t2) implies s.task_logs.contains_key(t2) &&
          s.task_logs[t2].len() == s2.task_logs[t2].len() by {
        assert(t2 == tid);
      }
    }
    assert(pending_poll_alignment(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_pending_for_id_at(s2.executor_log, i, t2) && s2.task_logs.contains_key(t2)
        implies task_log_ends_with_pending(s2.task_logs[t2]) by {
        assert(!el::is_poll_task_at(le2, i));
      }
    }
    assert(new_poll_has_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2)
        implies s2.task_logs.contains_key(t2) by {
        assert(!el::is_poll_task_at(le2, i));
      }
    }
    assert(new_poll_changes_task_log(s, s2)) by {
      assert forall |t2: TaskId, i: int| #![trigger s2.executor_log[i], s2.task_logs[t2]]
        s.executor_log.len() as int <= i < s2.executor_log.len() &&
        el::is_poll_task_for_id_at(s2.executor_log, i, t2) && s.task_logs.contains_key(t2)
        implies s.task_logs[t2].len() < s2.task_logs[t2].len() by {
        assert(!el::is_poll_task_at(le2, i));
      }
    }
  }

  // C_step: one executor Park <-> one reactor park cycle in the appended step.
  assert(le2[elen1] == bidle_tick()[0]);
  assert(le2[elen1 + 1] == bidle_tick()[1]);
  assert(le2[elen1 + 2] == bidle_tick()[2]);
  assert(le2[elen1 + 3] == bidle_tick()[3]);
  assert(le2[elen1 + 4] == bidle_tick()[4]);
  assert(le2[elen1 + 5] == bidle_tick()[5]);
  assert(le2[elen1 + 6] == bidle_tick()[6]);
  assert(lr2[rlen1] == bpark_cycle(2 + (k + 1) as int)[0]);
  assert(lr2[rlen1 + 1] == bpark_cycle(2 + (k + 1) as int)[1]);
  assert(lr2[rlen1 + 2] == bpark_cycle(2 + (k + 1) as int)[2]);
  assert(lr2[rlen1 + 3] == bpark_cycle(2 + (k + 1) as int)[3]);
  assert(count_park_events_in(le2, elen1 + 7, elen1 + 7) == 0);
  assert(count_park_events_in(le2, elen1 + 6, elen1 + 7) == 0);
  assert(count_park_events_in(le2, elen1 + 5, elen1 + 7) == 0);
  assert(count_park_events_in(le2, elen1 + 4, elen1 + 7) == 1);
  assert(count_park_events_in(le2, elen1 + 3, elen1 + 7) == 1);
  assert(count_park_events_in(le2, elen1 + 2, elen1 + 7) == 1);
  assert(count_park_events_in(le2, elen1 + 1, elen1 + 7) == 1);
  assert(count_park_events_in(le2, elen1, elen1 + 7) == 1);
  assert(count_park_cycles_in(lr2, rlen1 + 4, rlen1 + 4) == 0);
  assert(count_park_cycles_in(lr2, rlen1 + 3, rlen1 + 4) == 1);
  assert(count_park_cycles_in(lr2, rlen1 + 2, rlen1 + 4) == 1);
  assert(count_park_cycles_in(lr2, rlen1 + 1, rlen1 + 4) == 1);
  assert(count_park_cycles_in(lr2, rlen1, rlen1 + 4) == 1);
  assert(park_alignment(s, s2));
}

#[verifier::rlimit(50)]
proof fn bext_extension(tid: TID, k: nat)
  ensures
    is_extension_of(bext(tid, k), bext(tid, (k + 1) as nat)),
{
  let s = bext(tid, k);
  let s2 = bext(tid, (k + 1) as nat);
  bextexec_len(tid, k);
  bextreac_len(k);
  assert(el::is_prefix_of(s.executor_log, s2.executor_log)) by {
    assert(s.executor_log =~= s2.executor_log.subrange(0, s.executor_log.len() as int));
  }
  assert(rl::is_prefix_of(s.reactor_log, s2.reactor_log)) by {
    assert(s.reactor_log =~= s2.reactor_log.subrange(0, s.reactor_log.len() as int));
  }
  assert forall |t2: TaskId| s.task_logs.contains_key(t2) implies
    s2.task_logs.contains_key(t2) &&
    crate::composed::spec::state::is_task_log_prefix(s.task_logs[t2], s2.task_logs[t2]) by {
    assert(t2 == tid);
    assert(s.task_logs[t2] == s2.task_logs[t2]);
  }
}

// All three modeled wake queues are empty at every bext state (tid's last poll
// is Ready and no other task has a log), so the drain-step clauses are vacuous.
#[verifier::rlimit(50)]
proof fn bext_drain_steps(tid: TID, k: nat)
  ensures
    crate::composed::spec::wake_queues::deferred_drain_step(bext(tid, k), bext(tid, (k + 1) as nat)),
    crate::composed::spec::wake_queues::reactor_wake_drain_step(bext(tid, k), bext(tid, (k + 1) as nat)),
    crate::composed::spec::wake_queues::taskwake_drain_step(bext(tid, k), bext(tid, (k + 1) as nat)),
{
  let s = bext(tid, k);
  let s2 = bext(tid, (k + 1) as nat);
  bext_poll_facts(tid, k);
  assert forall |tid2: TaskId|
    !#[trigger] crate::composed::spec::wake_queues::in_deferred_queue(s, tid2) by {
    if s.task_logs.contains_key(tid2) {
      assert(tid2 == tid);
      assert(!el::last_poll_is_pending(s.executor_log, tid));
    }
  }
  assert(crate::composed::spec::wake_queues::deferred_drain_step(s, s2));
  reveal(crate::composed::spec::wake_queues::reactor_wake_pending);
  assert forall |tid2: TaskId|
    !#[trigger] crate::composed::spec::wake_queues::reactor_wake_pending(s, tid2) by {
    if s.task_logs.contains_key(tid2) {
      assert(tid2 == tid);
      assert(!el::last_poll_is_pending(s.executor_log, tid));
    }
  }
  reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
  assert(crate::composed::spec::wake_queues::reactor_wake_drain_step(s, s2));
  reveal(crate::composed::spec::wake_queues::taskwake_pending);
  assert forall |tid2: TaskId|
    !#[trigger] crate::composed::spec::wake_queues::taskwake_pending(s, tid2) by {
    if s.task_logs.contains_key(tid2) {
      assert(tid2 == tid);
      assert(!el::last_poll_is_pending(s.executor_log, tid));
    }
  }
  reveal(crate::composed::spec::wake_queues::taskwake_drain_step);
  assert(crate::composed::spec::wake_queues::taskwake_drain_step(s, s2));
}

#[verifier::rlimit(50)]
proof fn bext_task_logs_inv(tid: TID, k: nat)
  ensures
    crate::composed::spec::progress::task_logs_preserve_utilities_inv(
      bext(tid, k), bext(tid, (k + 1) as nat)),
    crate::composed::spec::alignment::monotonic_task_reactor_alignment(bext(tid, (k + 1) as nat)),
{
  let s2 = bext(tid, (k + 1) as nat);
  btask_idx();
  btask_utilities_inv();
  assert forall |t2: TaskId| s2.task_logs.contains_key(t2) implies
    crate::utilities::invariants::wakeup_guarantee::utilities_inv(#[trigger] s2.task_logs[t2]) by {
    assert(t2 == tid && s2.task_logs[t2] == btask_ready());
  }
  crate::composed::proof::inhabitation_goal_wake::monotonic_alignment_holds_single(s2, tid);
}

pub proof fn bext_step(tid: TID, k: nat)
  ensures
    composed_progress(bext(tid, k), bext(tid, (k + 1) as nat)),
{
  reveal(composed_progress);
  bext_extension(tid, k);
  bextexec_progress(tid, (k + 1) as nat);
  bextreac_progress((k + 1) as nat);
  bext_cross(tid, k);
  bext_task_logs_inv(tid, k);
  bext_injected(tid, (k + 1) as nat);
  bext_drain_steps(tid, k);
}

#[verifier::rlimit(100)]
pub proof fn bext_env(tid: TID, k: nat)
  requires
    get_max_queue_length(bs1(tid)) >= 1,
    get_max_timer_deadline_gap(bs1(tid), tid) >= 3,
  ensures
    env_N(bext(tid, k), tid, 2nat),
{
  let s = bext(tid, k);
  let le = bextexec(tid, k);
  let lr = bextreac(k);
  bextexec_flags(tid, k);
  bextreac_flags(k);
  bextreac_gct(k);
  bexec2_idx(tid);
  bexec1_idx(tid);
  breac2_idx();
  btask_idx();
  bext_poll_facts(tid, k);
  bext_injected(tid, k);
  bext_tid_unique(tid, k);
  bextexec_queue(tid, k);
  assert(get_max_queue_length(s) == get_max_queue_length(bs1(tid)));
  assert(get_max_timer_deadline_gap(s, tid) == get_max_timer_deadline_gap(bs1(tid), tid));

  assert(timer_deadline_gap_bounded(s, tid)) by {
    reveal(timer_deadline_gap_bounded);
    assert(lr[0] == breac2()[0]);
    assert(rl::max_timestamp_up_to(lr, 1) == 0) by {
      breac2_flags(0);
      assert(!rl::is_get_current_time_at(lr, 0));
      assert(rl::max_timestamp_up_to(lr, 0) == 0);
    }
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < lr.len() && rl::is_succ_register_timer_at(lr, reg_idx) &&
      crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(
        lr, reg_idx, lr.len() as int)
      implies crate::reactor::proof::round_extension::compute_bound(
        re::get_register_timer_deadline(lr[reg_idx]),
        rl::max_timestamp_up_to(lr, (reg_idx + 1) as int))
        <= get_max_timer_deadline_gap(s, tid) by {
      assert(reg_idx == 0);
      assert(re::get_register_timer_deadline(lr[0]) == 2);
    }
  }
  assert(timer_resources_remain_active(s)) by {
    assert forall |reg_idx: int| #![trigger s.reactor_log[reg_idx]]
      0 <= reg_idx < lr.len() && rl::is_succ_register_timer_at(lr, reg_idx)
      implies crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(
        lr, reg_idx, lr.len() as int) by {
      assert(reg_idx == 0);
      assert forall |j: int| 0 < j < lr.len() implies
        !(rl::is_succ_deregister_timer_at(lr, j) &&
          re::get_deregister_timer_rid(#[trigger] lr[j]) == re::get_register_timer_rid(lr[0])) by {
        assert(!rl::is_succ_deregister_timer_at(lr, j));
      }
    }
  }
  assert(queue_length_bounded(s)) by {
    assert forall |i: int|
      #![trigger crate::executor::invariants::fifo_task_selection::fifo_queue_at(s.executor_log, i)]
      0 <= i <= s.executor_log.len() implies
      crate::executor::invariants::fifo_task_selection::fifo_queue_at(s.executor_log, i).len()
        <= get_max_queue_length(s) by {
      assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(le, i).len() <= 1);
    }
  }
  assert(contract_io_assumption_here(s)) by {
    assert forall |rid: ResourceIdView| #![trigger io_assumption_here(s.reactor_log, rid)]
      io_assumption_here(s.reactor_log, rid) by {
      no_sw_find_last_none(lr, rid, lr.len() as int);
      assert(crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(lr, rid));
    }
  }
  assert(env_holds_at_state_core(s, tid));
  assert(end_to_end_env(s, tid));
  assert(bounded_poll_count_here_with_bound(s, tid, 2nat)) by {
    assert(el::is_poll_ready_for_id_at(le, 14, tid));
    assert(crate::composed::spec::assumptions::task_polled_to_ready(le, tid));
  }
  assert forall |rid: ResourceIdView|
    #[trigger] io_ready_forward_here(s.reactor_log, rid,
      crate::composed::spec::assumptions::get_io_ready_bound(s, tid)) by {
    no_sw_find_last_none(lr, rid, lr.len() as int);
  }
  taskwake_arrival_within_vacuous(s, tid, 2nat);
}

// The env_N-good trace: arrival_witness --(k+2 steps)--> bext(tid, k).
pub proof fn bext_reachable(tid: TaskId, k: nat)
  requires
    get_max_queue_length(bs1(tid)) >= 1,
    get_max_timer_deadline_gap(bs1(tid), tid) >= 3,
  ensures
    ete_reachable_N(arrival_witness(tid), bext(tid, k), (k + 2) as nat, 2nat, tid),
  decreases k
{
  if k == 0 {
    b_domain_inhabited(tid);
    assert(bextexec(tid, 0) == bexec2(tid));
    assert(bextreac(0) == breac2());
    assert(bext(tid, 0) == bs2(tid));
  } else {
    bext_reachable(tid, (k - 1) as nat);
    bext_step(tid, (k - 1) as nat);
    bext_env(tid, k);
    let progress = crate::composed::spec::progress::composed_module_spec().progress;
    let env = |x: ComposedState, t2: TaskId| env_N(x, t2, 2nat);
    assert(crate::framework::module_spec::env_progress_n(
      progress, arrival_witness(tid), bext(tid, (k - 1) as nat), (k + 1) as nat, env, tid));
    assert(((k - 1) as nat + 1) as nat == k);
    assert(bext(tid, ((k - 1) as nat + 1) as nat) == bext(tid, k));
    assert((progress)(bext(tid, (k - 1) as nat), bext(tid, k)));
    assert(env(bext(tid, k), tid));
    crate::framework::module_spec::env_progress_n_step(
      progress, arrival_witness(tid), bext(tid, (k - 1) as nat), bext(tid, k),
      (k + 1) as nat, env, tid);
    assert(ete_reachable_N(arrival_witness(tid), bext(tid, k), (k + 2) as nat, 2nat, tid));
  }
}

// ============================================================================
// F-A budget-gap closure: the response-filter domain is inhabited at EVERY
// budget n >= 2 — in particular at the proof-instantiated n* = chunk+cap·chunk
// — by the bs2-plus-idle-stuttering witness family. Same env-constant
// conditionality as b_domain_inhabited (the n = 2 base witness).
// ============================================================================
pub proof fn b_domain_inhabited_at_any_n(tid: TaskId, n: nat)
  requires
    n >= 2,
    get_max_queue_length(bs1(tid)) >= 1,
    get_max_timer_deadline_gap(bs1(tid), tid) >= 3,
  ensures
    exists |l2: ComposedState|
      #[trigger] ete_reachable_N(arrival_witness(tid), l2, n, 2nat, tid) &&
      crate::composed::spec::contract::end_to_end_response(l2, tid),
{
  let k = (n - 2) as nat;
  bext_reachable(tid, k);
  bext_poll_facts(tid, k);
  let w = bext(tid, k);
  assert((k + 2) as nat == n);
  assert(crate::composed::spec::contract::end_to_end_response(w, tid)) by {
    assert(el::is_poll_ready_for_id_at(w.executor_log, 14, tid));
  }
  assert(ete_reachable_N(arrival_witness(tid), w, n, 2nat, tid) &&
    crate::composed::spec::contract::end_to_end_response(w, tid));
}

}
