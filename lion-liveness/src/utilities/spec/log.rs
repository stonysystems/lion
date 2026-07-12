use vstd::prelude::*;
use crate::utilities::spec::events::*;

verus! {

pub type Log = Seq<UtilityEvent>;

pub open spec fn find_last_poll_begin(l: Log, i: int) -> int
  recommends 0 <= i < l.len()
  decreases i + 1 when i >= -1
{
  if i < 0 {
    -1
  } else if i < l.len() && is_poll_begin(l[i]) {
    i
  } else {
    find_last_poll_begin(l, i - 1)
  }
}

pub open spec fn current_poll_start(l: Log, i: int) -> int {
  find_last_poll_begin(l, i)
}

pub open spec fn in_current_poll_cycle(l: Log, action_idx: int, i: int) -> bool {
  let poll_start = current_poll_start(l, i);
  poll_start >= 0 && action_idx >= poll_start && action_idx <= i
}

pub open spec fn is_timer_registered_before(l: Log, rid: RID, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    0 <= j < i &&
    is_register_timer(l[j]) &&
    get_resource_id(l[j]) == Some(rid)
}

// NOTE (semantics): deregistration is counted by is_deregister_timer — ANY
// result, including failed deregisters. The modeling choice is "a deregister
// call consumes the linear handle regardless of result". (The reactor-side
// alignment uses is_succ_deregister_* — asymmetric on purpose. The event
// vocabulary is also asymmetric: DeregisterTimer carries a `result: bool`
// while DeregisterIo carries none — see utilities/spec/events.rs.)
pub open spec fn is_timer_deregistered_before(l: Log, rid: RID, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    0 <= j < i &&
    is_deregister_timer(l[j]) &&
    get_resource_id(l[j]) == Some(rid)
}

pub open spec fn is_timer_active(l: Log, rid: RID, i: int) -> bool {
  is_timer_registered_before(l, rid, i) &&
  !is_timer_deregistered_before(l, rid, i)
}

pub open spec fn is_io_registered_before(l: Log, rid: RID, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    0 <= j < i &&
    is_register_io(l[j]) &&
    get_resource_id(l[j]) == Some(rid)
}

pub open spec fn is_io_deregistered_before(l: Log, rid: RID, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    0 <= j < i &&
    is_deregister_io(l[j]) &&
    get_resource_id(l[j]) == Some(rid)
}

// IO resource is active at position i if:
// 1. It was registered before i
// 2. No deregister occurred before i (strictly: at positions j < i)
pub open spec fn is_io_active(l: Log, rid: RID, i: int) -> bool {
  is_io_registered_before(l, rid, i) &&
  !is_io_deregistered_before(l, rid, i)
}

// Waker must be set in current poll cycle (not just any time before)
pub open spec fn has_waker_set_in_current_poll(l: Log, rid: RID, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    in_current_poll_cycle(l, j, i) &&
    is_succ_set_waker(l[j]) &&
    get_resource_id(l[j]) == Some(rid)
}

pub open spec fn has_defer_in_current_poll(l: Log, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    in_current_poll_cycle(l, j, i) &&
    is_defer(l[j])
}

pub open spec fn has_pass_waker_in_current_poll(l: Log, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    in_current_poll_cycle(l, j, i) &&
    is_pass_waker(l[j])
}

// A Woken event (the task's waker was invoked by an external task/utility) occurs in
// the task's current poll cycle. The TaskWake-queue arrival growth event
// (wake-routing Phase C) — self-identifying (in tid's OWN task log).
pub open spec fn has_woken_in_current_poll(l: Log, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    in_current_poll_cycle(l, j, i) &&
    is_woken(l[j])
}

// NOTE (boundary): dereg AT the endpoint counts here (k <= end), unlike is_timer_active's strict < i; at call sites the endpoint is a PollEnd so no dereg can occupy it.
pub open spec fn timer_deregistered_after_in_poll(l: Log, rid: RID, reg_idx: int, end: int) -> bool {
  exists |k: int|
    #![trigger l[k]]
    reg_idx < k <= end &&
    is_deregister_timer(l[k]) &&
    get_resource_id(l[k]) == Some(rid)
}

pub open spec fn has_timer_registered_in_current_poll(l: Log, rid: RID, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    in_current_poll_cycle(l, j, i) &&
    is_register_timer(l[j]) &&
    get_resource_id(l[j]) == Some(rid) &&
    !timer_deregistered_after_in_poll(l, rid, j, i)
}

// NOTE (naming): despite the name, no waker condition is checked here (contrast
// has_active_io_with_waker) — a timer registration in Lion always carries its
// waker. Also, only timers registered in the CURRENT poll cycle count: the
// modeling assumption is that a pending future re-registers (or re-arms) its
// timer interest on every poll. A still-armed timer from an earlier poll does
// not count as a wakeup source for wakeup_guarantee.
pub open spec fn has_active_timer_with_waker(l: Log, i: int) -> bool {
  exists |rid: RID|
    #![trigger has_timer_registered_in_current_poll(l, rid, i)]
    has_timer_registered_in_current_poll(l, rid, i)
}

// IO can be registered in previous polls, but waker must be set in current poll
pub open spec fn has_active_io_with_waker(l: Log, i: int) -> bool {
  exists |rid: RID|
    #![trigger is_io_active(l, rid, i)]
    is_io_active(l, rid, i) &&
    has_waker_set_in_current_poll(l, rid, i)
}

pub open spec fn has_active_wakeup_source(l: Log, i: int) -> bool {
  has_active_timer_with_waker(l, i) ||
  has_active_io_with_waker(l, i) ||
  has_defer_in_current_poll(l, i) ||
  has_pass_waker_in_current_poll(l, i)
}

// ============================================================================
// Boundary probes (AUDIT_CHECKLIST §1.2): pin the log-index specs' values on
// concrete tiny logs at the boundary points — empty log, i = 0, i = len-1,
// event AT i vs strictly before i — so an off-by-one regression here becomes
// a verify failure instead of a silently constant-true/false predicate.
// ============================================================================

proof fn probe_empty_log()
  ensures
    current_poll_start(Seq::<UtilityEvent>::empty(), 0) == -1,
    !in_current_poll_cycle(Seq::<UtilityEvent>::empty(), 0, 0),
    !is_timer_registered_before(Seq::<UtilityEvent>::empty(), 7, 0),
    !is_timer_active(Seq::<UtilityEvent>::empty(), 7, 0),
    !is_io_active(Seq::<UtilityEvent>::empty(), 7, 0),
    !has_active_wakeup_source(Seq::<UtilityEvent>::empty(), 0),
{
  let l = Seq::<UtilityEvent>::empty();
  reveal_with_fuel(find_last_poll_begin, 3);
  assert(find_last_poll_begin(l, 0) == -1);
  assert(!has_active_timer_with_waker(l, 0)) by {
    if has_active_timer_with_waker(l, 0) {
      let rid = choose |rid: RID| has_timer_registered_in_current_poll(l, rid, 0);
      assert(false);
    }
  }
  assert(!has_active_io_with_waker(l, 0)) by {
    if has_active_io_with_waker(l, 0) {
      let rid = choose |rid: RID| is_io_active(l, rid, 0) && has_waker_set_in_current_poll(l, rid, 0);
      assert(false);
    }
  }
}

// l = [PollBegin, RegisterTimer{7}, Poll(Pending)]: registration counts only
// STRICTLY before i; poll-cycle membership at i = 0 and i = len-1.
proof fn probe_small_log()
  ensures ({
    let l: Log = seq![
      UtilityEvent::Inbound(InboundCall::Poll { result: None }),
      UtilityEvent::Outbound(OutboundCall::RegisterTimer { resource_id: 7, deadline: 10 }),
      UtilityEvent::Inbound(InboundCall::Poll { result: Some(PollResult::Pending) }),
    ];
    current_poll_start(l, 0) == 0 &&
    current_poll_start(l, 2) == 0 &&
    in_current_poll_cycle(l, 0, 0) &&
    in_current_poll_cycle(l, 1, 2) &&
    !is_timer_registered_before(l, 7, 0) &&
    !is_timer_registered_before(l, 7, 1) &&    // reg AT 1 does not count at 1
    is_timer_registered_before(l, 7, 2) &&
    is_timer_active(l, 7, 2)
  }),
{
  let l: Log = seq![
    UtilityEvent::Inbound(InboundCall::Poll { result: None }),
    UtilityEvent::Outbound(OutboundCall::RegisterTimer { resource_id: 7, deadline: 10 }),
    UtilityEvent::Inbound(InboundCall::Poll { result: Some(PollResult::Pending) }),
  ];
  reveal_with_fuel(find_last_poll_begin, 5);
  assert(is_poll_begin(l[0]));
  assert(find_last_poll_begin(l, 0) == 0);
  assert(!is_poll_begin(l[2]) && !is_poll_begin(l[1]));
  assert(find_last_poll_begin(l, 2) == 0);
  assert(is_register_timer(l[1]) && get_resource_id(l[1]) == Some(7nat));
  assert(is_timer_registered_before(l, 7, 2));
  assert(!is_timer_deregistered_before(l, 7, 2));
}

// Deregistration semantics probes: a FAILED deregister (result: false) still
// deactivates (ANY-result modeling choice documented above), and a dereg AT i
// does not count at i (strict j < i).
proof fn probe_dereg_boundary()
  ensures ({
    let l: Log = seq![
      UtilityEvent::Inbound(InboundCall::Poll { result: None }),
      UtilityEvent::Outbound(OutboundCall::RegisterTimer { resource_id: 7, deadline: 10 }),
      UtilityEvent::Outbound(OutboundCall::DeregisterTimer { resource_id: 7, result: false }),
    ];
    !is_timer_deregistered_before(l, 7, 2) &&   // dereg AT 2 does not count at 2
    is_timer_active(l, 7, 2) &&
    is_timer_deregistered_before(l, 7, 3) &&    // failed dereg still counts
    !is_timer_active(l, 7, 3)
  }),
{
  let l: Log = seq![
    UtilityEvent::Inbound(InboundCall::Poll { result: None }),
    UtilityEvent::Outbound(OutboundCall::RegisterTimer { resource_id: 7, deadline: 10 }),
    UtilityEvent::Outbound(OutboundCall::DeregisterTimer { resource_id: 7, result: false }),
  ];
  assert(is_register_timer(l[1]) && get_resource_id(l[1]) == Some(7nat));
  assert(is_deregister_timer(l[2]) && get_resource_id(l[2]) == Some(7nat));
  assert(!is_deregister_timer(l[0]) && !is_deregister_timer(l[1]));
  assert(is_timer_registered_before(l, 7, 2));
}

// A log with no PollBegin: current_poll_start is -1, so every
// in_current_poll_cycle / has_*_in_current_poll is false (the safe direction).
proof fn probe_no_poll_begin()
  ensures ({
    let l: Log = seq![
      UtilityEvent::Outbound(OutboundCall::RegisterTimer { resource_id: 7, deadline: 10 }),
    ];
    current_poll_start(l, 0) == -1 &&
    !in_current_poll_cycle(l, 0, 0) &&
    !has_waker_set_in_current_poll(l, 7, 0) &&
    !has_timer_registered_in_current_poll(l, 7, 0)
  }),
{
  let l: Log = seq![
    UtilityEvent::Outbound(OutboundCall::RegisterTimer { resource_id: 7, deadline: 10 }),
  ];
  reveal_with_fuel(find_last_poll_begin, 3);
  assert(!is_poll_begin(l[0]));
  assert(find_last_poll_begin(l, 0) == -1);
}

}
