use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::log::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::events::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::types::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::invariants::reactor_inv;
#[cfg(verus_keep_ghost)]
use crate::reactor::invariants::wake_on_expired::*;
#[cfg(verus_keep_ghost)]
use crate::framework::local_liveness::local_liveness_satisfied;
#[cfg(verus_keep_ghost)]
use super::timer_predicates::*;

verus! {

// At most one registration of a given rid is active at any point: to re-register
// a rid you must first retire the prior registration (R7). So if our timer
// (register_idx) is active at i and a WakeTask for rid occurs at i, that wake
// belongs to our registration — its waker is ours. Handles rid re-registration.
pub proof fn active_rid_wake_is_ours(l: Log, register_idx: int, i: int)
  requires
    reactor_inv(l),
    is_succ_register_timer_at(l, register_idx),
    register_idx < i < l.len(),
    timer_active_at(l, register_idx, i),
    is_wake_task_at(l, i),
    get_wake_task_source_rid(l[i]) == get_register_timer_rid(l[register_idx]),
  ensures
    get_wake_task_waker(l[i]) == get_register_timer_waker(l[register_idx]),
{
  use crate::reactor::invariants::reactor_action_safety_inv;
  use crate::reactor::invariants::{timer_waker_validity, timer_reg_uniqueness};
  use crate::framework::action_safety::action_safety_satisfied;

  let rid = get_register_timer_rid(l[register_idx]);
  assert(reactor_action_safety_inv(l));
  let twv = timer_waker_validity::timer_waker_validity();
  let tru = timer_reg_uniqueness::timer_reg_uniqueness();
  assert(action_safety_satisfied(twv, l));
  assert(action_safety_satisfied(tru, l));

  // R5 (timer_waker_validity): the rid-wake at i has a registration whose waker
  // it carries, and which is active at i.
  assert(timer_waker_validity::is_timer_wake_at(l, i)) by {
    assert(0 <= register_idx < i && is_succ_register_timer_at(l, register_idx) &&
      get_register_timer_rid(l[register_idx]) == rid);
  };
  assert((twv.acceptance)(l, i));
  assert((twv.validity)(l, i));
  let j = choose |j: int|
    0 <= j < i &&
    is_succ_register_timer_at(l, j) &&
    get_register_timer_rid(l[j]) == rid &&
    get_register_timer_waker(l[j]) == get_wake_task_waker(l[i]) &&
    timer_active_at(l, j, i);

  // j == register_idx: a different registration would force a retirement inside
  // the other's active interval (R7), contradicting activity.
  assert((tru.acceptance)(l, register_idx));
  assert((tru.validity)(l, register_idx));
  assert((tru.acceptance)(l, j));
  assert((tru.validity)(l, j));
  if j < register_idx {
    timer_reg_uniqueness::reveal_no_prior_timer_registration(l, rid, register_idx);
    let m = choose |m: int| j < m < register_idx && timer_retired_at(l, rid, m);
    assert(j < m < i);
    assert(!timer_retired_at(l, rid, m));
    assert(false);
  }
  if register_idx < j {
    timer_reg_uniqueness::reveal_no_prior_timer_registration(l, rid, j);
    let m = choose |m: int| register_idx < m < j && timer_retired_at(l, rid, m);
    assert(register_idx < m < i);
    assert(!timer_retired_at(l, rid, m));
    assert(false);
  }
  assert(j == register_idx);
}

// First index >= start carrying a WakeTask for rid (or l.len() if none).
pub open spec fn first_wake_rid_from(l: Log, rid: ResourceIdView, start: int) -> int
  decreases l.len() - start when start <= l.len()
{
  if start >= l.len() {
    l.len() as int
  } else if is_wake_task_at(l, start) && get_wake_task_source_rid(l[start]) == rid {
    start
  } else {
    first_wake_rid_from(l, rid, start + 1)
  }
}

pub proof fn first_wake_rid_props(l: Log, rid: ResourceIdView, start: int)
  requires 0 <= start <= l.len(),
  ensures
    start <= first_wake_rid_from(l, rid, start) <= l.len(),
    forall |k: int| start <= k < first_wake_rid_from(l, rid, start) ==>
      !(is_wake_task_at(l, k) && get_wake_task_source_rid(l[k]) == rid),
    first_wake_rid_from(l, rid, start) < l.len() ==> (
      is_wake_task_at(l, first_wake_rid_from(l, rid, start)) &&
      get_wake_task_source_rid(l[first_wake_rid_from(l, rid, start)]) == rid
    ),
  decreases l.len() - start
{
  if start >= l.len() {
  } else if is_wake_task_at(l, start) && get_wake_task_source_rid(l[start]) == rid {
  } else {
    first_wake_rid_props(l, rid, start + 1);
  }
}

proof fn no_earlier_timeout_point(l: Log, register_idx: int, timeout_idx: int, j: int)
  requires
    is_succ_register_timer_at(l, register_idx),
    is_timeout_point(l, register_idx, timeout_idx),
    register_idx < j < timeout_idx,
  ensures
    !has_timeout_point_at(l, register_idx, j),
{
  let deadline = get_register_timer_deadline(l[register_idx]);
  if is_get_current_time_at(l, j) {
    assert(is_first_timeout_point(l, register_idx, timeout_idx));
    assert(get_current_timestamp(l[j]) < deadline);
    assert(!has_timeout_point_at(l, register_idx, j));
  }
}

proof fn find_first_timeout_point_from_eq(l: Log, register_idx: int, timeout_idx: int, start: int)
  requires
    is_succ_register_timer_at(l, register_idx),
    register_idx + 1 <= start <= timeout_idx,
    has_timeout_point_at(l, register_idx, timeout_idx),
    forall |j: int| start <= j < timeout_idx ==> !has_timeout_point_at(l, register_idx, j),
  ensures
    find_first_timeout_point_from(l, register_idx, start) == timeout_idx,
  decreases timeout_idx - start
{
  if start == timeout_idx {
    assert(has_timeout_point_at(l, register_idx, start));
    assert(find_first_timeout_point_from(l, register_idx, start) == start);
  } else {
    assert(!has_timeout_point_at(l, register_idx, start));
    find_first_timeout_point_from_eq(l, register_idx, timeout_idx, start + 1);
  }
}

proof fn first_timeout_point_is_trigger(l: Log, register_idx: int, timeout_idx: int)
  requires
    is_succ_register_timer_at(l, register_idx),
    is_timeout_point(l, register_idx, timeout_idx),
  ensures
    has_timeout_point_at(l, register_idx, timeout_idx),
    first_timeout_point_rec(l, register_idx) == timeout_idx,
    has_first_timeout_point(l, register_idx),
{
  let deadline = get_register_timer_deadline(l[register_idx]);
  assert(is_get_current_time_at(l, timeout_idx));
  assert(get_current_timestamp(l[timeout_idx]) >= deadline);
  assert(timer_active_at(l, register_idx, timeout_idx));
  assert(has_timeout_point_at(l, register_idx, timeout_idx));

  assert forall |j: int| register_idx + 1 <= j < timeout_idx
    implies !has_timeout_point_at(l, register_idx, j) by {
    no_earlier_timeout_point(l, register_idx, timeout_idx, j);
  };

  find_first_timeout_point_from_eq(l, register_idx, timeout_idx, register_idx + 1);
}

pub proof fn timeout_triggers_wake_lemma(
  l: Log,
  register_idx: int,
  timeout_idx: int,
)
  requires
    reactor_inv(l),
    is_succ_register_timer_at(l, register_idx),
    is_timeout_point(l, register_idx, timeout_idx),
    // R16 is weakened (aligned with lion-reactor) with timer_awaiting_wake. The
    // composing context supplies the *decoupled* "not deregistered through end"
    // (NOT timer_active_at, which would also assert not-woken).
    timer_not_deregistered_through(l, register_idx, l.len() as int),
  ensures
    has_wake_task_for_timer_after(l, register_idx, register_idx + 1)
{
  use crate::reactor::invariants::{reactor_local_liveness_inv, reactor_inv};

  let rid = get_register_timer_rid(l[register_idx]);
  let waker = get_register_timer_waker(l[register_idx]);
  first_timeout_point_is_trigger(l, register_idx, timeout_idx);

  let k0 = first_wake_rid_from(l, rid, register_idx + 1);
  first_wake_rid_props(l, rid, register_idx + 1);

  // Our registration stays active up to k0: no deregister (precondition) and no
  // rid-wake (k0 is the first) in (register_idx, k0).
  assert(timer_active_at(l, register_idx, k0)) by {
    assert forall |m: int| register_idx < m < k0 implies
      !timer_retired_at(l, rid, m) by {
      if timer_retired_at(l, rid, m) {
        reveal_timer_retired_implies(l, rid, m);
      }
    };
  };

  if k0 < l.len() {
    // The first rid-wake at k0 belongs to OUR registration (matching waker).
    active_rid_wake_is_ours(l, register_idx, k0);
    assert(has_wake_task_for_timer_after(l, register_idx, register_idx + 1)) by {
      assert(register_idx + 1 <= k0 < l.len() &&
        is_wake_task_at(l, k0) &&
        get_wake_task_source_rid(l[k0]) == rid &&
        get_wake_task_waker(l[k0]) == waker);
    };
  } else {
    // No rid-wake at all ⟹ timer_awaiting_wake ⟹ fire weak R16 ⟹ a wake exists.
    assert(k0 == l.len() as int);
    assert(timer_active_at(l, register_idx, l.len() as int));
    assert(timer_awaiting_wake(l, register_idx));
    assert(trigger_fn(l, register_idx));

    assert(reactor_local_liveness_inv(l));
    assert(local_liveness_satisfied(wake_on_expired(), l));
    let woe = wake_on_expired();
    assert((woe.acceptance)(l, register_idx));
    let wake_idx: int = choose |j: int|
      #![trigger (woe.fulfillment)(l, register_idx, j)]
      j > register_idx &&
      (woe.fulfillment)(l, register_idx, j) &&
      (woe.timely)(l, register_idx, j);
    assert(response_fn(l, register_idx, wake_idx));
    assert(register_idx + 1 <= wake_idx < l.len());
    assert(has_wake_task_for_timer_after(l, register_idx, register_idx + 1)) by {
      assert(register_idx + 1 <= wake_idx < l.len() &&
        is_wake_task_at(l, wake_idx) &&
        get_wake_task_source_rid(l[wake_idx]) == rid &&
        get_wake_task_waker(l[wake_idx]) == waker);
    };
  }
}

}
