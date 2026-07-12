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
use crate::reactor::{reactor_module_spec, timestamps_strictly_increasing, timestamps_positive};
#[cfg(verus_keep_ghost)]
use crate::reactor::contracts::bounded_timer_wakeup::*;
#[cfg(verus_keep_ghost)]
use crate::framework::module_spec::{ModuleSpec, progress_n, progress_preserves_wf};
#[cfg(verus_keep_ghost)]
use crate::framework::async_contract::*;
#[cfg(verus_keep_ghost)]
use super::round_extension::*;
#[cfg(verus_keep_ghost)]
use super::timer_predicates::*;
#[cfg(verus_keep_ghost)]
use super::timeout_existence::{find_first_timestamp_ge_deadline, no_ts_in_range_same_max, k_timestamps_reach_deadline_aux, max_timestamp_on_prefix_eq};
#[cfg(verus_keep_ghost)]
use super::timeout_triggers_wake::timeout_triggers_wake_lemma;
#[cfg(verus_keep_ghost)]
use crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through;

verus! {


// Single-state reactor env predicate for the timer contract: the clock is
// strictly-increasing + positive, and (if a timer for rid is registered) it
// remains active through the log. This is what env_timer_wake_general_at consumes at
// each reached state; the env-form contract filters the response to traces where
// this holds at every state (so the facts are available everywhere, non-vacuously).
pub open spec fn env_reactor_timer(l: Log, rid: ResourceIdView) -> bool {
  timestamps_strictly_increasing(l) &&
  timestamps_positive(l) &&
  (find_register_timer_idx(l, rid) >= 0 ==>
    crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(
      l, find_register_timer_idx(l, rid), l.len() as int))
}

// PER-REGISTRATION env predicate + bound (Phase 0/A), keyed on the register INDEX
// i instead of the rid. env_reactor_timer_at anchors the resource-hold at the
// specific registration i (reuse of the rid via other registrations is
// unconstrained); timer_concrete_bound_at is i's deadline-based response bound.
pub open spec fn env_reactor_timer_at(l: Log, i: int) -> bool {
  timestamps_strictly_increasing(l) &&
  timestamps_positive(l) &&
  crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(
    l, i, l.len() as int)
}

pub open spec fn timer_concrete_bound_at(l: Log, i: int) -> nat {
  compute_bound(
    get_register_timer_deadline(l[i]),
    max_timestamp_up_to(l, l.len() as int))
}


// env-sourced timer wake: timer registered somewhere in l (acceptance), l_mid
// reached by k >= timer_concrete_bound rounds, env's clock+active facts at l_mid
// and active at a one-longer real state l_long ⇒ the reactor wake is fulfilled at
// l_mid. Every single-state fact is an env hypothesis (the old forall-extension
// timer_assumption and its consumer timer_bounded_liveness_proof were
// unsatisfiable/vacuous and have been removed). (deadline > max_ts general
// case; the already-timed-out case is separate.)
// env-sourced timer wake (WEAK "not deregistered" hypothesis):
// env only asserts the task hasn't DEREGISTERED the timer (timer_not_deregistered_through),
// NOT that the timer stays active (which the old timer_remains_active_between wrongly did
// by counting a WakeTask as retirement, excluding real firing states). Case-split on the
// first rid-wake k0: if a wake already fired (k0 < len) it is ours (active_rid_wake_is_ours,
// since k0 is the first ⟹ active up to it), so response holds directly; else no wake yet ⟹
// with not-deregistered the timer IS active to len ⟹ the existing timeout logic fires one.
// PER-REGISTRATION core wake lemma (Phase 0/A): the timer registered at the FIXED
// index reg fires its own waker by l_mid, given reg is not deregistered through
// l_mid and k >= reg's deadline bound. The registration index reg is a PARAMETER
// (the old rid-keyed wrapper carried a fixed reg = find(l,rid)); rid is derived
// from reg. Reuse-tolerant: nothing anchors at the leftmost registration.
pub proof fn env_timer_wake_general_at(l: Log, l_mid: Log, reg: int, k: nat)
  requires
    reactor_inv(l),
    reactor_inv(l_mid),
    0 <= reg < l.len(),
    is_succ_register_timer_at(l, reg),
    extends_by_k_rounds(l, l_mid, k),
    timestamps_strictly_increasing(l_mid),
    timestamps_positive(l_mid),
    timer_not_deregistered_through(l_mid, reg, l_mid.len() as int),
    l.len() < l_mid.len(),
    k >= timer_concrete_bound_at(l, reg),
  ensures
    crate::reactor::spec::log::has_wake_task_for_timer_after(l_mid, reg, reg + 1),
    crate::reactor::contracts::bounded_timer_wakeup::response_at(l_mid, reg),
{
  let rid = get_register_timer_rid(l[reg]);
  extends_by_k_rounds_implies_prefix(l, l_mid, k);
  assert(l_mid[reg] == l[reg]);
  assert(is_succ_register_timer_at(l_mid, reg));
  assert(get_register_timer_rid(l_mid[reg]) == rid);

  let k0 = super::timeout_triggers_wake::first_wake_rid_from(l_mid, rid, reg + 1);
  super::timeout_triggers_wake::first_wake_rid_props(l_mid, rid, reg + 1);
  // active up to k0: not deregistered (env) + no rid-wake before k0 (k0 is first)
  assert(crate::reactor::spec::log::timer_active_at(l_mid, reg, k0)) by {
    assert forall |m: int| reg < m < k0 implies
      !crate::reactor::spec::log::timer_retired_at(l_mid, rid, m) by {
      if crate::reactor::spec::log::timer_retired_at(l_mid, rid, m) {
        crate::reactor::spec::log::reveal_timer_retired_implies(l_mid, rid, m);
      }
    }
  }
  if k0 < l_mid.len() {
    // a wake already fired in the current window; it is ours (waker matches)
    super::timeout_triggers_wake::active_rid_wake_is_ours(l_mid, reg, k0);
    assert(crate::reactor::spec::log::has_wake_task_for_timer_after(l_mid, reg, reg + 1)) by {
      assert(reg + 1 <= k0 < l_mid.len() &&
        crate::reactor::spec::log::is_wake_task_at(l_mid, k0) &&
        get_wake_task_source_rid(l_mid[k0]) == rid &&
        get_wake_task_waker(l_mid[k0]) == get_register_timer_waker(l_mid[reg]));
    }
  } else {
    // no rid-wake yet ⟹ timer active to len (not deregistered + no wake)
    assert(timer_remains_active_between(l_mid, reg, reg + 1, l_mid.len() as int)) by {
      assert forall |i: int| reg + 1 <= i < l_mid.len() implies
        crate::reactor::spec::log::timer_active_at(l_mid, reg, i) by {
        assert forall |m: int| reg < m < i implies
          !crate::reactor::spec::log::timer_retired_at(l_mid, rid, m) by {
          if crate::reactor::spec::log::timer_retired_at(l_mid, rid, m) {
            crate::reactor::spec::log::reveal_timer_retired_implies(l_mid, rid, m);
          }
        }
      }
    }
    let deadline = get_register_timer_deadline(l[reg]);
    let max_ts = max_timestamp_up_to(l, l.len() as int);
    if deadline <= max_ts {
      // weak on l from weak on l_mid (prefix)
      assert(crate::reactor::spec::log::is_prefix_of(l, l_mid));
      assert(l[reg] == l_mid[reg]);
      assert(get_register_timer_rid(l_mid[reg]) == rid);
      assert(timer_not_deregistered_through(l, reg, l.len() as int)) by {
        assert forall |j: int| reg < j < l.len() implies
          !(is_succ_deregister_timer_at(l, j) && get_deregister_timer_rid(l[j]) == rid) by {
          assert(l[j] == l_mid[j]);
          assert(!(is_succ_deregister_timer_at(l_mid, j) &&
            get_deregister_timer_rid(l_mid[j]) == get_register_timer_rid(l_mid[reg])));
        }
      }
      timer_timed_out_in_l_gives_wake(l, l_mid, reg, deadline);
    } else {
      timer_eventual_wake_general(l, l_mid, reg, k);
    }
  }
  assert(crate::reactor::contracts::bounded_timer_wakeup::response_at(l_mid, reg)) by {
    let w: int = choose |w: int|
      reg + 1 <= w < l_mid.len() &&
      crate::reactor::spec::log::is_wake_task_at(l_mid, w) &&
      get_wake_task_source_rid(l_mid[w]) == rid &&
      get_wake_task_waker(l_mid[w]) == get_register_timer_waker(l_mid[reg]);
  }
}

// ============================================================================
// Shared helper lemmas (round extension, timeout crossing, wake bridging)
// ============================================================================

// reactor_inv is preserved under progress_n (chained reactor_progress).
// The progress relation requires reactor_inv on the right side of each
// step, so by induction on k, reactor_inv holds at l_prime.
proof fn reactor_inv_preserved_by_progress(l: Log, l_prime: Log, k: nat)
  requires
    reactor_inv(l),
    extends_by_k_rounds(l, l_prime, k),
  ensures
    reactor_inv(l_prime),
  decreases k
{
  if k == 0 {
    assert(l == l_prime);
  } else {
    let l_mid: Log = choose |l_mid: Log|
      extends_by_one_round(l, l_mid) &&
      extends_by_k_rounds(l_mid, l_prime, (k - 1) as nat);
    assert(crate::reactor::reactor_progress(l, l_mid));
    assert(reactor_inv(l_mid));
    reactor_inv_preserved_by_progress(l_mid, l_prime, (k - 1) as nat);
  }
}

// Searches for the first crossing of `deadline` between `start` and `end`.
// Returns an index where a GetCurrentTime with ts >= deadline appears, and
// no earlier GetCurrentTime in [start, idx) has ts >= deadline.
//
// Existence is guaranteed by the precondition that `max_ts` grew past
// `deadline` in this range.
#[verifier::rlimit(50)]
proof fn find_first_crossing(l: Log, start: int, end: int, deadline: InstantView)
    -> (idx: int)
  requires
    0 <= start <= end <= l.len(),
    max_timestamp_up_to(l, start) < deadline,
    max_timestamp_up_to(l, end) >= deadline,
  ensures
    start <= idx < end,
    is_get_current_time_at(l, idx),
    get_current_timestamp(l[idx]) >= deadline,
    forall |j: int| start <= j < idx && is_get_current_time_at(l, j) ==>
      get_current_timestamp(#[trigger] l[j]) < deadline,
  decreases end - start
{
  if start == end {
    // Contradicts max_ts(start) < deadline <= max_ts(end) when start == end.
    assert(false);
    return 0;
  }
  // Inspect the (end - 1)-th event vs (end-1)-th max_timestamp.
  // Easier: scan forward.
  if is_get_current_time_at(l, start) && get_current_timestamp(l[start]) >= deadline {
    return start;
  }
  // The event at `start` is either non-GetCurrentTime, or has ts < deadline.
  // In either case, max_ts(l, start + 1) <= max(max_ts(l, start), ts_at_start)
  // and if ts_at_start < deadline, still < deadline.
  let max_at_start_plus_1 = max_timestamp_up_to(l, start + 1);
  assert(max_at_start_plus_1 < deadline) by {
    if is_get_current_time_at(l, start) {
      // ts_at_start < deadline (by the else branch above)
      assert(get_current_timestamp(l[start]) < deadline);
    } else {
      // max_ts unchanged
    }
  };
  let idx = find_first_crossing(l, start + 1, end, deadline);
  // Forall holds: for j == start, GetCurrentTime ⇒ ts < deadline. For j > start, recursion.
  assert forall |j: int| start <= j < idx && is_get_current_time_at(l, j) implies
    get_current_timestamp(#[trigger] l[j]) < deadline
  by {
    if j == start {
      assert(get_current_timestamp(l[start]) < deadline);
    }
  };
  idx
}

// has_wake_task_for_timer_after on a prefix lifts to the extension.
proof fn has_wake_task_prefix_lift(
  l: Log,
  l_prime: Log,
  register_idx: int,
)
  requires
    is_prefix_of(l, l_prime),
    0 <= register_idx < l.len(),
    has_wake_task_for_timer_after(l, register_idx, register_idx + 1),
  ensures
    has_wake_task_for_timer_after(l_prime, register_idx, register_idx + 1),
{
  let rid = get_register_timer_rid(l[register_idx]);
  let waker = get_register_timer_waker(l[register_idx]);
  let i: int = choose |i: int| #![trigger l[i]]
    register_idx + 1 <= i < l.len() &&
    is_wake_task_at(l, i) &&
    get_wake_task_source_rid(l[i]) == rid &&
    get_wake_task_waker(l[i]) == waker;
  assert(l[i] == l_prime[i]);
  assert(l[register_idx] == l_prime[register_idx]);
  assert(get_register_timer_rid(l_prime[register_idx]) == rid);
  assert(get_register_timer_waker(l_prime[register_idx]) == waker);
  assert(is_wake_task_at(l_prime, i));
  assert(get_wake_task_source_rid(l_prime[i]) == rid);
  assert(get_wake_task_waker(l_prime[i]) == waker);
  assert(register_idx + 1 <= i < l_prime.len());
}

// timer_remains_active_between transfers from l_prime to l (when end <= l.len()).
// Uses existing timer_active_transfer_to_prefix.
proof fn timer_remains_active_l_prime_to_l(
  l: Log,
  l_prime: Log,
  register_idx: int,
  start: int,
  end: int,
)
  requires
    is_prefix_of(l, l_prime),
    is_succ_register_timer_at(l, register_idx),
    0 <= register_idx < l.len(),
    register_idx < start,
    start <= end <= l.len(),
    timer_remains_active_between(l_prime, register_idx, start, end),
  ensures
    timer_remains_active_between(l, register_idx, start, end),
{
  assert forall |i: int| start <= i < end implies timer_active_at(l, register_idx, i) by {
    timer_active_transfer_to_prefix(l, l_prime, register_idx, i);
  };
}

// Case B (deadline already reached in l): there's a timestamp in
// (register_idx, l.len()) ≥ deadline. Find the first such, apply
// timeout_triggers_wake_lemma on l, then transfer to l_prime.
#[verifier::rlimit(50)]
proof fn timer_timed_out_in_l_gives_wake(
  l: Log,
  l_prime: Log,
  register_idx: int,
  deadline: InstantView,
)
  requires
    reactor_inv(l),
    reactor_inv(l_prime),
    is_prefix_of(l, l_prime),
    0 <= register_idx < l.len(),
    is_succ_register_timer_at(l, register_idx),
    get_register_timer_deadline(l[register_idx]) == deadline,
    timestamps_strictly_increasing(l_prime),
    timer_remains_active_between(l_prime, register_idx, register_idx + 1, l_prime.len() as int),
    timer_not_deregistered_through(l, register_idx, l.len() as int),
    deadline <= max_timestamp_up_to(l, l.len() as int),
  ensures
    has_wake_task_for_timer_after(l_prime, register_idx, register_idx + 1),
{
  use crate::reactor::invariants::{reactor_action_safety_inv, timer_deadline_future};
  use crate::framework::action_safety::action_safety_satisfied;

  // 1. timer_deadline_future: deadline > max_ts(l, register_idx)
  assert(reactor_action_safety_inv(l));
  assert(action_safety_satisfied(timer_deadline_future::timer_deadline_future(), l));
  let tdf = timer_deadline_future::timer_deadline_future();
  assert((tdf.acceptance)(l, register_idx));
  assert((tdf.validity)(l, register_idx));
  assert(deadline > max_timestamp_up_to(l, register_idx));

  // 2. register_idx is RegisterTimer not GetCurrentTime
  assert(!is_get_current_time_at(l, register_idx));
  no_ts_in_range_same_max(l, register_idx, register_idx + 1);
  assert(max_timestamp_up_to(l, register_idx + 1) == max_timestamp_up_to(l, register_idx));
  assert(max_timestamp_up_to(l, register_idx + 1) < deadline);

  // 3. Find the first crossing in (register_idx, l.len())
  let timeout_idx = find_first_crossing(l, register_idx + 1, l.len() as int, deadline);
  assert(register_idx + 1 <= timeout_idx < l.len());
  assert(is_get_current_time_at(l, timeout_idx));
  assert(get_current_timestamp(l[timeout_idx]) >= deadline);

  // 4. Verify is_first_timeout_point(l, register_idx, timeout_idx)
  assert(is_first_timeout_point(l, register_idx, timeout_idx)) by {
    assert forall |j: int|
      register_idx < j < timeout_idx && is_get_current_time_at(l, j) implies
      get_current_timestamp(#[trigger] l[j]) < deadline
    by {
      if j == register_idx {
        // register_idx is not a GetCurrentTime
        assert(false);
      } else {
        // register_idx + 1 <= j < timeout_idx
        assert(register_idx + 1 <= j < timeout_idx);
      }
    };
  };

  // 5. Get timer_remains_active_between on l (from l_prime via prefix)
  timer_remains_active_l_prime_to_l(
    l, l_prime, register_idx, register_idx + 1, l.len() as int
  );
  assert(timer_remains_active_between(l, register_idx, register_idx + 1, l.len() as int));
  // From this, timer_active_at(l, register_idx, timeout_idx) holds (since
  // register_idx + 1 <= timeout_idx < l.len()).
  assert(timer_active_at(l, register_idx, timeout_idx));

  // is_timeout_point requires timer_active_at, GetCurrentTime, ts >= deadline,
  // and is_first_timeout_point — all established.
  assert(is_timeout_point(l, register_idx, timeout_idx));

  // For timeout_triggers_wake_lemma, also need:
  //   timer_remains_active_between(l, register_idx, timeout_idx, l.len() as int)
  assert(timer_remains_active_between(l, register_idx, timeout_idx, l.len() as int)) by {
    assert forall |i: int| timeout_idx <= i < l.len() implies
      timer_active_at(l, register_idx, i)
    by {
      // From timer_remains_active_between(l, register_idx, register_idx + 1, l.len())
      // since register_idx + 1 <= timeout_idx <= i < l.len().
    };
  };

  // 6. Apply timeout_triggers_wake_lemma
  super::timeout_triggers_wake::timeout_triggers_wake_lemma(l, register_idx, timeout_idx);
  assert(has_wake_task_for_timer_after(l, register_idx, register_idx + 1));

  // 7. Lift to l_prime via prefix
  has_wake_task_prefix_lift(l, l_prime, register_idx);
}

// If a GetCurrentTime with ts ≥ deadline exists at `ts_idx < end`, then
// max_timestamp_up_to(l, end) ≥ deadline.
proof fn ts_at_idx_implies_max_at_end(
  l: Log,
  ts_idx: int,
  end: int,
  deadline: InstantView,
)
  requires
    0 <= ts_idx < end <= l.len(),
    is_get_current_time_at(l, ts_idx),
    get_current_timestamp(l[ts_idx]) >= deadline,
  ensures
    max_timestamp_up_to(l, end) >= deadline,
  decreases end
{
  if end <= 0 {
    // unreachable
  } else if end == ts_idx + 1 {
    // max_ts(l, end) = max(max_ts(l, end-1), ts) >= ts >= deadline
    assert(is_get_current_time_at(l, end - 1));
    assert(get_current_timestamp(l[end - 1]) >= deadline);
  } else {
    // end > ts_idx + 1
    ts_at_idx_implies_max_at_end(l, ts_idx, end - 1, deadline);
    // max_ts(l, end) >= max_ts(l, end - 1) >= deadline
    assert(max_timestamp_up_to(l, end - 1) >= deadline);
  }
}

// Case A (deadline not yet reached in l): use k rounds of reactor_progress
// to extend timestamps past deadline, then derive wake.
#[verifier::rlimit(50)]
proof fn timer_eventual_wake_general(
  l: Log,
  l_prime: Log,
  register_idx: int,
  k: nat,
)
  requires
    reactor_inv(l),
    reactor_inv(l_prime),
    0 <= register_idx < l.len(),
    is_succ_register_timer_at(l, register_idx),
    extends_by_k_rounds(l, l_prime, k),
    timestamps_strictly_increasing(l_prime),
    timestamps_positive(l_prime),
    timer_remains_active_between(l_prime, register_idx, register_idx + 1, l_prime.len() as int),
    timer_not_deregistered_through(l_prime, register_idx, l_prime.len() as int),
    get_register_timer_deadline(l[register_idx]) > max_timestamp_up_to(l, l.len() as int),
    k >= compute_bound(
      get_register_timer_deadline(l[register_idx]),
      max_timestamp_up_to(l, l.len() as int)
    ),
  ensures
    has_wake_task_for_timer_after(l_prime, register_idx, register_idx + 1)
{
  let deadline = get_register_timer_deadline(l[register_idx]);
  let max_ts_l = max_timestamp_up_to(l, l.len() as int);

  // 1. Prefix + register_idx valid in l_prime
  extends_by_k_rounds_implies_prefix(l, l_prime, k);
  assert(is_prefix_of(l, l_prime));
  assert(l[register_idx] == l_prime[register_idx]);

  // 2. max_ts on prefix: max_ts(l_prime, l.len()) == max_ts(l, l.len()) < deadline
  max_timestamp_on_prefix_eq(l, l_prime, l.len() as int);
  assert(max_timestamp_up_to(l_prime, l.len() as int) == max_ts_l);
  assert(max_timestamp_up_to(l_prime, l.len() as int) < deadline);

  // 3. k_rounds_imply_k_timestamps + k_timestamps_reach_deadline_aux:
  //    there's a GetCurrentTime in [l.len(), l_prime.len()) with ts >= deadline
  k_rounds_imply_k_timestamps(l, l_prime, k);
  assert(count_get_current_time_in_range(l_prime, l.len() as int, l_prime.len() as int) >= k);
  // compute_bound guarantees max_ts + k > deadline:
  //   if deadline <= max_ts: bound = 1, deadline + 0 > deadline trivially (but we
  //   are in the case deadline > max_ts).
  //   if deadline > max_ts:  bound = (deadline - max_ts) + 1, so max_ts + bound > deadline.
  assert(max_ts_l + (k as int) > deadline);
  k_timestamps_reach_deadline_aux(
    l_prime,
    l.len() as int,
    l_prime.len() as int,
    max_ts_l,
    deadline,
    k
  );
  let exist_idx: int = choose |idx: int|
    l.len() as int <= idx < l_prime.len() &&
    is_get_current_time_at(l_prime, idx) &&
    get_current_timestamp(l_prime[idx]) >= deadline;
  assert(l.len() as int <= exist_idx < l_prime.len());

  // 4. max_ts(l_prime, l_prime.len()) >= deadline
  ts_at_idx_implies_max_at_end(l_prime, exist_idx, l_prime.len() as int, deadline);
  assert(max_timestamp_up_to(l_prime, l_prime.len() as int) >= deadline);

  // 5. Find FIRST crossing in (register_idx, l_prime.len()) — need to start
  //    from register_idx + 1 to preserve the "first after register" semantics.
  //    Use the fact: max_ts(l_prime, register_idx + 1) < deadline
  //    (since register_idx is not GetCurrentTime, max_ts(l_prime, register_idx + 1)
  //     == max_ts(l_prime, register_idx) <= max_ts(l_prime, l.len()) < deadline).
  assert(!is_get_current_time_at(l_prime, register_idx));
  no_ts_in_range_same_max(l_prime, register_idx, register_idx + 1);
  assert(max_timestamp_up_to(l_prime, register_idx + 1) == max_timestamp_up_to(l_prime, register_idx));
  // max_ts is monotone: max_ts(l_prime, register_idx) <= max_ts(l_prime, l.len()) < deadline
  max_ts_monotone(l_prime, register_idx, l.len() as int);
  assert(max_timestamp_up_to(l_prime, register_idx) <= max_timestamp_up_to(l_prime, l.len() as int));
  assert(max_timestamp_up_to(l_prime, register_idx + 1) < deadline);

  let timeout_idx = find_first_crossing(
    l_prime, register_idx + 1, l_prime.len() as int, deadline
  );
  assert(register_idx + 1 <= timeout_idx < l_prime.len());
  assert(is_get_current_time_at(l_prime, timeout_idx));
  assert(get_current_timestamp(l_prime[timeout_idx]) >= deadline);

  // 6. is_first_timeout_point(l_prime, register_idx, timeout_idx)
  assert(is_first_timeout_point(l_prime, register_idx, timeout_idx)) by {
    assert forall |j: int|
      register_idx < j < timeout_idx && is_get_current_time_at(l_prime, j) implies
      get_current_timestamp(#[trigger] l_prime[j]) < deadline
    by {
      if j == register_idx {
        assert(false);
      } else {
        assert(register_idx + 1 <= j < timeout_idx);
      }
    };
  };

  // 7. timer_active_at(l_prime, register_idx, timeout_idx) from timer_remains_active_between
  assert(timer_active_at(l_prime, register_idx, timeout_idx));
  assert(is_succ_register_timer_at(l_prime, register_idx));
  assert(is_timeout_point(l_prime, register_idx, timeout_idx));

  // 8. timer_remains_active_between(l_prime, register_idx, timeout_idx, l_prime.len())
  assert(timer_remains_active_between(l_prime, register_idx, timeout_idx, l_prime.len() as int)) by {
    assert forall |i: int| timeout_idx <= i < l_prime.len() implies
      timer_active_at(l_prime, register_idx, i)
    by {
      assert(register_idx + 1 <= timeout_idx <= i < l_prime.len());
    };
  };

  // 9. Apply timeout_triggers_wake_lemma on l_prime
  super::timeout_triggers_wake::timeout_triggers_wake_lemma(l_prime, register_idx, timeout_idx);
}

// max_timestamp_up_to is monotone in `end`.
pub proof fn max_ts_monotone(l: Log, i: int, j: int)
  requires
    0 <= i <= j <= l.len(),
  ensures
    max_timestamp_up_to(l, i) <= max_timestamp_up_to(l, j),
  decreases j - i
{
  if i == j {
  } else {
    max_ts_monotone(l, i, j - 1);
    // max_ts(l, j) is either max_ts(l, j-1) or max(max_ts(l, j-1), ts_at_j-1)
    // Either way, >= max_ts(l, j-1) >= max_ts(l, i).
  }
}

// Concrete bound for the timer contract: deadline-vs-current-timestamp difference.
pub open spec fn timer_concrete_bound(l: Log, rid: ResourceIdView) -> nat {
  let canonical_idx = find_register_timer_idx(l, rid);
  let deadline = get_register_timer_deadline(l[canonical_idx]);
  let max_ts_l = max_timestamp_up_to(l, l.len() as int);
  compute_bound(deadline, max_ts_l)
}


}
