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
use crate::reactor::invariants::park_poll_once;
#[cfg(verus_keep_ghost)]
use crate::reactor::contracts::bounded_io_wakeup::{find_io_syscall_register_idx, find_io_syscall_register_idx_from};
#[cfg(verus_keep_ghost)]
use crate::reactor::reactor_module_spec;
#[cfg(verus_keep_ghost)]
use crate::reactor::contracts::bounded_io_wakeup::*;
#[cfg(verus_keep_ghost)]
use crate::framework::module_spec::{ModuleSpec, progress_n, progress_preserves_wf};
#[cfg(verus_keep_ghost)]
use crate::framework::async_contract::*;
#[cfg(verus_keep_ghost)]
use crate::framework::action_safety::action_safety_satisfied;
#[cfg(verus_keep_ghost)]
use crate::framework::local_liveness::local_liveness_satisfied;
#[cfg(verus_keep_ghost)]
use super::round_extension::*;

verus! {

proof fn reactor_inv_preserved_by_progress_io(l: Log, l_prime: Log, k: nat)
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
    reactor_inv_preserved_by_progress_io(l_mid, l_prime, (k - 1) as nat);
  }
}

proof fn find_register_io_idx_from_stable(
  l: Log,
  l_prime: Log,
  rid: ResourceIdView,
  start: int,
  idx_l: int,
)
  requires
    is_prefix_of(l, l_prime),
    0 <= start <= idx_l + 1,
    0 <= idx_l < l.len(),
    io_syscall_registered_at(l, idx_l),
    get_io_syscall_register_rid(l[idx_l]) == rid,
    find_io_syscall_register_idx_from(l, rid, start) == idx_l,
  ensures
    find_io_syscall_register_idx_from(l_prime, rid, start) == idx_l,
  decreases (idx_l + 1) - start
{
  if start == idx_l {
    assert(l[start] == l_prime[start]);
  } else {
    if start > idx_l {
      find_register_io_idx_from_ge_start(l, rid, start);
      assert(false);
    }
    assert(start < idx_l);
    assert(l[start] == l_prime[start]);
    assert(start < l.len());
    if io_syscall_registered_at(l, start) && get_io_syscall_register_rid(l[start]) == rid {
      assert(false);
    }
    assert(!(io_syscall_registered_at(l, start) && get_io_syscall_register_rid(l[start]) == rid));
    assert(!(io_syscall_registered_at(l_prime, start)
          && get_io_syscall_register_rid(l_prime[start]) == rid));
    find_register_io_idx_from_stable(l, l_prime, rid, start + 1, idx_l);
  }
}

proof fn find_register_io_idx_from_ge_start(l: Log, rid: ResourceIdView, start: int)
  ensures
    find_io_syscall_register_idx_from(l, rid, start) == -1 ||
      find_io_syscall_register_idx_from(l, rid, start) >= start,
  decreases (if start <= l.len() { l.len() - start } else { 0 })
{
  if start >= l.len() {
  } else if io_syscall_registered_at(l, start) && get_io_syscall_register_rid(l[start]) == rid {
  } else {
    find_register_io_idx_from_ge_start(l, rid, start + 1);
  }
}

// find_io_syscall_register_idx_from, when returning >= 0, points to a succ register io.
proof fn find_register_io_idx_from_returns_valid(l: Log, rid: ResourceIdView, start: int)
  ensures
    find_io_syscall_register_idx_from(l, rid, start) >= 0 ==> {
      let idx = find_io_syscall_register_idx_from(l, rid, start);
      0 <= idx < l.len() &&
      io_syscall_registered_at(l, idx) &&
      get_io_syscall_register_rid(l[idx]) == rid
    },
  decreases (if start <= l.len() { l.len() - start } else { 0 })
{
  if start >= l.len() {
  } else if io_syscall_registered_at(l, start) && get_io_syscall_register_rid(l[start]) == rid {
  } else {
    find_register_io_idx_from_returns_valid(l, rid, start + 1);
  }
}

proof fn find_last_set_waker_readable_returns_valid(
  l: Log,
  rid: ResourceIdView,
  before: int,
)
  ensures
    crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(l, rid, before) >= 0 ==> {
      let idx = crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(l, rid, before);
      0 <= idx < before &&
      is_succ_set_waker_at(l, idx) &&
      get_set_waker_rid(l[idx]) == rid &&
      get_set_waker_interest(l[idx]).0
    },
  decreases before
{
  use crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec;
  if before <= 0 {
  } else if is_succ_set_waker_at(l, before - 1) &&
            get_set_waker_rid(l[before - 1]) == rid &&
            get_set_waker_interest(l[before - 1]).0
  {
  } else {
    find_last_set_waker_readable_returns_valid(l, rid, before - 1);
  }
}

// Symmetric writable version.
proof fn find_last_set_waker_writable_returns_valid(
  l: Log,
  rid: ResourceIdView,
  before: int,
)
  ensures
    crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_writable_rec(l, rid, before) >= 0 ==> {
      let idx = crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_writable_rec(l, rid, before);
      0 <= idx < before &&
      is_succ_set_waker_at(l, idx) &&
      get_set_waker_rid(l[idx]) == rid &&
      get_set_waker_interest(l[idx]).1
    },
  decreases before
{
  use crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_writable_rec;
  if before <= 0 {
  } else if is_succ_set_waker_at(l, before - 1) &&
            get_set_waker_rid(l[before - 1]) == rid &&
            get_set_waker_interest(l[before - 1]).1
  {
  } else {
    find_last_set_waker_writable_returns_valid(l, rid, before - 1);
  }
}

// If a readable match exists at `match_idx < before`, find_last returns >= match_idx.
proof fn find_last_set_waker_readable_ge(
  l: Log,
  rid: ResourceIdView,
  before: int,
  match_idx: int,
)
  requires
    0 <= match_idx < before <= l.len(),
    is_succ_set_waker_at(l, match_idx),
    get_set_waker_rid(l[match_idx]) == rid,
    get_set_waker_interest(l[match_idx]).0,
  ensures
    crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(l, rid, before) >= match_idx,
  decreases before
{
  use crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_readable_rec;
  if before <= 0 {
  } else if is_succ_set_waker_at(l, before - 1) &&
            get_set_waker_rid(l[before - 1]) == rid &&
            get_set_waker_interest(l[before - 1]).0
  {
  } else {
    if before - 1 == match_idx {
      assert(false);
    }
    assert(before - 1 > match_idx);
    find_last_set_waker_readable_ge(l, rid, before - 1, match_idx);
  }
}

// Symmetric writable.
proof fn find_last_set_waker_writable_ge(
  l: Log,
  rid: ResourceIdView,
  before: int,
  match_idx: int,
)
  requires
    0 <= match_idx < before <= l.len(),
    is_succ_set_waker_at(l, match_idx),
    get_set_waker_rid(l[match_idx]) == rid,
    get_set_waker_interest(l[match_idx]).1,
  ensures
    crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_writable_rec(l, rid, before) >= match_idx,
  decreases before
{
  use crate::reactor::invariants::wake_on_io_ready::find_last_set_waker_for_rid_writable_rec;
  if before <= 0 {
  } else if is_succ_set_waker_at(l, before - 1) &&
            get_set_waker_rid(l[before - 1]) == rid &&
            get_set_waker_interest(l[before - 1]).1
  {
  } else {
    if before - 1 == match_idx {
      assert(false);
    }
    assert(before - 1 > match_idx);
    find_last_set_waker_writable_ge(l, rid, before - 1, match_idx);
  }
}

// Bridge: under reactor_inv, contract's `io_syscall_active_at_set_waker` (uses
// leftmost register via find_io_syscall_register_idx) implies invariant's
// `io_syscall_active_at_set_waker` (uses rightmost-before-sw_idx via
// find_io_syscall_register_for_rid). They coincide because:
//   - The contract's "no deregister of rid in (leftmost, sw_idx)" rules
//     out any deregister in that range.
//   - By io_reg_uniqueness, any LATER register of the same rid would
//     have a prior deregister, contradicting the above.
//   - Therefore no register of `rid` exists in (leftmost, sw_idx), so
//     `find_io_syscall_register_for_rid` (rightmost-before-sw) returns leftmost.
proof fn bridge_io_active(
  l: Log,
  rid: ResourceIdView,
  sw_idx: int,
)
  requires
    reactor_inv(l),
    0 <= sw_idx < l.len(),
    io_syscall_active_at_set_waker(l, rid, sw_idx),  // contract version
  ensures
    crate::reactor::invariants::wake_on_io_ready::io_syscall_active_at_set_waker(l, rid, sw_idx),
{
}

proof fn find_register_io_for_rid_eq_leftmost(
  l: Log,
  rid: ResourceIdView,
  before: int,
  expected: int,
)
  requires
    0 <= expected < before <= l.len(),
    io_syscall_registered_at(l, expected),
    get_io_syscall_register_rid(l[expected]) == rid,
    forall |idx2: int| expected < idx2 < before ==> !(
      io_syscall_registered_at(l, idx2) && get_io_syscall_register_rid(l[idx2]) == rid
    ),
  ensures
    crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, rid, before) == expected,
  decreases before
{
  use crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid;
  if before <= 0 {
  } else if io_syscall_registered_at(l, before - 1) && get_io_syscall_register_rid(l[before - 1]) == rid {
    // returns before - 1. Must equal `expected`.
    if before - 1 != expected {
      // before - 1 > expected (since before > expected) and predicate holds at before - 1.
      assert(expected < before - 1 < before);
      assert(false);
    }
  } else {
    // recurse on before - 1
    if before - 1 == expected {
      assert(io_syscall_registered_at(l, expected));
      assert(get_io_syscall_register_rid(l[expected]) == rid);
      assert(false);
    }
    find_register_io_for_rid_eq_leftmost(l, rid, before - 1, expected);
  }
}

// From IoEventReady (with matching direction) + reactor_inv (containing
// the directional wake_on_io_ready invariants), derive response_fn:
// some (sw, wake) matching pair exists in l_prime.
pub proof fn io_ready_implies_response(
  l_prime: Log,
  rid: ResourceIdView,
  set_waker_idx: int,
)
  requires
    reactor_inv(l_prime),
    io_remains_active_assumption(l_prime, rid),
    0 <= set_waker_idx < l_prime.len(),
    // set_waker_idx is the LAST SetWaker for rid, so the reshaped
    // io_remains_active_assumption is anchored exactly at its before-waker
    // registration (find_io_syscall_register_for_rid(rid, set_waker_idx)).
    set_waker_idx == find_last_set_waker_for_rid(l_prime, rid, l_prime.len() as int),
    is_succ_set_waker_at(l_prime, set_waker_idx),
    get_set_waker_rid(l_prime[set_waker_idx]) == rid,
    io_syscall_active_at_set_waker(l_prime, rid, set_waker_idx),
    exists |i: int| #![trigger l_prime[i]]
      set_waker_idx < i < l_prime.len() &&
      is_io_event_ready_at(l_prime, i) &&
      get_io_event(l_prime[i]).resource_id == rid &&
      ((get_set_waker_interest(l_prime[set_waker_idx]).0 && get_io_event(l_prime[i]).readable) ||
       (get_set_waker_interest(l_prime[set_waker_idx]).1 && get_io_event(l_prime[i]).writable)),
  ensures
    response_fn(l_prime, rid),
    exists |w: int| #![trigger l_prime[w]]
      set_waker_idx < w < l_prime.len() &&
      is_wake_task_at(l_prime, w) &&
      get_wake_task_source_rid(l_prime[w]) == rid,
{
  use crate::reactor::invariants::wake_on_io_ready;

  let io_ready_idx: int = choose |i: int| #![trigger l_prime[i]]
    set_waker_idx < i < l_prime.len() &&
    is_io_event_ready_at(l_prime, i) &&
    get_io_event(l_prime[i]).resource_id == rid &&
    ((get_set_waker_interest(l_prime[set_waker_idx]).0 && get_io_event(l_prime[i]).readable) ||
     (get_set_waker_interest(l_prime[set_waker_idx]).1 && get_io_event(l_prime[i]).writable));

  // Bridge contract io_syscall_active_at_set_waker → invariant version
  bridge_io_active(l_prime, rid, set_waker_idx);
  assert(wake_on_io_ready::io_syscall_active_at_set_waker(l_prime, rid, set_waker_idx));

  // No deregister of `rid` in (set_waker_idx, io_ready_idx). set_waker_idx is the
  // LAST SetWaker for rid (requires), so the reshaped io_remains_active_assumption
  // is anchored exactly at reg_bw = find_io_syscall_register_for_rid(rid, set_waker_idx)
  // (its before-waker registration, given by io_syscall_active_at_set_waker), yielding
  // no-deregister in (reg_bw, l_prime.len()) directly — no leftmost bridge needed.
  let reg_bw = wake_on_io_ready::find_io_syscall_register_for_rid(l_prime, rid, set_waker_idx);
  assert(reg_bw >= 0 && reg_bw < set_waker_idx);  // from io_syscall_active_at_set_waker
  assert(set_waker_idx == find_last_set_waker_for_rid(l_prime, rid, l_prime.len() as int));
  assert forall |k: int| set_waker_idx < k < io_ready_idx implies !(
    io_syscall_deregistered_at(l_prime, k) && get_io_syscall_deregister_rid(l_prime[k]) == rid
  ) by {
    if set_waker_idx < k < io_ready_idx
      && io_syscall_deregistered_at(l_prime, k)
      && get_io_syscall_deregister_rid(l_prime[k]) == rid
    {
      // io_remains_active_assumption's forall is over j in (reg_bw, l_prime.len())
      assert(reg_bw < set_waker_idx);
      assert(reg_bw < k);
      assert(k < l_prime.len());
      assert(false);
    }
  };

  let interest = get_set_waker_interest(l_prime[set_waker_idx]);
  let event = get_io_event(l_prime[io_ready_idx]);

  if interest.0 && event.readable {
    // Readable case: apply wake_on_io_ready_readable invariant
    let woir = wake_on_io_ready::wake_on_io_ready_readable();
    assert(reactor_inv(l_prime));
    assert(local_liveness_satisfied(woir, l_prime));

    // Show trigger_fn_readable(l_prime, io_ready_idx)
    assert(wake_on_io_ready::has_valid_set_waker_readable_syscall(l_prime, io_ready_idx)) by {
      assert(event.readable);
      // The exists witness is `set_waker_idx`.
      assert(0 <= set_waker_idx < io_ready_idx);
      assert(is_succ_set_waker_at(l_prime, set_waker_idx));
      assert(get_set_waker_rid(l_prime[set_waker_idx]) == rid);
      assert(get_set_waker_interest(l_prime[set_waker_idx]).0);
      assert(wake_on_io_ready::io_syscall_active_at_set_waker(l_prime, rid, set_waker_idx));
    };
    assert(wake_on_io_ready::trigger_fn_readable(l_prime, io_ready_idx));
    assert((woir.acceptance)(l_prime, io_ready_idx));

    let wake_j: int = choose |j: int|
      #![trigger (woir.fulfillment)(l_prime, io_ready_idx, j)]
      j > io_ready_idx &&
      (woir.fulfillment)(l_prime, io_ready_idx, j) &&
      (woir.timely)(l_prime, io_ready_idx, j);
    assert(wake_on_io_ready::response_fn_readable(l_prime, io_ready_idx, wake_j));

    // response_fn_readable picks `find_last_set_waker_for_rid_readable_rec` for the waker.
    let chosen_sw_idx = wake_on_io_ready::find_last_set_waker_for_rid_readable_rec(
      l_prime, rid, io_ready_idx
    );
    find_last_set_waker_readable_ge(l_prime, rid, io_ready_idx, set_waker_idx);
    assert(chosen_sw_idx >= set_waker_idx);
    find_last_set_waker_readable_returns_valid(l_prime, rid, io_ready_idx);
    assert(0 <= chosen_sw_idx < io_ready_idx);
    assert(is_succ_set_waker_at(l_prime, chosen_sw_idx));
    assert(get_set_waker_rid(l_prime[chosen_sw_idx]) == rid);
    // wake_j > io_ready_idx > chosen_sw_idx
    assert(chosen_sw_idx < wake_j);
    assert(chosen_sw_idx < l_prime.len());

    assert(response_fn(l_prime, rid)) by {
      assert(is_wake_task_at(l_prime, wake_j));
      assert(get_wake_task_source_rid(l_prime[wake_j]) == rid);
      assert(get_wake_task_waker(l_prime[wake_j])
             == get_set_waker_waker(l_prime[chosen_sw_idx]));
    };
    assert(set_waker_idx < wake_j < l_prime.len() &&
      is_wake_task_at(l_prime, wake_j) &&
      get_wake_task_source_rid(l_prime[wake_j]) == rid);
  } else {
    // Writable case (symmetric)
    assert(interest.1 && event.writable);
    let woiw = wake_on_io_ready::wake_on_io_ready_writable();
    assert(local_liveness_satisfied(woiw, l_prime));

    assert(wake_on_io_ready::has_valid_set_waker_writable_syscall(l_prime, io_ready_idx)) by {
      assert(event.writable);
      assert(0 <= set_waker_idx < io_ready_idx);
      assert(is_succ_set_waker_at(l_prime, set_waker_idx));
      assert(get_set_waker_rid(l_prime[set_waker_idx]) == rid);
      assert(get_set_waker_interest(l_prime[set_waker_idx]).1);
      assert(wake_on_io_ready::io_syscall_active_at_set_waker(l_prime, rid, set_waker_idx));
    };
    assert(wake_on_io_ready::trigger_fn_writable(l_prime, io_ready_idx));
    assert((woiw.acceptance)(l_prime, io_ready_idx));

    let wake_j: int = choose |j: int|
      #![trigger (woiw.fulfillment)(l_prime, io_ready_idx, j)]
      j > io_ready_idx &&
      (woiw.fulfillment)(l_prime, io_ready_idx, j) &&
      (woiw.timely)(l_prime, io_ready_idx, j);
    assert(wake_on_io_ready::response_fn_writable(l_prime, io_ready_idx, wake_j));

    let chosen_sw_idx = wake_on_io_ready::find_last_set_waker_for_rid_writable_rec(
      l_prime, rid, io_ready_idx
    );
    find_last_set_waker_writable_ge(l_prime, rid, io_ready_idx, set_waker_idx);
    assert(chosen_sw_idx >= set_waker_idx);
    find_last_set_waker_writable_returns_valid(l_prime, rid, io_ready_idx);
    assert(0 <= chosen_sw_idx < io_ready_idx);
    assert(is_succ_set_waker_at(l_prime, chosen_sw_idx));
    assert(get_set_waker_rid(l_prime[chosen_sw_idx]) == rid);
    assert(chosen_sw_idx < wake_j);
    assert(chosen_sw_idx < l_prime.len());

    assert(response_fn(l_prime, rid)) by {
      assert(is_wake_task_at(l_prime, wake_j));
      assert(get_wake_task_source_rid(l_prime[wake_j]) == rid);
      assert(get_wake_task_waker(l_prime[wake_j])
             == get_set_waker_waker(l_prime[chosen_sw_idx]));
    };
    assert(set_waker_idx < wake_j < l_prime.len() &&
      is_wake_task_at(l_prime, wake_j) &&
      get_wake_task_source_rid(l_prime[wake_j]) == rid);
  }
}

// find_last_set_waker_for_rid scans right-to-left from `before-1`. If a
// match exists at `set_waker_idx < before`, the result is `>= set_waker_idx`.
pub proof fn find_last_set_waker_ge_match(
  l: Log,
  rid: ResourceIdView,
  before: int,
  set_waker_idx: int,
)
  requires
    0 <= set_waker_idx < before <= l.len(),
    is_succ_set_waker_at(l, set_waker_idx),
    get_set_waker_rid(l[set_waker_idx]) == rid,
  ensures
    find_last_set_waker_for_rid(l, rid, before) >= set_waker_idx,
  decreases before
{
  if before <= 0 {
    // unreachable: before > set_waker_idx >= 0
  } else if is_succ_set_waker_at(l, before - 1) && get_set_waker_rid(l[before - 1]) == rid {
    // returns before - 1, and before - 1 >= set_waker_idx (since before > set_waker_idx)
  } else {
    if before - 1 == set_waker_idx {
      // contradicts: predicate holds at set_waker_idx but else branch says it doesn't
      assert(false);
    }
    assert(before - 1 > set_waker_idx);
    find_last_set_waker_ge_match(l, rid, before - 1, set_waker_idx);
  }
}

// find_last_set_waker_for_rid, when returning >= 0, points to a succ set_waker for rid.
pub proof fn find_last_set_waker_returns_succ(l: Log, rid: ResourceIdView, before: int)
  ensures
    find_last_set_waker_for_rid(l, rid, before) >= 0 ==> {
      let idx = find_last_set_waker_for_rid(l, rid, before);
      0 <= idx < before &&
      is_succ_set_waker_at(l, idx) &&
      get_set_waker_rid(l[idx]) == rid
    },
  decreases before
{
  if before <= 0 {
  } else if is_succ_set_waker_at(l, before - 1) && get_set_waker_rid(l[before - 1]) == rid {
  } else {
    find_last_set_waker_returns_succ(l, rid, before - 1);
  }
}

// find_last_set_waker_for_rid returns the LARGEST matching index: no SetWaker for
// rid exists strictly above the result (below `before`).
pub proof fn find_last_set_waker_no_later(l: Log, rid: ResourceIdView, before: int)
  ensures
    forall |q: int| find_last_set_waker_for_rid(l, rid, before) < q < before ==>
      !(is_succ_set_waker_at(l, q) && get_set_waker_rid(l[q]) == rid),
  decreases before
{
  if before <= 0 {
  } else if is_succ_set_waker_at(l, before - 1) && get_set_waker_rid(l[before - 1]) == rid {
  } else {
    find_last_set_waker_no_later(l, rid, before - 1);
    assert forall |q: int| find_last_set_waker_for_rid(l, rid, before) < q < before implies
      !(is_succ_set_waker_at(l, q) && get_set_waker_rid(l[q]) == rid) by {
      if q < before - 1 {
      }
    }
  }
}

// If j is a SetWaker for rid and no SetWaker for rid exists in (j, before), then
// find_last_set_waker_for_rid(before) == j.
pub proof fn find_last_eq_if_last(l: Log, rid: ResourceIdView, before: int, j: int)
  requires
    0 <= j < before <= l.len(),
    is_succ_set_waker_at(l, j),
    get_set_waker_rid(l[j]) == rid,
    forall |q: int| j < q < before ==> !(is_succ_set_waker_at(l, q) && get_set_waker_rid(l[q]) == rid),
  ensures
    find_last_set_waker_for_rid(l, rid, before) == j,
  decreases before
{
  if before <= 0 {
  } else if is_succ_set_waker_at(l, before - 1) && get_set_waker_rid(l[before - 1]) == rid {
    if before - 1 != j {
      assert(j < before - 1 < before);
      assert(false);
    }
  } else {
    if before - 1 == j {
      assert(false);
    }
    find_last_eq_if_last(l, rid, before - 1, j);
  }
}

pub proof fn find_last_prefix_eq(l1: Log, l2: Log, rid: ResourceIdView, before: int)
  requires
    0 <= before <= l1.len(),
    before <= l2.len(),
    forall |i: int| 0 <= i < before ==> l1[i] == l2[i],
  ensures
    find_last_set_waker_for_rid(l1, rid, before) == find_last_set_waker_for_rid(l2, rid, before),
  decreases before
{
  if before > 0 {
    find_last_prefix_eq(l1, l2, rid, before - 1);
  }
}

// find_last is stable when no NEW SetWaker for rid appears in the extension window.
pub proof fn find_last_stable_no_new_setwaker(s_r: Log, l_r: Log, rid: ResourceIdView, before: int)
  requires
    s_r.len() <= before <= l_r.len(),
    crate::reactor::spec::log::is_prefix_of(s_r, l_r),
    forall |m: int| s_r.len() <= m < before ==>
      !(is_succ_set_waker_at(l_r, m) && get_set_waker_rid(l_r[m]) == rid),
  ensures
    find_last_set_waker_for_rid(l_r, rid, before) ==
      find_last_set_waker_for_rid(s_r, rid, s_r.len() as int),
  decreases before
{
  if before <= s_r.len() {
    assert(s_r =~= l_r.subrange(0, s_r.len() as int));
    find_last_prefix_eq(l_r, s_r, rid, s_r.len() as int);
  } else {
    find_last_stable_no_new_setwaker(s_r, l_r, rid, before - 1);
  }
}

// Single-state reactor env predicate for the io contract: the io registration
// remains active, and (for the LATEST SetWaker for rid — find_last) it is active and
// becomes ready once `cap` poll-events accumulate from it. Count-conditional (like
// env_N's io_ready_forward_here) so it holds at pre-ready states too (satisfiable).
pub open spec fn env_reactor_io(l: Log, rid: ResourceIdView, cap: nat) -> bool {
  io_remains_active_assumption(l, rid) &&
  (find_last_set_waker_for_rid(l, rid, l.len() as int) >= 0 ==> {
    let sw = find_last_set_waker_for_rid(l, rid, l.len() as int);
    &&& 0 <= sw < l.len()
    &&& is_succ_set_waker_at(l, sw)
    &&& get_set_waker_rid(l[sw]) == rid
    &&& io_syscall_active_at_set_waker(l, rid, sw)
    &&& (count_poll_events_in_range(l, sw, l.len() as int) >= cap ==>
          has_io_event_ready_matching_interest_after(l, rid, get_set_waker_interest(l[sw]), sw))
  })
}

// Per-state io wake: given env_reactor_io and that `cap` poll-events have accumulated
// from the latest SetWaker (so the readiness clause fires), env_io_wake_general
// yields the wake. Single-state (env_io_wake_general needs no l_long, unlike timer).
pub proof fn io_env_response_at(l: Log, rid: ResourceIdView, cap: nat)
  requires
    reactor_inv(l),
    env_reactor_io(l, rid, cap),
    find_last_set_waker_for_rid(l, rid, l.len() as int) >= 0,
    count_poll_events_in_range(l, find_last_set_waker_for_rid(l, rid, l.len() as int), l.len() as int) >= cap,
  ensures
    response_fn(l, rid),
    exists |w: int| #![trigger l[w]]
      find_last_set_waker_for_rid(l, rid, l.len() as int) < w < l.len() &&
      is_wake_task_at(l, w) &&
      get_wake_task_source_rid(l[w]) == rid,
{
  let sw = find_last_set_waker_for_rid(l, rid, l.len() as int);
  env_io_wake_general(l, rid, sw);
}

pub proof fn env_io_wake_general(l_mid: Log, rid: ResourceIdView, sw_idx: int)
  requires
    reactor_inv(l_mid),
    io_remains_active_assumption(l_mid, rid),
    0 <= sw_idx < l_mid.len(),
    sw_idx == find_last_set_waker_for_rid(l_mid, rid, l_mid.len() as int),
    is_succ_set_waker_at(l_mid, sw_idx),
    get_set_waker_rid(l_mid[sw_idx]) == rid,
    io_syscall_active_at_set_waker(l_mid, rid, sw_idx),
    has_io_event_ready_matching_interest_after(
      l_mid, rid, get_set_waker_interest(l_mid[sw_idx]), sw_idx),
  ensures
    response_fn(l_mid, rid),
    exists |w: int| #![trigger l_mid[w]]
      sw_idx < w < l_mid.len() &&
      is_wake_task_at(l_mid, w) &&
      get_wake_task_source_rid(l_mid[w]) == rid,
{
  // The IoEventReady witness is strictly after sw_idx (sw_idx is a SetWaker, not
  // an IoEventReady), so the strict-form readiness io_ready_implies_response needs.
  let i: int = choose |i: int| #![trigger l_mid[i]]
    sw_idx <= i < l_mid.len() &&
    is_io_event_ready_at(l_mid, i) &&
    get_io_event(l_mid[i]).resource_id == rid &&
    ((get_set_waker_interest(l_mid[sw_idx]).0 && get_io_event(l_mid[i]).readable) ||
     (get_set_waker_interest(l_mid[sw_idx]).1 && get_io_event(l_mid[i]).writable));
  assert(sw_idx < i);
  io_ready_implies_response(l_mid, rid, sw_idx);
}

pub proof fn k_rounds_imply_k_poll_events(l: Log, l_prime: Log, k: nat)
  requires
    reactor_inv(l),
    extends_by_k_rounds(l, l_prime, k),
  ensures
    is_prefix_of(l, l_prime),
    count_poll_events_in_range(l_prime, l.len() as int, l_prime.len() as int) >= k,
  decreases k
{
  extends_by_k_rounds_implies_prefix(l, l_prime, k);
  if k == 0 {
    assert(l == l_prime);
  } else {
    let l_mid: Log = choose |l_mid: Log|
      extends_by_one_round(l, l_mid) &&
      extends_by_k_rounds(l_mid, l_prime, (k - 1) as nat);

    one_round_has_at_least_one_poll_events(l, l_mid);
    k_rounds_imply_k_poll_events(l_mid, l_prime, (k - 1) as nat);

    extends_by_k_rounds_implies_prefix(l_mid, l_prime, (k - 1) as nat);

    count_poll_events_split_additive(l_prime, l.len() as int, l_mid.len() as int, l_prime.len() as int);
    count_poll_events_on_prefix_eq(l_mid, l_prime, l.len() as int, l_mid.len() as int);
  }
}

proof fn one_round_has_at_least_one_poll_events(l: Log, l_prime: Log)
  requires
    reactor_inv(l),
    extends_by_one_round(l, l_prime),
  ensures
    count_poll_events_in_range(l_prime, l.len() as int, l_prime.len() as int) >= 1,
{
  use crate::reactor::is_complete_park_cycle;
  use crate::reactor::invariants::reactor_action_safety_inv;

  assert(crate::reactor::reactor_progress(l, l_prime));

  let (park_start, park_end): (int, int) = choose |park_start: int, park_end: int|
    #![trigger is_complete_park_cycle(l_prime, park_start, park_end)]
    l.len() as int <= park_start &&
    park_start < park_end &&
    park_end <= l_prime.len() as int &&
    is_complete_park_cycle(l_prime, park_start, park_end) &&
    (forall |i: int| l.len() as int <= i < park_start ==>
      crate::reactor::spec::events::is_inbound_non_park(#[trigger] l_prime[i])) &&
    (forall |i: int| park_end <= i < l_prime.len() as int ==>
      crate::reactor::spec::events::is_inbound_non_park(#[trigger] l_prime[i]));

  let park_end_idx = park_end - 1;
  assert(is_park_end_at(l_prime, park_end_idx));
  assert(is_park_begin_at(l_prime, park_start));

  assert(reactor_inv(l_prime));
  assert(reactor_action_safety_inv(l_prime));
  assert(action_safety_satisfied(park_poll_once::park_poll_once(), l_prime));

  let ppo = park_poll_once::park_poll_once();
  assert(park_poll_once::action_fn(l_prime, park_end_idx));
  assert((ppo.acceptance)(l_prime, park_end_idx));
  assert((ppo.validity)(l_prime, park_end_idx));
  assert(park_poll_once::has_exactly_one_poll_events_in_park(l_prime, park_end_idx));

  assert forall |idx: int| park_start < idx && idx <= park_end_idx
    implies !is_park_begin_at(l_prime, idx) by {
    if park_start < idx && idx < park_end_idx {
      assert(!is_park_begin_at(l_prime, idx));
    } else if idx == park_end_idx {
      assert(is_park_end_at(l_prime, idx));
    }
  };

  assert forall |k: int| park_start < k < park_end_idx implies
    !is_park_end_at(l_prime, k) by {
    assert(park_start < k < park_end - 1);
    assert(!is_park_begin_at(l_prime, k));  // triggers is_complete_park_cycle's inner forall
  };
  current_park_start_in_cycle(l_prime, park_start, park_end_idx);
  let ps = current_park_start(l_prime, park_end_idx);
  assert(ps == park_start);

  assert(park_poll_once::count_poll_events_in_range(l_prime, ps, park_end_idx) == 1);

  count_poll_events_eq_park_poll_once(l_prime, ps, park_end_idx);
  assert(count_poll_events_in_range(l_prime, ps, park_end_idx) == 1);

  count_poll_events_split_additive(l_prime, l.len() as int, park_start, l_prime.len() as int);
  count_poll_events_split_additive(l_prime, park_start, park_end_idx, l_prime.len() as int);
}

proof fn find_last_park_begin_in_cycle(l: Log, start: int, i: int)
  requires
    0 <= start < l.len(),
    start <= i < l.len(),
    is_park_begin_at(l, start),
    forall |k: int| start < k <= i ==> !is_park_begin_at(l, k),
  ensures
    find_last_park_begin(l, i) == start,
  decreases i - start
{
  if i == start {
    assert(is_park_begin_at(l, i));
    assert(find_last_park_begin(l, i) == i);
  } else {
    assert(!is_park_begin_at(l, i));
    find_last_park_begin_in_cycle(l, start, i - 1);
  }
}

// Same, for the (now reactor-aligned) current_park_start.
proof fn current_park_start_in_cycle(l: Log, start: int, i: int)
  requires
    0 <= start < l.len(),
    start < i < l.len(),
    is_park_begin_at(l, start),
    forall |k: int| start < k <= i ==> !is_park_begin_at(l, k),
    forall |k: int| start < k < i ==> !is_park_end_at(l, k),
  ensures
    current_park_start(l, i) == start,
  decreases i - start
{
  if i == start + 1 {
  } else {
    current_park_start_in_cycle(l, start, i - 1);
  }
}

proof fn count_poll_events_eq_park_poll_once(l: Log, start: int, end: int)
  requires
    0 <= start <= end,
    end <= l.len(),
  ensures
    count_poll_events_in_range(l, start, end) ==
    park_poll_once::count_poll_events_in_range(l, start, end),
  decreases end - start
{
  if start >= end {
  } else {
    count_poll_events_eq_park_poll_once(l, start + 1, end);
  }
}

pub proof fn count_poll_events_split_additive(l: Log, start: int, mid: int, end: int)
  requires
    0 <= start <= mid,
    mid <= end <= l.len(),
  ensures
    count_poll_events_in_range(l, start, end) ==
      count_poll_events_in_range(l, start, mid) +
      count_poll_events_in_range(l, mid, end),
  decreases mid - start
{
  if start >= mid {
  } else {
    count_poll_events_split_additive(l, start + 1, mid, end);
  }
}

// First io-deregister of `rid` in [lo, hi) (or -1). Used by the io keystone to
// obtain a deregister d with io_syscall_active_at(reg, d) — i.e. no earlier deregister —
// so io dereg-by-owner attribution applies.
pub open spec fn first_io_dereg_in(l: Log, rid: ResourceIdView, lo: int, hi: int) -> int
  decreases hi - lo
{
  if lo >= hi {
    -1
  } else if io_syscall_deregistered_at(l, lo) && get_io_syscall_deregister_rid(l[lo]) == rid {
    lo
  } else {
    first_io_dereg_in(l, rid, lo + 1, hi)
  }
}

pub proof fn first_io_dereg_in_props(l: Log, rid: ResourceIdView, lo: int, hi: int, w: int)
  requires
    lo <= w < hi,
    io_syscall_deregistered_at(l, w),
    get_io_syscall_deregister_rid(l[w]) == rid,
  ensures
    lo <= first_io_dereg_in(l, rid, lo, hi) < hi,
    io_syscall_deregistered_at(l, first_io_dereg_in(l, rid, lo, hi)),
    get_io_syscall_deregister_rid(l[first_io_dereg_in(l, rid, lo, hi)]) == rid,
    forall |j: int| lo <= j < first_io_dereg_in(l, rid, lo, hi) ==>
      !(io_syscall_deregistered_at(l, j) && get_io_syscall_deregister_rid(l[j]) == rid),
  decreases hi - lo
{
  if lo >= hi {
  } else if io_syscall_deregistered_at(l, lo) && get_io_syscall_deregister_rid(l[lo]) == rid {
  } else {
    first_io_dereg_in_props(l, rid, lo + 1, hi, w);
  }
}

pub proof fn count_poll_events_on_prefix_eq(l: Log, l_prime: Log, start: int, end: int)
  requires
    is_prefix_of(l, l_prime),
    0 <= start <= end,
    end <= l.len(),
  ensures
    count_poll_events_in_range(l, start, end) ==
    count_poll_events_in_range(l_prime, start, end),
  decreases end - start
{
  if start >= end {
  } else {
    assert(l[start] == l_prime[start]);
    count_poll_events_on_prefix_eq(l, l_prime, start + 1, end);
  }
}


}
