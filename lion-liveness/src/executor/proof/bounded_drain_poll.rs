use vstd::prelude::*;
use crate::executor::spec::types::*;
use crate::executor::spec::log::*;
use crate::executor::spec::events::*;
use crate::executor::invariants;
use crate::executor::contracts::bounded_drain_poll::*;
use crate::framework::module_spec::*;
use crate::framework::async_contract::*;
use crate::framework::local_liveness::*;
use crate::framework::action_safety::*;

verus! {

pub open spec fn executor_module_spec() -> crate::framework::module_spec::ModuleSpec<Log> {
  crate::executor::executor_module_spec()
}

pub open spec fn executor_progress(l: Log, l_prime: Log) -> bool {
  crate::executor::executor_progress(l, l_prime)
}

// ============================================================================
// Bounded Drain Poll Liveness Proof (Generic for all DrainSource variants)
// ============================================================================
//
// Goal: bounded_liveness_without_arrival(executor_module_spec(), bounded_drain_poll(source))
//
// This proof covers all three Drain-based contracts:
// - Bounded ReactorWake Poll (source = ReactorWake)
// - Bounded TaskWake Poll (source = TaskWake)
// - Bounded Deferred Poll (source = Deferred)
//
// Proof structure is identical to bounded_injection_poll:
// 1. arrival + n progress => trigger (tid appears in Drain)
// 2. trigger => response (tid gets polled via TICK_EMPTIES_QUEUE + FIFO_TASK_SELECTION)
//
// ============================================================================

pub proof fn single_progress_has_drain_reactor_wake(l_prev: Log, l_next: Log)
  requires
    executor_progress(l_prev, l_next),
  ensures
    count_drain_between(l_next, DrainSource::ReactorWake, l_prev.len() as int, l_next.len() as int) >= 1,
    exists |idx: int|
      l_prev.len() as int <= idx < l_next.len() as int &&
      is_drain_reactor_wake_at(l_next, idx),
{
  let start = l_prev.len() as int;
  let end = l_next.len() as int;
  let tick_end_idx = end - 1;

  assert(is_tick_end_at(l_next, tick_end_idx));
  assert(invariants::executor_inv(l_next));

  // Step 1: TICK_HAS_PARK gives us a Park in this tick
  let thp = invariants::tick_has_park::tick_has_park();
  assert(action_safety_satisfied(thp, l_next));
  assert((thp.acceptance)(l_next, tick_end_idx));
  assert((thp.validity)(l_next, tick_end_idx));

  let park_idx: int = choose |p: int|
    0 <= p < tick_end_idx &&
    is_park_at(l_next, p) &&
    (forall |k: int| p < k < tick_end_idx ==> !is_tick_begin_at(l_next, k));

  // Park is in the new content (same logic as single_progress_has_pop)
  assert(is_tick_begin_at(l_next, start));
  if park_idx < start {
    assert(park_idx < start && start < tick_end_idx);
    assert(!is_tick_begin_at(l_next, start));
    assert(false);
  }
  assert(start <= park_idx);

  // Step 2: PARK_DRAIN_REACTOR_WAKE gives us Drain(ReactorWake) after park_idx
  let pdrw = invariants::park_drain_reactor_wake::park_drain_reactor_wake();
  assert(local_liveness_satisfied(pdrw, l_next));
  assert((pdrw.acceptance)(l_next, park_idx));

  let drain_idx: int = choose |j: int|
    #![trigger (pdrw.fulfillment)(l_next, park_idx, j)]
    j > park_idx &&
    (pdrw.fulfillment)(l_next, park_idx, j) &&
    (pdrw.timely)(l_next, park_idx, j);

  assert(is_drain_reactor_wake_at(l_next, drain_idx));

  // drain_idx is within same tick (no Tick::End between park_idx and drain_idx)
  // So drain_idx <= tick_end_idx
  if drain_idx > tick_end_idx {
    assert(park_idx < tick_end_idx && tick_end_idx < drain_idx);
    assert(is_tick_end_at(l_next, tick_end_idx));
    assert(!is_tick_end_at(l_next, tick_end_idx));
    assert(false);
  }
  assert(drain_idx <= tick_end_idx);
  assert(drain_idx < end);

  // drain_idx >= start (since drain_idx > park_idx >= start)
  assert(start <= drain_idx);

  // Now we have Drain(ReactorWake) at drain_idx in [start, end)
  count_includes_drain_at(l_next, DrainSource::ReactorWake, start, end, drain_idx);
  assert(start <= drain_idx < end && is_drain_reactor_wake_at(l_next, drain_idx));
}

// Helper: A single tick cycle has at least one Drain(TaskWake)
// Uses: TICK_HAS_DRAIN_TASK_WAKE (ActionSafety)
pub proof fn single_progress_has_drain_task_wake(l_prev: Log, l_next: Log)
  requires
    executor_progress(l_prev, l_next),
  ensures
    count_drain_between(l_next, DrainSource::TaskWake, l_prev.len() as int, l_next.len() as int) >= 1,
    exists |d: int|
      #![trigger is_drain_task_wake_at(l_next, d)]
      l_prev.len() as int <= d < l_next.len() && is_drain_task_wake_at(l_next, d),
{
  let start = l_prev.len() as int;
  let end = l_next.len() as int;
  let tick_end_idx = end - 1;

  assert(is_tick_end_at(l_next, tick_end_idx));
  assert(invariants::executor_inv(l_next));

  // TICK_HAS_DRAIN_TASK_WAKE gives us a Drain(TaskWake) in this tick
  let thdtw = invariants::tick_has_drain_task_wake::tick_has_drain_task_wake();
  assert(action_safety_satisfied(thdtw, l_next));
  assert((thdtw.acceptance)(l_next, tick_end_idx));
  assert((thdtw.validity)(l_next, tick_end_idx));

  let drain_idx: int = choose |d: int|
    0 <= d < tick_end_idx &&
    is_drain_task_wake_at(l_next, d) &&
    (forall |k: int| d < k < tick_end_idx ==> !is_tick_begin_at(l_next, k));

  // drain_idx is in the new content (same logic as single_progress_has_drain_reactor_wake)
  assert(is_tick_begin_at(l_next, start));
  if drain_idx < start {
    assert(drain_idx < start && start < tick_end_idx);
    assert(!is_tick_begin_at(l_next, start));
    assert(false);
  }
  assert(start <= drain_idx);
  assert(drain_idx < end);

  count_includes_drain_at(l_next, DrainSource::TaskWake, start, end, drain_idx);
}

// Helper: A single tick cycle has at least one Drain(Deferred)
// Uses: TICK_HAS_DRAIN_DEFERRED (ActionSafety)
pub proof fn single_progress_has_drain_deferred(l_prev: Log, l_next: Log)
  requires
    executor_progress(l_prev, l_next),
  ensures
    count_drain_between(l_next, DrainSource::Deferred, l_prev.len() as int, l_next.len() as int) >= 1,
    exists |d: int|
      #![trigger is_drain_deferred_at(l_next, d)]
      l_prev.len() as int <= d < l_next.len() && is_drain_deferred_at(l_next, d),
{
  let start = l_prev.len() as int;
  let end = l_next.len() as int;
  let tick_end_idx = end - 1;

  assert(is_tick_end_at(l_next, tick_end_idx));
  assert(invariants::executor_inv(l_next));

  // TICK_HAS_DRAIN_DEFERRED gives us a Drain(Deferred) in this tick
  let thdd = invariants::tick_has_drain_deferred::tick_has_drain_deferred();
  assert(action_safety_satisfied(thdd, l_next));
  assert((thdd.acceptance)(l_next, tick_end_idx));
  assert((thdd.validity)(l_next, tick_end_idx));

  let drain_idx: int = choose |d: int|
    0 <= d < tick_end_idx &&
    is_drain_deferred_at(l_next, d) &&
    (forall |k: int| d < k < tick_end_idx ==> !is_tick_begin_at(l_next, k));

  // drain_idx is in the new content
  assert(is_tick_begin_at(l_next, start));
  if drain_idx < start {
    assert(drain_idx < start && start < tick_end_idx);
    assert(!is_tick_begin_at(l_next, start));
    assert(false);
  }
  assert(start <= drain_idx);
  assert(drain_idx < end);
  assert(is_drain_deferred_at(l_next, drain_idx));

  count_includes_drain_at(l_next, DrainSource::Deferred, start, end, drain_idx);
}

// Helper: If there's a Drain(source) at d in [start, end), count >= 1
proof fn count_includes_drain_at(l: Log, source: DrainSource, start: int, end: int, d: int)
  requires
    0 <= start <= d && d < end && end <= l.len(),
    is_drain_at(l, d),
    get_drain_source(l[d]) == source,
  ensures
    count_drain_between(l, source, start, end) >= 1,
  decreases end - start
{
  if start == d {
    // The first element is a Drain(source)
  } else {
    // Recurse: count(start, end) = delta + count(start+1, end)
    count_includes_drain_at(l, source, start + 1, end, d);
  }
}

// Helper: Count additivity for Drain events
pub proof fn count_drain_additivity_range(l: Log, source: DrainSource, start: int, mid: int, end: int)
  requires
    0 <= start <= mid && mid <= end && end <= l.len(),
  ensures
    count_drain_between(l, source, start, end) ==
    count_drain_between(l, source, start, mid) + count_drain_between(l, source, mid, end),
  decreases mid - start
{
  if start >= mid {
    assert(count_drain_between(l, source, start, mid) == 0 as nat);
  } else {
    count_drain_additivity_range(l, source, start + 1, mid, end);
  }
}

// Helper: Count is preserved under prefix
pub proof fn count_drain_prefix_equals(l_short: Log, l_long: Log, source: DrainSource, start: int, end: int)
  requires
    is_prefix_of(l_short, l_long),
    0 <= start && end <= l_short.len(),
  ensures
    count_drain_between(l_short, source, start, end) == count_drain_between(l_long, source, start, end),
  decreases end - start
{
  if start >= end {
  } else {
    assert(l_short[start] == l_long[start]);
    count_drain_prefix_equals(l_short, l_long, source, start + 1, end);
  }
}

// Helper: Find the position of the n-th Drain(source) event
pub open spec fn find_nth_drain(l: Log, source: DrainSource, start: int, n: nat) -> int
  decreases l.len() - start
{
  if start >= l.len() || n == 0 {
    start
  } else if is_drain_at(l, start) && get_drain_source(l[start]) == source {
    if n == 1 {
      start
    } else {
      find_nth_drain(l, source, start + 1, (n - 1) as nat)
    }
  } else {
    find_nth_drain(l, source, start + 1, n)
  }
}

// Helper: Count of single Drain position
proof fn count_drain_single(l: Log, source: DrainSource, start: int)
  requires
    0 <= start < l.len(),
  ensures
    is_drain_at(l, start) && get_drain_source(l[start]) == source ==>
      count_drain_between(l, source, start, start + 1) == 1 as nat,
    !(is_drain_at(l, start) && get_drain_source(l[start]) == source) ==>
      count_drain_between(l, source, start, start + 1) == 0 as nat,
{
  reveal_with_fuel(count_drain_between, 2);
}

// Helper: If count >= n, then find_nth_drain finds a valid position
pub proof fn find_nth_drain_valid(l: Log, source: DrainSource, start: int, n: nat)
  requires
    0 <= start,
    n > 0,
    count_drain_between(l, source, start, l.len() as int) >= n,
  ensures
    start <= find_nth_drain(l, source, start, n) < l.len(),
    is_drain_at(l, find_nth_drain(l, source, start, n)),
    get_drain_source(l[find_nth_drain(l, source, start, n)]) == source,
    count_drain_between(l, source, start, find_nth_drain(l, source, start, n) + 1) == n,
  decreases l.len() - start
{
  let nth_pos = find_nth_drain(l, source, start, n);

  if start >= l.len() {
    assert(count_drain_between(l, source, start, l.len() as int) == 0 as nat);
    assert(false);
  } else if is_drain_at(l, start) && get_drain_source(l[start]) == source {
    count_drain_single(l, source, start);
    if n == 1 {
      assert(nth_pos == start);
    } else {
      assert(count_drain_between(l, source, start + 1, l.len() as int) >= (n - 1) as nat);
      find_nth_drain_valid(l, source, start + 1, (n - 1) as nat);
      let sub_nth_pos = find_nth_drain(l, source, start + 1, (n - 1) as nat);
      assert(nth_pos == sub_nth_pos);
      count_drain_additivity_range(l, source, start, start + 1, nth_pos + 1);
    }
  } else {
    count_drain_single(l, source, start);
    assert(count_drain_between(l, source, start + 1, l.len() as int) >= n);
    find_nth_drain_valid(l, source, start + 1, n);
    let sub_nth_pos = find_nth_drain(l, source, start + 1, n);
    assert(nth_pos == sub_nth_pos);
    count_drain_additivity_range(l, source, start, start + 1, nth_pos + 1);
  }
}

// ---- Tick-end counting helpers (wake-routing Phase C) — mirror the Drain
//      helpers above, but count is_tick_end_at instead of is_drain_at. ----

// count_tick_ends_between >= 1 if there is a tick-end at some d in [start, end).
pub proof fn count_includes_tick_end_at(l: Log, start: int, end: int, d: int)
  requires
    0 <= start <= d && d < end && end <= l.len(),
    is_tick_end_at(l, d),
  ensures
    count_tick_ends_between(l, start, end) >= 1,
  decreases end - start
{
  if start == d {
  } else {
    count_includes_tick_end_at(l, start + 1, end, d);
  }
}

// Additivity over a split point.
pub proof fn count_tick_ends_additivity_range(l: Log, start: int, mid: int, end: int)
  requires
    0 <= start <= mid && mid <= end && end <= l.len(),
  ensures
    count_tick_ends_between(l, start, end) ==
    count_tick_ends_between(l, start, mid) + count_tick_ends_between(l, mid, end),
  decreases mid - start
{
  if start >= mid {
    assert(count_tick_ends_between(l, start, mid) == 0 as nat);
  } else {
    count_tick_ends_additivity_range(l, start + 1, mid, end);
  }
}

// Preserved under prefix extension.
pub proof fn count_tick_ends_prefix_equals(l_short: Log, l_long: Log, start: int, end: int)
  requires
    is_prefix_of(l_short, l_long),
    0 <= start && end <= l_short.len(),
  ensures
    count_tick_ends_between(l_short, start, end) == count_tick_ends_between(l_long, start, end),
  decreases end - start
{
  if start >= end {
  } else {
    assert(l_short[start] == l_long[start]);
    count_tick_ends_prefix_equals(l_short, l_long, start + 1, end);
  }
}

// One executor step's new content is exactly one complete tick cycle, so it has a
// Tick::End at l_next.len()-1 ⟹ at least one tick-end in [l_prev.len(), l_next.len()).
pub proof fn single_progress_has_tick_end(l_prev: Log, l_next: Log)
  requires
    executor_progress(l_prev, l_next),
  ensures
    count_tick_ends_between(l_next, l_prev.len() as int, l_next.len() as int) >= 1,
{
  assert(crate::executor::is_complete_tick_cycle(l_next, l_prev.len() as int, l_next.len() as int));
  assert(is_tick_end_at(l_next, l_next.len() - 1));
  count_includes_tick_end_at(l_next, l_prev.len() as int, l_next.len() as int, l_next.len() - 1);
}

pub proof fn n_ticks_yield_n_drains_reactor_wake(l: Log, l_prime: Log, n: nat)
  requires
    is_prefix_of(l, l_prime),
    progress_n(executor_module_spec().progress, l, l_prime, n),
  ensures
    count_drain_between(l_prime, DrainSource::ReactorWake, l.len() as int, l_prime.len() as int) >= n,
  decreases n,
{
  if n == 0 {
  } else if n == 1 {
    let l_mid = crate::executor::proof::bounded_injection_poll::progress_n_decompose(l, l_prime, n);
    single_progress_has_drain_reactor_wake(l, l_mid);
  } else {
    let l_mid = crate::executor::proof::bounded_injection_poll::progress_n_decompose(l, l_prime, n);

    single_progress_has_drain_reactor_wake(l, l_mid);
    count_drain_prefix_equals(l_mid, l_prime, DrainSource::ReactorWake, l.len() as int, l_mid.len() as int);
    n_ticks_yield_n_drains_reactor_wake(l_mid, l_prime, (n - 1) as nat);
    count_drain_additivity_range(l_prime, DrainSource::ReactorWake, l.len() as int, l_mid.len() as int, l_prime.len() as int);
  }
}

// Main lemma: n tick cycles yield at least n Drain(TaskWake) events
// Uses: TICK_HAS_DRAIN_TASK_WAKE (ActionSafety)
#[verifier::rlimit(50)]
pub proof fn n_ticks_yield_n_drains_task_wake(l: Log, l_prime: Log, n: nat)
  requires
    is_prefix_of(l, l_prime),
    progress_n(executor_module_spec().progress, l, l_prime, n),
  ensures
    count_drain_between(l_prime, DrainSource::TaskWake, l.len() as int, l_prime.len() as int) >= n,
  decreases n,
{
  if n == 0 {
  } else if n == 1 {
    let l_mid = crate::executor::proof::bounded_injection_poll::progress_n_decompose(l, l_prime, n);
    single_progress_has_drain_task_wake(l, l_mid);
  } else {
    let l_mid = crate::executor::proof::bounded_injection_poll::progress_n_decompose(l, l_prime, n);

    single_progress_has_drain_task_wake(l, l_mid);
    count_drain_prefix_equals(l_mid, l_prime, DrainSource::TaskWake, l.len() as int, l_mid.len() as int);
    n_ticks_yield_n_drains_task_wake(l_mid, l_prime, (n - 1) as nat);
    count_drain_additivity_range(l_prime, DrainSource::TaskWake, l.len() as int, l_mid.len() as int, l_prime.len() as int);
  }
}

// Main lemma: n tick cycles yield at least n Drain(Deferred) events
// Uses: TICK_HAS_DRAIN_DEFERRED (ActionSafety)
#[verifier::rlimit(50)]
pub proof fn n_ticks_yield_n_drains_deferred(l: Log, l_prime: Log, n: nat)
  requires
    is_prefix_of(l, l_prime),
    progress_n(executor_module_spec().progress, l, l_prime, n),
  ensures
    count_drain_between(l_prime, DrainSource::Deferred, l.len() as int, l_prime.len() as int) >= n,
  decreases n,
{
  if n == 0 {
  } else if n == 1 {
    let l_mid = crate::executor::proof::bounded_injection_poll::progress_n_decompose(l, l_prime, n);
    single_progress_has_drain_deferred(l, l_mid);
  } else {
    let l_mid = crate::executor::proof::bounded_injection_poll::progress_n_decompose(l, l_prime, n);

    single_progress_has_drain_deferred(l, l_mid);
    count_drain_prefix_equals(l_mid, l_prime, DrainSource::Deferred, l.len() as int, l_mid.len() as int);
    n_ticks_yield_n_drains_deferred(l_mid, l_prime, (n - 1) as nat);
    count_drain_additivity_range(l_prime, DrainSource::Deferred, l.len() as int, l_mid.len() as int, l_prime.len() as int);
  }
}

}
