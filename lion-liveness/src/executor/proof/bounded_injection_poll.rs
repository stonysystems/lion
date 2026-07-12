use vstd::prelude::*;
use crate::executor::spec::types::*;
use crate::executor::spec::log::*;
use crate::executor::spec::events::*;
use crate::executor::invariants;
use crate::executor::contracts::bounded_injection_poll::*;
use crate::framework::module_spec::*;
use crate::framework::async_contract::*;
use crate::framework::local_liveness::*;
use crate::framework::action_safety::*;

verus! {

// Re-define wrappers for functions in crate::executor verus! block
// These functions are defined in super::super (crate::executor::mod.rs)
pub open spec fn executor_module_spec() -> crate::framework::module_spec::ModuleSpec<Log> {
  crate::executor::executor_module_spec()
}

pub open spec fn executor_progress(l: Log, l_prime: Log) -> bool {
  crate::executor::executor_progress(l, l_prime)
}

pub open spec fn is_complete_tick_cycle(l: Log, start: int, end: int) -> bool {
  crate::executor::is_complete_tick_cycle(l, start, end)
}

// ============================================================================
// Bounded Injection Poll Liveness Proof
// ============================================================================
//
// Goal: bounded_liveness_without_arrival(executor_module_spec(), bounded_injection_poll())
//
// Theorem: For any task tid with arrival_at_position(l, tid, n), after n tick
// cycles (progress_n), the task will be polled (response_fn).
//
// Proof structure:
// 1. progress_preserves_wf: invariants are preserved by tick cycles
// 2. arrival + n progress => trigger (tid popped from injection queue)
// 3. trigger => response (tid gets polled)
//
// ============================================================================
// Proof Status: Helper lemmas only (main liveness moved to composed layer)
// ============================================================================
//
// The main bounded_injection_poll_liveness theorem has been removed.
// The composed proof (end_to_end.rs) now uses multi-step queue drainage directly.
// This file retains helper lemmas used by the composed layer:
// - pop_injection_adds_to_queue: PopInjection adds tid to FIFO queue
// - progress_preserves_executor_inv: executor_inv preserved by progress
// - progress_n_implies_prefix, progress_n_preserves_inv, etc.
//
// ============================================================================
// Design: progress includes well-formedness preservation
// ============================================================================
//
// executor_progress(l, l') includes executor_inv(l') in its definition.
// This moves implementation-level invariant preservation into progress,
// making progress_preserves_wf trivial.
//
// ============================================================================

// ============================================================================
// Part 1: Progress Preserves Well-Formedness
// ============================================================================
//
// With the updated definition of executor_progress, well-formedness preservation
// is now part of the progress definition itself:
//
//   executor_progress(l, l') :=
//     l' extends l by one tick cycle AND executor_inv(l')
//
// This makes progress_preserves_wf trivial to prove.

use crate::executor::proof::action_safety_prefix::*;

pub proof fn progress_preserves_executor_inv()
  ensures
    progress_preserves_wf(executor_module_spec())
{
  // Trivial: executor_progress definition includes executor_inv(l_prime)
}

// ============================================================================
// Part 2: Helper Lemmas (decomposed from main theorem)
// ============================================================================

// Lemma: executor_progress implies is_prefix_of
proof fn executor_progress_implies_prefix(l: Log, l_prime: Log)
  requires
    executor_progress(l, l_prime),
  ensures
    is_prefix_of(l, l_prime),
{
  // From executor_progress definition:
  // l_prime.len() > l.len() && l =~= l_prime.subrange(0, l.len())
  // This directly implies is_prefix_of
}

// Helper: prefix relation is transitive
proof fn prefix_transitive(l1: Log, l2: Log, l3: Log)
  requires
    is_prefix_of(l1, l2),
    is_prefix_of(l2, l3),
  ensures
    is_prefix_of(l1, l3),
{
  // l1.len() <= l2.len() <= l3.len()
  // l1 =~= l2.subrange(0, l1.len()) =~= l3.subrange(0, l1.len())
  assert(l1.len() <= l3.len());
  assert forall |i: int| 0 <= i < l1.len() implies l1[i] == l3[i] by {
    assert(l1[i] == l2[i]);
    assert(l2[i] == l3[i]);
  };
}

// Lemma: progress_n with executor_progress implies is_prefix_of
// (By induction on n: each step extends the log)
pub proof fn progress_n_implies_prefix(l: Log, l_prime: Log, n: nat)
  requires
    progress_n(executor_module_spec().progress, l, l_prime, n),
  ensures
    is_prefix_of(l, l_prime),
  decreases n,
{
  // progress_n definition: exists trace of length n+1
  // trace[0] = l, trace[n] = l_prime, each step is executor_progress
  let trace: Seq<Log> = choose |trace: Seq<Log>|
    #![trigger trace.len()]
    trace.len() == n + 1 &&
    trace.first() == l &&
    trace.last() == l_prime &&
    is_valid_trace(executor_module_spec().progress, trace);

  if n == 0 {
    // trace.len() == 1, so l == l_prime
    assert(l =~= l_prime);
  } else {
    // trace[0] = l, trace[1], ..., trace[n] = l_prime
    // executor_progress(trace[0], trace[1]) => is_prefix_of(l, trace[1])
    let l_mid: Log = trace[1];
    assert(executor_progress(l, l_mid));
    executor_progress_implies_prefix(l, l_mid);

    // Recursively: is_prefix_of(trace[1], l_prime)
    // Need to show progress_n(trace[1], l_prime, n-1)
    let subtrace: Seq<Log> = trace.subrange(1, trace.len() as int);
    assert(subtrace.len() == n);
    assert(subtrace.first() == l_mid);
    assert(subtrace.last() == l_prime);

    // Show is_valid_trace(subtrace)
    assert(is_valid_trace(executor_module_spec().progress, subtrace)) by {
      assert forall |i: int| 0 <= i < subtrace.len() - 1 implies
        (executor_module_spec().progress)(#[trigger] subtrace[i], subtrace[i + 1])
      by {
        assert(subtrace[i] == trace[i + 1]);
        assert(subtrace[i + 1] == trace[i + 2]);
        assert((executor_module_spec().progress)(trace[i + 1], trace[i + 2]));
      };
    };

    // Now we have progress_n(l_mid, l_prime, n-1)
    progress_n_implies_prefix(l_mid, l_prime, (n - 1) as nat);

    // Combine: prefix(l, l_mid) && prefix(l_mid, l_prime) => prefix(l, l_prime)
    prefix_transitive(l, l_mid, l_prime);
  }
}

// Lemma: progress_n preserves well-formedness
// (Follows from progress_preserves_wf by induction)
pub proof fn progress_n_preserves_inv(l: Log, l_prime: Log, n: nat)
  requires
    invariants::executor_inv(l),
    progress_n(executor_module_spec().progress, l, l_prime, n),
    progress_preserves_wf(executor_module_spec()),
  ensures
    invariants::executor_inv(l_prime),
  decreases n,
{
  let trace: Seq<Log> = choose |trace: Seq<Log>|
    #![trigger trace.len()]
    trace.len() == n + 1 &&
    trace.first() == l &&
    trace.last() == l_prime &&
    is_valid_trace(executor_module_spec().progress, trace);

  if n == 0 {
    // trace.len() == 1, so l == l_prime
    assert(l =~= l_prime);
  } else {
    // trace[0] = l, executor_progress(l, trace[1])
    let l_mid: Log = trace[1];
    assert(executor_progress(l, l_mid));

    // progress_preserves_wf gives us: executor_inv(l) && progress(l, l_mid) => executor_inv(l_mid)
    assert(invariants::executor_inv(l_mid));

    // Build subtrace for recursive call
    let subtrace: Seq<Log> = trace.subrange(1, trace.len() as int);
    assert(subtrace.len() == n);
    assert(subtrace.first() == l_mid);
    assert(subtrace.last() == l_prime);

    assert(is_valid_trace(executor_module_spec().progress, subtrace)) by {
      assert forall |i: int| 0 <= i < subtrace.len() - 1 implies
        (executor_module_spec().progress)(#[trigger] subtrace[i], subtrace[i + 1])
      by {
        assert(subtrace[i] == trace[i + 1]);
        assert(subtrace[i + 1] == trace[i + 2]);
      };
    };

    // Recursive call
    progress_n_preserves_inv(l_mid, l_prime, (n - 1) as nat);
  }
}

// ============================================================================
// Key Lemma: arrival + n progress => trigger
// ============================================================================
//
// This is the core of the bounded liveness proof.
//
// Proof structure:
// 1. arrival_at_position(l, tid, n) says: tid is at position n in queue
// 2. Each tick cycle has at least one PopInjection attempt (TICK_HAS_POP_INJECTION)
// 3. If there are tasks in the queue, PopInjection returns Some
// 4. After n tick cycles, we've done at least n pops
// 5. By arrival semantics, the n-th pop yields tid
// 6. Therefore trigger_fn holds
//
// The key MODEL ASSUMPTION is: arrival implies the queue is non-empty
// for at least n pops (FIFO queue semantics).

// Helper: Find the index of the n-th PopInjection (any, regardless of Some/None) after start
pub open spec fn find_nth_pop_index(l: Log, start: int, n: nat) -> int
  recommends n > 0
  decreases l.len() - start
{
  if start >= l.len() || n == 0 {
    l.len() as int  // sentinel: not found
  } else if is_pop_injection_at(l, start) {
    if n == 1 {
      start
    } else {
      find_nth_pop_index(l, start + 1, (n - 1) as nat)
    }
  } else {
    find_nth_pop_index(l, start + 1, n)
  }
}

// Helper: find_nth_pop_index is valid when count >= n
// Note: This finds ANY PopInjection (Some or None). The arrival predicate
// guarantees the n-th PopInjection returns Some(tid).
pub proof fn find_nth_pop_index_valid(l: Log, start: int, end: int, n: nat)
  requires
    0 <= start <= end && end <= l.len(),
    n > 0,
    count_pop_injection_between(l, start, end) >= n,
  ensures
    ({
      let idx = find_nth_pop_index(l, start, n);
      start <= idx && idx < end &&
      is_pop_injection_at(l, idx) &&
      count_pop_injection_between(l, start, idx) == (n - 1) as nat
    }),
  decreases end - start
{
  // Induction on end - start.
  // Since count >= n > 0 and start <= end, there's at least one pop in [start, end).

  if start >= end {
    // count_pop_injection_between(l, start, end) = 0 by definition when start >= end
    // But we have count >= n > 0, so this case is impossible
    assert(false);  // unreachable
  } else {
    // start < end, so we can look at l[start]
    if is_pop_injection_at(l, start) {
      // start is a PopInjection
      // count(start, end) = 1 + count(start+1, end)
      if n == 1 {
        // find_nth_pop_index returns start
        let idx = find_nth_pop_index(l, start, n);
        assert(idx == start);
        assert(start <= idx && idx < end);
        assert(is_pop_injection_at(l, idx));
        // count(start, start) = 0 = n-1
        assert(count_pop_injection_between(l, start, idx) == 0);
      } else {
        // n > 1, find_nth_pop_index recurses with n-1
        // count(start+1, end) = count(start, end) - 1 >= n - 1
        // By IH, find_nth_pop_index(l, start+1, n-1) is valid
        find_nth_pop_index_valid(l, start + 1, end, (n - 1) as nat);
      }
    } else {
      // start is not a PopInjection
      // count(start, end) = count(start+1, end) >= n
      // find_nth_pop_index recurses with same n
      // By IH, find_nth_pop_index(l, start+1, n) is valid
      find_nth_pop_index_valid(l, start + 1, end, n);
    }
  }
}

proof fn count_subrange_equals(l: Log, start: int, end: int, subrange_end: int)
  requires
    0 <= start <= end,
    end <= subrange_end,
    subrange_end <= l.len(),
  ensures
    count_pop_injection_between(l.subrange(0, subrange_end), start, end) ==
    count_pop_injection_between(l, start, end),
  decreases end - start
{
  if start >= end {
    // Base case: empty range
  } else {
    // Inductive case
    let l_sub = l.subrange(0, subrange_end);
    // l_sub[start] == l[start] since start < end <= subrange_end <= l.len()
    assert(l_sub[start] == l[start]);

    // Recursive case
    count_subrange_equals(l, start + 1, end, subrange_end);
  }
}

// Helper: count additivity - count(start, end+1) = count(start, end) + (is_pop at end ? 1 : 0)
// Note: Now counts ALL PopInjection events (not just Some)
proof fn count_additivity(l: Log, start: int, end: int)
  requires
    0 <= start <= end,
    end < l.len(),
  ensures
    count_pop_injection_between(l, start, end + 1) ==
    count_pop_injection_between(l, start, end) +
    (if is_pop_injection_at(l, end) { 1 as nat } else { 0 as nat }),
  decreases end - start
{
  let is_pop_at_end = is_pop_injection_at(l, end);
  let delta: nat = if is_pop_at_end { 1 as nat } else { 0 as nat };

  if start == end {
    // Base case: count(end, end) = 0
    assert(count_pop_injection_between(l, start, end) == 0);

    // count(end, end+1): unfold the definition
    // count(end+1, end+1) = 0 (since end+1 >= end+1)
    // So count(end, end+1) = delta
    assert(count_pop_injection_between(l, end + 1, end + 1) == 0 as nat);
    assert(count_pop_injection_between(l, start, end + 1) == delta);
  } else {
    // Inductive case: start < end
    count_additivity(l, start + 1, end);

    let count_start_plus_1_to_end = count_pop_injection_between(l, start + 1, end);
    let count_start_plus_1_to_end_plus_1 = count_pop_injection_between(l, start + 1, end + 1);

    // IH gives:
    assert(count_start_plus_1_to_end_plus_1 == count_start_plus_1_to_end + delta);

    let is_pop_at_start = is_pop_injection_at(l, start);
    let start_delta: nat = if is_pop_at_start { 1 as nat } else { 0 as nat };

    // Unfold count(start, end):
    // count(start, end) = start_delta + count(start+1, end)
    assert(count_pop_injection_between(l, start, end) == start_delta + count_start_plus_1_to_end);

    // Unfold count(start, end+1):
    // count(start, end+1) = start_delta + count(start+1, end+1)
    assert(count_pop_injection_between(l, start, end + 1) == start_delta + count_start_plus_1_to_end_plus_1);
  }
}

pub proof fn single_progress_has_pop(l_prev: Log, l_next: Log)
  requires
    executor_progress(l_prev, l_next),
  ensures
    count_pop_injection_between(l_next, l_prev.len() as int, l_next.len() as int) >= 1,
{
  // From executor_progress:
  // - is_complete_tick_cycle(l_next, l_prev.len(), l_next.len())
  // - executor_inv(l_next)

  let start = l_prev.len() as int;
  let end = l_next.len() as int;
  let tick_end_idx = end - 1;

  // is_complete_tick_cycle ensures tick_end_idx is Tick::End
  assert(is_tick_end_at(l_next, tick_end_idx));

  // executor_inv includes action_safety_satisfied(tick_has_pop_injection)
  // This means: for all i, action_fn(l_next, i) ==> validity_fn(l_next, i)
  // action_fn = is_tick_end_at
  // validity_fn: exists p < i with PopInjection at p, no Tick::Begin between p and i
  assert(invariants::executor_inv(l_next));
  assert(invariants::executor_action_safety_inv(l_next));

  let thpi = invariants::tick_has_pop_injection::tick_has_pop_injection();
  assert(action_safety_satisfied(thpi, l_next));

  // action_fn(l_next, tick_end_idx) = is_tick_end_at(l_next, tick_end_idx) = true
  assert(invariants::tick_has_pop_injection::action_fn(l_next, tick_end_idx));

  // Trigger the implication: action_fn ==> validity_fn
  // Need to instantiate with (thpi.acceptance)(l_next, tick_end_idx)
  assert((thpi.acceptance)(l_next, tick_end_idx));
  assert((thpi.validity)(l_next, tick_end_idx));

  // validity_fn and (thpi.validity) are the same
  assert(invariants::tick_has_pop_injection::validity_fn(l_next, tick_end_idx));

  // validity_fn gives us a witness p with PopInjection
  let p: int = choose |p: int|
    0 <= p < tick_end_idx &&
    is_pop_injection_at(l_next, p) &&
    (forall |k: int| p < k < tick_end_idx ==> !is_tick_begin_at(l_next, k));

  // We need to show p >= start (i.e., the PopInjection is in the new content)
  // This follows from is_complete_tick_cycle: l_next[start] is Tick::Begin
  // and there's no Tick::Begin in (p, tick_end_idx)
  // If p < start, then start would be a Tick::Begin in (p, tick_end_idx), contradiction

  assert(is_tick_begin_at(l_next, start));  // from is_complete_tick_cycle

  if p < start {
    // start is in (p, tick_end_idx) since p < start < tick_end_idx
    assert(p < start && start < tick_end_idx);
    // But validity_fn says no Tick::Begin in (p, tick_end_idx)
    // This contradicts is_tick_begin_at(l_next, start)
    assert(!is_tick_begin_at(l_next, start));
    assert(false);
  }

  assert(start <= p);
  assert(p < end);
  assert(is_pop_injection_at(l_next, p));

  // Now we have a PopInjection at p in [start, end), so count >= 1
  // Need to prove count >= 1 by showing the count includes p
  count_includes_pop_at(l_next, start, end, p);
}

// Helper: If there's a PopInjection at p in [start, end), count >= 1
proof fn count_includes_pop_at(l: Log, start: int, end: int, p: int)
  requires
    0 <= start <= p && p < end && end <= l.len(),
    is_pop_injection_at(l, p),
  ensures
    count_pop_injection_between(l, start, end) >= 1,
  decreases end - start
{
  if start == p {
    // The first element is a PopInjection
    // count(start, end) = 1 + count(start+1, end) >= 1
    assert(count_pop_injection_between(l, start, end) >= 1);
  } else {
    // start < p, recurse
    count_includes_pop_at(l, start + 1, end, p);
    // count(start, end) = (is_pop(start)?1:0) + count(start+1, end) >= count(start+1, end) >= 1
  }
}

// Helper: Extract first step and remaining trace from progress_n
pub proof fn progress_n_decompose(l: Log, l_prime: Log, n: nat) -> (l_mid: Log)
  requires
    n >= 1,
    progress_n(executor_module_spec().progress, l, l_prime, n),
  ensures
    executor_progress(l, l_mid),
    is_prefix_of(l, l_mid),
    is_prefix_of(l_mid, l_prime),
    l_mid.len() > l.len(),
    n == 1 ==> l_mid == l_prime,
    n > 1 ==> progress_n(executor_module_spec().progress, l_mid, l_prime, (n - 1) as nat),
{
  let trace: Seq<Log> = choose |trace: Seq<Log>|
    #![trigger trace.len()]
    trace.len() == n + 1 &&
    trace.first() == l &&
    trace.last() == l_prime &&
    is_valid_trace(executor_module_spec().progress, trace);

  let l_mid: Log = trace[1];
  assert(executor_progress(l, l_mid));
  executor_progress_implies_prefix(l, l_mid);

  if n == 1 {
    assert(l_mid == l_prime);
  } else {
    // Build subtrace for remaining n-1 steps
    let subtrace = trace.subrange(1, trace.len() as int);
    assert(subtrace.len() == n);
    assert(subtrace.first() == l_mid);
    assert(subtrace.last() == l_prime);

    assert(is_valid_trace(executor_module_spec().progress, subtrace)) by {
      assert forall |i: int| 0 <= i < subtrace.len() - 1 implies
        (executor_module_spec().progress)(#[trigger] subtrace[i], subtrace[i + 1])
      by {
        assert(subtrace[i] == trace[i + 1]);
        assert(subtrace[i + 1] == trace[i + 2]);
      };
    };

    // Show is_prefix_of(l_mid, l_prime)
    progress_n_implies_prefix(l_mid, l_prime, (n - 1) as nat);
  }

  l_mid
}

// Helper: Count on a prefix equals count on extension (for same range)
// If l_short is a prefix of l_long, then count on l_short[start, end) equals
// count on l_long[start, end) when end <= l_short.len()
proof fn count_prefix_equals(l_short: Log, l_long: Log, start: int, end: int)
  requires
    is_prefix_of(l_short, l_long),
    0 <= start <= end,
    end <= l_short.len(),
  ensures
    count_pop_injection_between(l_short, start, end) ==
    count_pop_injection_between(l_long, start, end),
  decreases end - start
{
  if start >= end {
    // Empty range
  } else {
    // l_short[start] == l_long[start] since start < end <= l_short.len()
    assert(l_short[start] == l_long[start]);
    count_prefix_equals(l_short, l_long, start + 1, end);
  }
}

// Helper: n tick cycles produce at least n PopInjection events.
//
// This follows from TICK_HAS_POP_INJECTION: each complete tick cycle
// has at least one PopInjection event. With n tick cycles, we get >= n pops.
#[verifier::rlimit(50)]
pub proof fn n_ticks_yield_n_pops(l: Log, l_prime: Log, n: nat)
  requires
    is_prefix_of(l, l_prime),
    progress_n(executor_module_spec().progress, l, l_prime, n),
  ensures
    count_pop_injection_between(l_prime, l.len() as int, l_prime.len() as int) >= n,
  decreases n,
{
  if n == 0 {
    // Base case: 0 ticks, 0 pops needed
  } else if n == 1 {
    // Single step case
    let l_mid = progress_n_decompose(l, l_prime, n);
    single_progress_has_pop(l, l_mid);
    // l_mid == l_prime by ensures of progress_n_decompose
  } else {
    // Inductive case: n > 1
    let l_mid = progress_n_decompose(l, l_prime, n);

    // Step 1: single_progress_has_pop gives count(l_mid, l.len(), l_mid.len()) >= 1
    single_progress_has_pop(l, l_mid);

    // Step 2: Transfer count from l_mid to l_prime
    // Since l_mid is prefix of l_prime, count(l_mid, l.len(), l_mid.len()) ==
    // count(l_prime, l.len(), l_mid.len())
    count_prefix_equals(l_mid, l_prime, l.len() as int, l_mid.len() as int);

    // Step 3: IH gives count(l_prime, l_mid.len(), l_prime.len()) >= n-1
    n_ticks_yield_n_pops(l_mid, l_prime, (n - 1) as nat);

    // Step 4: Combine counts
    count_additivity_range(l_prime, l.len() as int, l_mid.len() as int, l_prime.len() as int);
    // count(l_prime, l.len(), l_prime.len()) =
    //   count(l_prime, l.len(), l_mid.len()) + count(l_prime, l_mid.len(), l_prime.len())
    //   >= 1 + (n-1) = n
  }
}

// Helper: Count additivity over disjoint ranges
// count(start, end) = count(start, mid) + count(mid, end)
pub proof fn count_additivity_range(l: Log, start: int, mid: int, end: int)
  requires
    0 <= start <= mid && mid <= end && end <= l.len(),
  ensures
    count_pop_injection_between(l, start, end) ==
    count_pop_injection_between(l, start, mid) + count_pop_injection_between(l, mid, end),
  decreases mid - start
{
  if start >= mid {
    // count(start, mid) = 0
    assert(count_pop_injection_between(l, start, mid) == 0 as nat);
  } else {
    // start < mid
    count_additivity_range(l, start + 1, mid, end);

    let is_pop_at_start = is_pop_injection_at(l, start);
    let delta: nat = if is_pop_at_start { 1 as nat } else { 0 as nat };

    // count(start, mid) = delta + count(start+1, mid)
    // count(start, end) = delta + count(start+1, end)
    // By IH: count(start+1, end) = count(start+1, mid) + count(mid, end)
    // So: count(start, end) = delta + count(start+1, mid) + count(mid, end)
    //                       = count(start, mid) + count(mid, end)
  }
}

pub proof fn pop_injection_adds_to_queue(l: Log, pop_idx: int, tid: TID)
  requires
    is_pop_injection_at(l, pop_idx),
    get_pop_injection_task(l[pop_idx]).is_some(),
    get_pop_injection_task(l[pop_idx]).unwrap().id == tid,
  ensures
    ({
      let queue = invariants::fifo_task_selection::fifo_queue_at(l, pop_idx + 1);
      exists |k: int| 0 <= k < queue.len() && queue[k] == tid
    }),
{
  // By definition of fifo_queue_at(l, pop_idx + 1):
  //   let prev_queue = fifo_queue_at(l, pop_idx);
  //   let e = l[pop_idx];
  //   if is_pop_injection(e) && get_pop_injection_task(e).is_some() {
  //     prev_queue.push(get_pop_injection_task(e).unwrap().id)
  //   }
  //
  // We have: l[pop_idx] is PopInjection with task.id == tid
  // So: fifo_queue_at(l, pop_idx + 1) = fifo_queue_at(l, pop_idx).push(tid)

  let queue_before = invariants::fifo_task_selection::fifo_queue_at(l, pop_idx);
  let queue_after = invariants::fifo_task_selection::fifo_queue_at(l, pop_idx + 1);
  let e = l[pop_idx];

  // Trigger the definition unfolding
  assert(is_pop_injection(e));
  assert(get_pop_injection_task(e).is_some());
  assert(get_pop_injection_task(e).unwrap().id == tid);

  // By definition: queue_after = queue_before.push(tid)
  assert(queue_after =~= queue_before.push(tid));

  // Therefore tid is at the last position
  let last_idx = (queue_after.len() - 1) as int;
  assert(0 <= last_idx < queue_after.len());
  assert(queue_after[last_idx] == tid);
}


// Helper: Find the next PollTask after start
spec fn next_poll_task_after(l: Log, start: int) -> int
  recommends start < l.len()
  decreases l.len() - start
{
  if start >= l.len() {
    l.len() as int  // sentinel: not found
  } else if is_poll_task_at(l, start) {
    start
  } else {
    next_poll_task_after(l, start + 1)
  }
}

proof fn non_empty_queue_has_entry_event(l: Log, i: int)
  requires
    0 <= i <= l.len(),
    ({
      let queue = invariants::fifo_task_selection::fifo_queue_at(l, i);
      queue.len() > 0
    }),
  ensures
    exists |j: int| #![trigger l[j]]
      0 <= j < i &&
      (
        (is_pop_injection_at(l, j) && get_pop_injection_task(l[j]).is_some()) ||
        (is_drain_at(l, j) && get_drain_task_ids(l[j]).len() > 0)
      ),
  decreases i
{
  let queue = invariants::fifo_task_selection::fifo_queue_at(l, i);

  if i <= 0 {
    // Base case: queue at 0 is empty, contradiction
    assert(queue.len() == 0);
    assert(false);
  } else {
    let prev_queue = invariants::fifo_task_selection::fifo_queue_at(l, i - 1);
    let e = l[i - 1];

    if is_pop_injection(e) && get_pop_injection_task(e).is_some() {
      // Event at i-1 adds a task, we found our witness
      assert(is_pop_injection_at(l, i - 1));
      assert(get_pop_injection_task(l[i - 1]).is_some());
    } else if is_drain(e) && get_drain_task_ids(e).len() > 0 {
      // Event at i-1 adds tasks via drain
      assert(is_drain_at(l, i - 1));
      assert(get_drain_task_ids(l[i - 1]).len() > 0);
    } else if is_poll_task(e) {
      // PollTask removes one from queue (if present)
      // prev_queue.len() >= queue.len()
      // Since queue.len() > 0, prev_queue must have had at least one element
      // (because remove_first_occurrence can only reduce or maintain length)
      // So prev_queue.len() > 0, and we recurse
      //
      // Note: remove_first_occurrence(s, tid) has len(s) - 1 if tid in s, else len(s)
      // Since queue.len() > 0, prev_queue.len() >= queue.len() > 0 or prev_queue had the tid
      // Either way, prev_queue.len() > 0

      // If prev_queue was empty, queue would be empty (contradiction)
      if prev_queue.len() == 0 {
        // remove_first_occurrence on empty queue is empty
        assert(queue.len() == 0);
        assert(false);
      }
      non_empty_queue_has_entry_event(l, i - 1);
    } else {
      // Other event doesn't change queue
      assert(queue =~= prev_queue);
      assert(prev_queue.len() > 0);
      non_empty_queue_has_entry_event(l, i - 1);
    }
  }
}

// Helper: Non-PollTask events preserve queue head
// PopInjection appends to end, Drain appends to end, other events don't change queue
proof fn non_poll_event_preserves_head(l: Log, i: int, head: TID)
  requires
    0 <= i < l.len(),
    !is_poll_task_at(l, i),
    ({
      let queue = invariants::fifo_task_selection::fifo_queue_at(l, i);
      queue.len() > 0 && queue[0] == head
    }),
  ensures
    ({
      let queue_after = invariants::fifo_task_selection::fifo_queue_at(l, i + 1);
      queue_after.len() > 0 && queue_after[0] == head
    }),
{
  let queue_before = invariants::fifo_task_selection::fifo_queue_at(l, i);
  let queue_after = invariants::fifo_task_selection::fifo_queue_at(l, i + 1);
  let e = l[i];

  // By definition of fifo_queue_at:
  // - PopInjection(Some): prev.push(tid) - appends to end, preserves head
  // - Drain: prev + tids - appends to end, preserves head
  // - PollTask: removes head - but we excluded this case
  // - Other: no change

  if is_pop_injection(e) && get_pop_injection_task(e).is_some() {
    // queue_after = queue_before.push(new_tid)
    // Head is preserved
    assert(queue_after =~= queue_before.push(get_pop_injection_task(e).unwrap().id));
    assert(queue_after[0] == queue_before[0]);
  } else if is_drain(e) {
    // queue_after = queue_before + tids
    // Head is preserved
    let tids = get_drain_task_ids(e);
    assert(queue_after =~= queue_before + tids);
    assert(queue_after[0] == queue_before[0]);
  } else if is_poll_task(e) {
    // Excluded by precondition
    assert(false);
  } else {
    // queue_after = queue_before
    assert(queue_after =~= queue_before);
  }
}

// Helper: Queue head is preserved across a range with no PollTask
pub proof fn queue_head_preserved_in_range(l: Log, start: int, end: int, head: TID)
  requires
    0 <= start <= end,
    end <= l.len(),
    // No PollTask in [start, end)
    forall |j: int| start <= j < end ==> !#[trigger] is_poll_task_at(l, j),
    // Queue at start has head
    ({
      let queue = invariants::fifo_task_selection::fifo_queue_at(l, start);
      queue.len() > 0 && queue[0] == head
    }),
  ensures
    ({
      let queue = invariants::fifo_task_selection::fifo_queue_at(l, end);
      queue.len() > 0 && queue[0] == head
    }),
  decreases end - start
{
  if start >= end {
    // Base case: trivial
  } else {
    // Step: show head is preserved at start, then recurse
    // No PollTask at start, so head is preserved to start+1
    non_poll_event_preserves_head(l, start, head);

    // Recurse for [start+1, end)
    if start + 1 < end {
      queue_head_preserved_in_range(l, start + 1, end, head);
    }
  }
}

// Helper: Find the first PollTask in a range [start, end)
// Returns the index, or -1 if none exists
pub open spec fn find_first_poll_task(l: Log, start: int, end: int) -> int
  decreases end - start
{
  if start >= end {
    -1
  } else if is_poll_task_at(l, start) {
    start
  } else {
    find_first_poll_task(l, start + 1, end)
  }
}

// Helper: If there's a PollTask in [start, end), find_first_poll_task returns a valid index
pub proof fn find_first_poll_task_valid(l: Log, start: int, end: int)
  requires
    0 <= start,
    end <= l.len(),
    exists |j: int| start <= j < end && is_poll_task_at(l, j),
  ensures
    ({
      let idx = find_first_poll_task(l, start, end);
      start <= idx && idx < end &&
      is_poll_task_at(l, idx) &&
      // No PollTask before idx in [start, idx)
      forall |k: int| start <= k < idx ==> !#[trigger] is_poll_task_at(l, k)
    }),
  decreases end - start
{
  if start >= end {
    // Contradiction: no PollTask possible in empty range
    assert(false);
  } else if is_poll_task_at(l, start) {
    // start is the first PollTask
    let idx = find_first_poll_task(l, start, end);
    assert(idx == start);
  } else {
    // Recurse
    // Since exists j in [start, end) with PollTask, and start is not PollTask,
    // exists j in [start+1, end) with PollTask
    find_first_poll_task_valid(l, start + 1, end);
  }
}

// Helper: First PollTask in a range polls the queue head at that position
pub proof fn first_poll_polls_head(l: Log, poll_idx: int, range_start: int)
  requires
    invariants::executor_inv(l),
    range_start <= poll_idx < l.len(),
    is_poll_task_at(l, poll_idx),
    // No PollTask before poll_idx in the range
    forall |j: int| range_start <= j < poll_idx ==> !#[trigger] is_poll_task_at(l, j),
  ensures
    // The queue at poll_idx has the same head as at range_start
    // (because no PollTask happened between to change it)
    ({
      let queue_at_start = invariants::fifo_task_selection::fifo_queue_at(l, range_start);
      let queue_at_poll = invariants::fifo_task_selection::fifo_queue_at(l, poll_idx);
      queue_at_start.len() > 0 ==>
        (queue_at_poll.len() > 0 && queue_at_poll[0] == queue_at_start[0])
    }),
{
  let queue_at_start = invariants::fifo_task_selection::fifo_queue_at(l, range_start);

  if queue_at_start.len() == 0 {
    // Trivially true - antecedent is false
  } else {
    let head = queue_at_start[0];
    // Use helper to show head is preserved from range_start to poll_idx
    queue_head_preserved_in_range(l, range_start, poll_idx, head);
  }
}

}
