use vstd::prelude::*;
use crate::executor::spec::log::*;
use crate::executor::spec::events::*;
use crate::executor::invariants;
use crate::framework::local_liveness::*;

verus! {

// ============================================================================
// Prefix Monotonicity Lemmas for Specific LocalLiveness Properties
// ============================================================================
//
// These lemmas prove that our specific LocalLiveness properties are
// prefix-monotonic: if the property holds for log l, it also holds for
// triggers in [0, l.len()) when l is extended to l'.
//
// Key insight: Our trigger/response/timely predicates are "index-local" -
// they only read events at specific indices. Since l[i] == l'[i] for i < l.len(),
// the predicates behave identically on both logs for indices in [0, l.len()).

// ============================================================================
// Fundamental prefix property helpers
// ============================================================================

proof fn prefix_events_equal(l: Log, l_prime: Log, i: int)
  requires
    is_prefix_of(l, l_prime),
    0 <= i < l.len(),
  ensures
    l[i] == l_prime[i],
{
  assert(l =~= l_prime.subrange(0, l.len() as int));
  assert(l[i] == l_prime.subrange(0, l.len() as int)[i]);
}

// ============================================================================
// FIFO queue state prefix invariant
// ============================================================================
//
// fifo_queue_at(l, i) only depends on events [0, i), so if l is prefix of l',
// fifo_queue_at(l, i) == fifo_queue_at(l', i) for i <= l.len().

pub proof fn fifo_queue_at_prefix_equals(l: Log, l_prime: Log, i: int)
  requires
    is_prefix_of(l, l_prime),
    0 <= i <= l.len(),
  ensures
    invariants::fifo_task_selection::fifo_queue_at(l, i) =~=
    invariants::fifo_task_selection::fifo_queue_at(l_prime, i),
  decreases i
{
  if i <= 0 {
    // Base case: both return empty sequence
  } else {
    // Recursive case: compare events at i-1
    fifo_queue_at_prefix_equals(l, l_prime, i - 1);

    // Events at i-1 are equal
    assert(i - 1 < l.len());
    prefix_events_equal(l, l_prime, i - 1);
    assert(l[i - 1] == l_prime[i - 1]);

    // The recursive definition depends on l[i-1], which is equal
    // So the result is the same
  }
}

// ============================================================================
// Timely predicate transfer (no tick_end between i and j)
// ============================================================================

}
