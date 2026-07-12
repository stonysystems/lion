use vstd::prelude::*;
use crate::executor::spec::log::*;
use crate::executor::spec::events::*;
use crate::executor::spec::types::*;
use crate::executor::invariants;
use crate::framework::action_safety::*;

verus! {

// ============================================================================
// Action Safety Prefix Monotonicity Lemmas
// ============================================================================
//
// These lemmas prove that ActionSafety properties are prefix-monotonic:
// if the property holds for log l, it also holds for actions in [0, l.len())
// when l is extended to l'.
//
// Key insight:
// - action predicates are "index-local" (only read l[i])
// - validity predicates are "backward-looking" (only read l[0..i])
// Since l[k] == l'[k] for k < l.len(), both predicates behave identically.

// ============================================================================
// Helper: Events equality for prefix
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
// tick_has_park prefix monotonicity
// ============================================================================

proof fn fifo_queue_prefix_equiv(l: Log, l_prime: Log, i: int)
  requires
    is_prefix_of(l, l_prime),
    0 <= i <= l.len(),
  ensures
    invariants::fifo_task_selection::fifo_queue_at(l, i) ==
    invariants::fifo_task_selection::fifo_queue_at(l_prime, i),
  decreases i
{
  if i <= 0 {
    // Base case: empty queue
  } else {
    fifo_queue_prefix_equiv(l, l_prime, i - 1);
    prefix_events_equal(l, l_prime, i - 1);
    // l[i-1] == l'[i-1], so the queue update is identical
  }
}

}
