pub mod spec;
pub mod invariants;
pub mod contracts;
pub mod proof;

use vstd::prelude::*;
use crate::reactor::spec::log::*;
use crate::reactor::spec::events::*;
use crate::reactor::spec::types::*;
use crate::framework::module_spec::ModuleSpec;

verus! {

// ============================================================================
// Park Cycle Definition
// ============================================================================

pub open spec fn is_complete_park_cycle(l: Log, start: int, end: int) -> bool {
  0 <= start < end && end <= l.len() &&
  is_park_begin_at(l, start) &&
  is_park_end_at(l, end - 1) &&
  (forall |k: int| start < k < end - 1 ==>
    !#[trigger] is_park_begin_at(l, k) && !is_park_end_at(l, k))
}

// ============================================================================
// Progress Definition
// ============================================================================

pub open spec fn reactor_progress(l: Log, l_prime: Log) -> bool {
  l_prime.len() > l.len() &&
  l =~= l_prime.subrange(0, l.len() as int) &&
  (exists |park_start: int, park_end: int|
    l.len() as int <= park_start &&
    park_start < park_end &&
    park_end <= l_prime.len() as int &&
    is_complete_park_cycle(l_prime, park_start, park_end) &&
    (forall |i: int| l.len() as int <= i < park_start ==>
      is_inbound_non_park(#[trigger] l_prime[i])) &&
    (forall |i: int| park_end <= i < l_prime.len() as int ==>
      is_inbound_non_park(#[trigger] l_prime[i]))
  ) &&
  invariants::reactor_inv(l_prime)
}

// ============================================================================
// Module Specification
// ============================================================================

pub open spec fn reactor_module_spec() -> ModuleSpec<Log> {
  ModuleSpec {
    well_formed: |l: Log| invariants::reactor_inv(l),
    progress: |l: Log, l_prime: Log| reactor_progress(l, l_prime),
  }
}

// ============================================================================
// Model Assumptions (External to reactor_inv)
// ============================================================================

// Moved to the shared crate (consumed by the shared bounded contracts);
// re-exported to keep the crate::reactor:: paths.
pub use lion_reactor_spec::log::timestamps_strictly_increasing;
pub use lion_reactor_spec::log::timestamps_positive;

}
