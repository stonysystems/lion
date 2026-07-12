pub mod spec;
pub mod invariants;
pub mod contracts;
pub mod proof;

use vstd::prelude::*;
use crate::executor::spec::log::*;
use crate::executor::spec::events::*;
use crate::framework::module_spec::ModuleSpec;

verus! {

pub open spec fn is_complete_tick_cycle(l: Log, start: int, end: int) -> bool {
  0 <= start < end && end <= l.len() &&
  is_tick_begin_at(l, start) &&
  is_tick_end_at(l, end - 1) &&
  (forall |k: int| start < k < end - 1 ==>
    !#[trigger] is_tick_begin_at(l, k) && !is_tick_end_at(l, k))
}

pub open spec fn executor_progress(l: Log, l_prime: Log) -> bool {
  l_prime.len() > l.len() &&
  l =~= l_prime.subrange(0, l.len() as int) &&
  is_complete_tick_cycle(l_prime, l.len() as int, l_prime.len() as int) &&
  invariants::executor_inv(l_prime)
}

pub open spec fn executor_module_spec() -> ModuleSpec<Log> {
  ModuleSpec {
    well_formed: |l: Log| invariants::executor_inv(l),
    progress: |l: Log, l_prime: Log| executor_progress(l, l_prime),
  }
}

}
