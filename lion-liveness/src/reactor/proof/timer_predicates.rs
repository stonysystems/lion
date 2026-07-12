use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::log::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::events::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::types::*;

verus! {

pub open spec fn is_timeout_point(l: Log, register_idx: int, timeout_idx: int) -> bool
  recommends is_succ_register_timer_at(l, register_idx)
{
  let deadline = get_register_timer_deadline(l[register_idx]);
  register_idx < timeout_idx < l.len() &&
  is_get_current_time_at(l, timeout_idx) &&
  get_current_timestamp(l[timeout_idx]) >= deadline &&
  timer_active_at(l, register_idx, timeout_idx) &&
  is_first_timeout_point(l, register_idx, timeout_idx)
}

pub open spec fn is_first_timeout_point(l: Log, register_idx: int, timeout_idx: int) -> bool
  recommends is_succ_register_timer_at(l, register_idx)
{
  let deadline = get_register_timer_deadline(l[register_idx]);
  forall |j: int|
    register_idx < j < timeout_idx &&
    is_get_current_time_at(l, j) ==>
    get_current_timestamp(#[trigger] l[j]) < deadline
}

}
