use vstd::prelude::*;
use crate::reactor::spec::log as reactor_log;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::events::{is_get_current_time, get_current_timestamp};
#[cfg(verus_keep_ghost)]
use crate::composed::spec::state::{ComposedState, empty_composed_state};
#[cfg(verus_keep_ghost)]
use crate::composed::spec::progress::{composed_progress, composed_well_formed};

verus! {

pub open spec fn max_gct_timestamp(l: reactor_log::Log) -> int
  decreases l.len()
{
  if l.len() == 0 {
    0
  } else {
    let prev = max_gct_timestamp(l.subrange(0, l.len() - 1));
    let last = l[l.len() - 1];
    if is_get_current_time(last) && get_current_timestamp(last) > prev {
      get_current_timestamp(last)
    } else {
      prev
    }
  }
}

// max_gct_timestamp is >= 0 always.
pub proof fn max_gct_nonneg(l: reactor_log::Log)
  ensures
    max_gct_timestamp(l) >= 0,
  decreases l.len()
{
  if l.len() == 0 {
  } else {
    max_gct_nonneg(l.subrange(0, l.len() - 1));
  }
}

// Every GetCurrentTime timestamp in l is <= max_gct_timestamp(l).
pub proof fn max_gct_bounds(l: reactor_log::Log, i: int)
  requires
    0 <= i < l.len(),
    reactor_log::is_get_current_time_at(l, i),
  ensures
    get_current_timestamp(l[i]) <= max_gct_timestamp(l),
  decreases l.len()
{
  if l.len() == 0 {
  } else {
    let last_idx = l.len() - 1;
    if i == last_idx {
      // last element; by definition max >= its timestamp
    } else {
      let l_pre = l.subrange(0, last_idx);
      assert(l_pre.len() == last_idx);
      assert(l_pre[i] == l[i]);
      assert(reactor_log::is_get_current_time_at(l_pre, i));
      max_gct_bounds(l_pre, i);
      // max_gct_timestamp(l) >= max_gct_timestamp(l_pre) >= ts(l[i])
      max_gct_nonneg(l_pre);
    }
  }
}

}
