use vstd::prelude::*;
#[allow(unused_imports)]
use crate::composed::spec::state::*;
#[allow(unused_imports)]
use crate::composed::spec::types::*;
#[allow(unused_imports)]
use crate::composed::spec::progress::*;
#[allow(unused_imports)]
use crate::composed::spec::alignment::*;
#[allow(unused_imports)]
use crate::executor::spec::log as executor_log;
#[allow(unused_imports)]
use crate::reactor::spec::log as reactor_log;

verus! {

proof fn count_park_events_includes_park(l: executor_log::Log, start: int, end: int, park_idx: int)
  requires
    start >= 0,
    end <= l.len(),
    start <= park_idx < end,
    executor_log::is_park_at(l, park_idx),
  ensures
    count_park_events_in(l, start, end) >= 1,
  decreases end - start
{
  if start == park_idx {
    assert(executor_log::is_park_at(l, start));
    assert(count_park_events_in(l, start, end) == 1 + count_park_events_in(l, start + 1, end));
  } else {
    count_park_events_includes_park(l, start + 1, end, park_idx);
  }
}

}
