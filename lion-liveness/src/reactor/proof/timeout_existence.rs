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
use crate::reactor::timestamps_strictly_increasing;
#[cfg(verus_keep_ghost)]
use crate::reactor::timestamps_positive;
#[cfg(verus_keep_ghost)]
use super::timer_predicates::*;
#[cfg(verus_keep_ghost)]
use super::round_extension::*;

verus! {

pub open spec fn find_first_timestamp_ge_deadline(
  l: Log,
  start: int,
  deadline: InstantView
) -> int
  decreases l.len() - start
{
  if start >= l.len() {
    -1
  } else if is_get_current_time_at(l, start) && get_current_timestamp(l[start]) >= deadline {
    start
  } else {
    find_first_timestamp_ge_deadline(l, start + 1, deadline)
  }
}

proof fn strictly_increasing_implies_lower_bound(l: Log, i: int, j: int)
  requires
    timestamps_strictly_increasing(l),
    0 <= i < j < l.len(),
    is_get_current_time_at(l, i),
    is_get_current_time_at(l, j),
  ensures
    get_current_timestamp(l[j]) > get_current_timestamp(l[i]),
{
  let ts_i = get_current_timestamp(l[i]);
  let ts_j = get_current_timestamp(l[j]);
  assert(ts_i < ts_j);
}

proof fn count_range_shrink(l: Log, start: int, end: int)
  requires
    0 <= start < end <= l.len(),
    !is_get_current_time_at(l, end - 1),
  ensures
    count_get_current_time_in_range(l, start, end) == count_get_current_time_in_range(l, start, end - 1),
  decreases end - start
{
  if start == end - 1 {
    assert(!is_get_current_time_at(l, start));
    assert(count_get_current_time_in_range(l, start, end) == count_get_current_time_in_range(l, start + 1, end));
    assert(count_get_current_time_in_range(l, start + 1, end) == 0);
    assert(count_get_current_time_in_range(l, start, end - 1) == 0);
  } else {
    count_range_shrink(l, start + 1, end);
    if is_get_current_time_at(l, start) {
      assert(count_get_current_time_in_range(l, start, end) == 1 + count_get_current_time_in_range(l, start + 1, end));
      assert(count_get_current_time_in_range(l, start, end - 1) == 1 + count_get_current_time_in_range(l, start + 1, end - 1));
    } else {
      assert(count_get_current_time_in_range(l, start, end) == count_get_current_time_in_range(l, start + 1, end));
      assert(count_get_current_time_in_range(l, start, end - 1) == count_get_current_time_in_range(l, start + 1, end - 1));
    }
  }
}

proof fn find_last_timestamp_before(l: Log, end: int) -> (idx: int)
  requires
    0 < end <= l.len(),
    count_get_current_time_in_range(l, 0, end) >= 1,
  ensures
    0 <= idx < end,
    is_get_current_time_at(l, idx),
    forall |i: int| idx < i < end ==> !is_get_current_time_at(l, i),
  decreases end
{
  if is_get_current_time_at(l, end - 1) {
    assert forall |i: int| end - 1 < i < end implies !is_get_current_time_at(l, i) by {
      // vacuously true: no i satisfies end - 1 < i < end
    };
    end - 1
  } else {
    count_range_shrink(l, 0, end);
    let result = find_last_timestamp_before(l, end - 1);
    assert forall |i: int| result < i < end implies !is_get_current_time_at(l, i) by {
      if i == end - 1 {
        assert(!is_get_current_time_at(l, end - 1));
      } else {
        assert(result < i < end - 1);
        // From recursive call's postcondition
      }
    };
    result
  }
}

proof fn first_ts_in_range_greater_than_before(
  l: Log,
  start: int,
  end: int,
  base_ts: InstantView,
)
  requires
    timestamps_strictly_increasing(l),
    timestamps_positive(l),
    0 < start <= end <= l.len(),
    count_get_current_time_in_range(l, start, end) >= 1,
    count_get_current_time_in_range(l, 0, start) >= 1,
    base_ts == max_timestamp_up_to(l, start),
  ensures
    forall |ts_idx: int| start <= ts_idx < end && is_get_current_time_at(l, ts_idx) ==>
      get_current_timestamp(#[trigger] l[ts_idx]) > base_ts,
{
  let prev_idx = find_last_timestamp_before(l, start);
  let prev_ts = get_current_timestamp(l[prev_idx]);
  assert(0 <= prev_idx < start);
  assert(is_get_current_time_at(l, prev_idx));

  last_ts_equals_max(l, start, prev_idx);
  assert(prev_ts == base_ts);

  assert forall |ts_idx: int| start <= ts_idx < end && is_get_current_time_at(l, ts_idx)
    implies get_current_timestamp(#[trigger] l[ts_idx]) > base_ts by {
    strictly_increasing_implies_lower_bound(l, prev_idx, ts_idx);
    assert(get_current_timestamp(l[ts_idx]) > prev_ts);
    assert(prev_ts == base_ts);
  };
}

proof fn last_ts_equals_max(
  l: Log,
  end: int,
  last_ts_idx: int,
)
  requires
    timestamps_strictly_increasing(l),
    timestamps_positive(l),
    0 < end <= l.len(),
    0 <= last_ts_idx < end,
    is_get_current_time_at(l, last_ts_idx),
    forall |i: int| last_ts_idx < i < end ==> !is_get_current_time_at(l, i),
  ensures
    get_current_timestamp(l[last_ts_idx]) == max_timestamp_up_to(l, end),
  decreases end - last_ts_idx - 1
{
  let last_ts = get_current_timestamp(l[last_ts_idx]);
  if last_ts_idx == end - 1 {
    assert(is_get_current_time_at(l, end - 1));
    let prev_max = max_timestamp_up_to(l, end - 1);
    if last_ts_idx > 0 {
      last_ts_greater_than_prev_max(l, end, last_ts_idx);
      assert(last_ts > prev_max);
      assert(max_timestamp_up_to(l, end) == last_ts);
    } else {
      assert(last_ts_idx == 0);
      assert(end == 1);
      assert(prev_max == max_timestamp_up_to(l, 0));
      assert(prev_max == 0);
      assert(last_ts >= 1);
      assert(last_ts > prev_max);
      assert(max_timestamp_up_to(l, end) == last_ts);
    }
  } else {
    assert(!is_get_current_time_at(l, end - 1));
    last_ts_equals_max(l, end - 1, last_ts_idx);
    assert(last_ts == max_timestamp_up_to(l, end - 1));
  }
}

proof fn ts_greater_than_all_before(
  l: Log,
  last_ts_idx: int,
)
  requires
    timestamps_strictly_increasing(l),
    0 <= last_ts_idx < l.len(),
    is_get_current_time_at(l, last_ts_idx),
  ensures
    forall |i: int| 0 <= i < last_ts_idx && is_get_current_time_at(l, i) ==>
      get_current_timestamp(#[trigger] l[i]) < get_current_timestamp(l[last_ts_idx]),
{
  let last_ts = get_current_timestamp(l[last_ts_idx]);
  assert forall |i: int| 0 <= i < last_ts_idx && is_get_current_time_at(l, i)
    implies get_current_timestamp(#[trigger] l[i]) < last_ts by {
    strictly_increasing_implies_lower_bound(l, i, last_ts_idx);
  };
}

proof fn max_ts_is_some_ts_or_zero(l: Log, end: int) -> (result: Option<int>)
  requires
    0 <= end <= l.len(),
  ensures
    match result {
      None => max_timestamp_up_to(l, end) == 0,
      Some(idx) => {
        0 <= idx < end &&
        is_get_current_time_at(l, idx) &&
        get_current_timestamp(l[idx]) == max_timestamp_up_to(l, end)
      },
    },
  decreases end
{
  if end == 0 {
    None
  } else if is_get_current_time_at(l, end - 1) {
    let ts = get_current_timestamp(l[end - 1]);
    let prev = max_ts_is_some_ts_or_zero(l, end - 1);
    let prev_max = max_timestamp_up_to(l, end - 1);
    if ts > prev_max {
      Some(end - 1)
    } else {
      match prev {
        None => {
          assert(prev_max == 0);
          assert(ts <= 0);
          if ts >= 0 {
            Some(end - 1)
          } else {
            None
          }
        },
        Some(idx) => {
          assert(get_current_timestamp(l[idx]) == prev_max);
          assert(prev_max >= ts);
          assert(max_timestamp_up_to(l, end) == prev_max);
          Some(idx)
        },
      }
    }
  } else {
    max_ts_is_some_ts_or_zero(l, end - 1)
  }
}

proof fn last_ts_greater_than_prev_max(
  l: Log,
  end: int,
  last_ts_idx: int,
)
  requires
    timestamps_strictly_increasing(l),
    timestamps_positive(l),
    0 < end <= l.len(),
    0 <= last_ts_idx < end,
    is_get_current_time_at(l, last_ts_idx),
  ensures
    last_ts_idx > 0 ==> get_current_timestamp(l[last_ts_idx]) > max_timestamp_up_to(l, last_ts_idx),
  decreases last_ts_idx
{
  if last_ts_idx == 0 {
    // trivial, implication is vacuously true
  } else {
    let last_ts = get_current_timestamp(l[last_ts_idx]);
    let prev_max = max_timestamp_up_to(l, last_ts_idx);

    ts_greater_than_all_before(l, last_ts_idx);

    let result = max_ts_is_some_ts_or_zero(l, last_ts_idx);
    match result {
      None => {
        assert(prev_max == 0);
        assert(last_ts >= 1);
        assert(last_ts > 0);
      },
      Some(idx) => {
        assert(get_current_timestamp(l[idx]) == prev_max);
        assert(0 <= idx < last_ts_idx);
        assert(is_get_current_time_at(l, idx));
        assert(get_current_timestamp(l[idx]) < last_ts);
        assert(prev_max < last_ts);
      },
    };
  }
}


proof fn find_first_timestamp_in_range(l: Log, start: int, end: int) -> (idx: int)
  requires
    0 <= start <= end <= l.len(),
    count_get_current_time_in_range(l, start, end) >= 1,
  ensures
    start <= idx < end,
    is_get_current_time_at(l, idx),
    forall |j: int| start <= j < idx ==> !is_get_current_time_at(l, j),
  decreases end - start
{
  if is_get_current_time_at(l, start) {
    start
  } else {
    find_first_timestamp_in_range(l, start + 1, end)
  }
}


proof fn count_positive_implies_exists_timestamp(l: Log, start: int, end: int)
  requires
    0 <= start <= end <= l.len(),
    count_get_current_time_in_range(l, start, end) >= 1,
  ensures
    exists |idx: int| start <= idx < end && is_get_current_time_at(l, idx),
  decreases end - start
{
  if is_get_current_time_at(l, start) {
    assert(start >= start && start < end && is_get_current_time_at(l, start));
  } else {
    count_positive_implies_exists_timestamp(l, start + 1, end);
  }
}

proof fn timestamp_implies_count_ge_one(l: Log, ts_idx: int)
  requires
    0 <= ts_idx < l.len(),
    is_get_current_time_at(l, ts_idx),
  ensures
    count_get_current_time_in_range(l, 0, ts_idx + 1) >= 1,
  decreases ts_idx
{
  count_ge_one_if_exists(l, 0, ts_idx + 1, ts_idx);
}

proof fn count_ge_one_if_exists(l: Log, start: int, end: int, ts_idx: int)
  requires
    0 <= start <= ts_idx,
    ts_idx < end <= l.len(),
    is_get_current_time_at(l, ts_idx),
  ensures
    count_get_current_time_in_range(l, start, end) >= 1,
  decreases ts_idx - start
{
  if start == ts_idx {
    assert(is_get_current_time_at(l, start));
  } else {
    count_ge_one_if_exists(l, start + 1, end, ts_idx);
  }
}

proof fn count_decreases_after_timestamp(l: Log, start: int, end: int, ts_idx: int)
  requires
    0 <= start <= ts_idx,
    ts_idx < end <= l.len(),
    is_get_current_time_at(l, ts_idx),
    forall |j: int| start <= j < ts_idx ==> !is_get_current_time_at(l, j),
  ensures
    count_get_current_time_in_range(l, start, end) ==
      1 + count_get_current_time_in_range(l, ts_idx + 1, end),
  decreases ts_idx - start
{
  if start == ts_idx {
    assert(is_get_current_time_at(l, start));
  } else {
    assert(!is_get_current_time_at(l, start));
    count_decreases_after_timestamp(l, start + 1, end, ts_idx);
  }
}

proof fn count_shrink_no_ts(l: Log, end: int)
  requires
    0 < end <= l.len(),
    !is_get_current_time_at(l, end - 1),
    count_get_current_time_in_range(l, 0, end) == 0,
  ensures
    count_get_current_time_in_range(l, 0, end - 1) == 0,
{
  count_range_shrink(l, 0, end);
}

proof fn no_ts_implies_max_zero(l: Log, end: int)
  requires
    0 <= end <= l.len(),
    count_get_current_time_in_range(l, 0, end) == 0,
  ensures
    max_timestamp_up_to(l, end) == 0,
  decreases end
{
  if end == 0 {
  } else {
    if is_get_current_time_at(l, end - 1) {
      count_ge_one_if_exists(l, 0, end, end - 1);
      assert(count_get_current_time_in_range(l, 0, end) >= 1);
      assert(false);
    } else {
      count_shrink_no_ts(l, end);
      no_ts_implies_max_zero(l, end - 1);
    }
  }
}

proof fn count_is_non_negative(l: Log, start: int, end: int)
  requires
    0 <= start <= end <= l.len(),
  ensures
    count_get_current_time_in_range(l, start, end) >= 0,
  decreases end - start
{
  if start >= end {
  } else {
    count_is_non_negative(l, start + 1, end);
  }
}

proof fn nth_timestamp_at_least(
  l: Log,
  start: int,
  end: int,
  base_ts: InstantView,
  n: nat,
) -> (ts_idx: int)
  requires
    timestamps_strictly_increasing(l),
    timestamps_positive(l),
    0 <= start <= end <= l.len(),
    count_get_current_time_in_range(l, start, end) >= n,
    n >= 1,
    base_ts == max_timestamp_up_to(l, start),
  ensures
    start <= ts_idx < end,
    is_get_current_time_at(l, ts_idx),
    get_current_timestamp(l[ts_idx]) >= base_ts + (n as int),
  decreases n
{
  let first_ts_idx = find_first_timestamp_in_range(l, start, end);
  let first_ts = get_current_timestamp(l[first_ts_idx]);

  let prev_count = count_get_current_time_in_range(l, 0, start);

  if n == 1 {
    if prev_count >= 1 {
      first_ts_in_range_greater_than_before(l, start, end, base_ts);
      assert(first_ts > base_ts);
      assert(first_ts >= base_ts + 1);
    } else {
      assert(prev_count == 0) by {
        count_is_non_negative(l, 0, start);
      };
      no_ts_implies_max_zero(l, start);
      assert(base_ts == 0);
      assert(first_ts >= 1);
      assert(first_ts >= base_ts + 1);
    }
    first_ts_idx
  } else {
    count_decreases_after_timestamp(l, start, end, first_ts_idx);

    if prev_count >= 1 {
      first_ts_in_range_greater_than_before(l, start, end, base_ts);
      assert(first_ts > base_ts);
      assert(first_ts >= base_ts + 1);
    } else {
      assert(prev_count == 0) by {
        count_is_non_negative(l, 0, start);
      };
      no_ts_implies_max_zero(l, start);
      assert(base_ts == 0);
      assert(first_ts >= 1);
      assert(first_ts >= base_ts + 1);
    }

    timestamp_implies_count_ge_one(l, first_ts_idx);
    assert(count_get_current_time_in_range(l, 0, first_ts_idx + 1) >= 1);

    first_ts_is_new_max(l, start, first_ts_idx, base_ts);

    let result = nth_timestamp_at_least(
      l,
      first_ts_idx + 1,
      end,
      first_ts,
      (n - 1) as nat
    );
    assert(get_current_timestamp(l[result]) >= first_ts + ((n - 1) as int));
    assert(first_ts + ((n - 1) as int) >= base_ts + 1 + ((n - 1) as int));
    assert(base_ts + 1 + ((n - 1) as int) == base_ts + (n as int));
    result
  }
}

pub proof fn no_ts_in_range_same_max(l: Log, start: int, end: int)
  requires
    0 <= start <= end <= l.len(),
    forall |j: int| start <= j < end ==> !is_get_current_time_at(l, j),
  ensures
    max_timestamp_up_to(l, start) == max_timestamp_up_to(l, end),
  decreases end - start
{
  if start == end {
    // trivial
  } else {
    no_ts_in_range_same_max(l, start, end - 1);
    assert(!is_get_current_time_at(l, end - 1));
  }
}

proof fn first_ts_is_new_max(
  l: Log,
  start: int,
  first_ts_idx: int,
  base_ts: InstantView,
)
  requires
    timestamps_strictly_increasing(l),
    timestamps_positive(l),
    0 <= start <= first_ts_idx,
    first_ts_idx < l.len(),
    is_get_current_time_at(l, first_ts_idx),
    forall |j: int| start <= j < first_ts_idx ==> !is_get_current_time_at(l, j),
    start > 0 ==> base_ts == max_timestamp_up_to(l, start),
  ensures
    get_current_timestamp(l[first_ts_idx]) == max_timestamp_up_to(l, first_ts_idx + 1),
{
  let first_ts = get_current_timestamp(l[first_ts_idx]);

  no_ts_in_range_same_max(l, start, first_ts_idx);
  assert(max_timestamp_up_to(l, start) == max_timestamp_up_to(l, first_ts_idx));

  let prev_max = max_timestamp_up_to(l, first_ts_idx);

  if first_ts_idx > 0 {
    last_ts_greater_than_prev_max(l, first_ts_idx + 1, first_ts_idx);
    assert(first_ts > prev_max);
    assert(max_timestamp_up_to(l, first_ts_idx + 1) == first_ts);
  } else {
    assert(first_ts_idx == 0);
    assert(prev_max == 0);
    assert(first_ts >= 1);
    assert(first_ts > prev_max);
    assert(max_timestamp_up_to(l, first_ts_idx + 1) == first_ts);
  }
}

pub proof fn max_timestamp_on_prefix_eq(l: Log, l_prime: Log, end: int)
  requires
    is_prefix_of(l, l_prime),
    0 <= end <= l.len(),
  ensures
    max_timestamp_up_to(l, end) == max_timestamp_up_to(l_prime, end),
  decreases end
{
  if end <= 0 {
    // Both are 0
  } else {
    max_timestamp_on_prefix_eq(l, l_prime, end - 1);
    assert(l[end - 1] == l_prime[end - 1]);
  }
}

pub proof fn k_timestamps_reach_deadline_aux(
  l: Log,
  start: int,
  end: int,
  base_ts: InstantView,
  deadline: InstantView,
  count: nat,
)
  requires
    timestamps_strictly_increasing(l),
    timestamps_positive(l),
    0 <= start <= end <= l.len(),
    count_get_current_time_in_range(l, start, end) >= count,
    count >= 1,
    base_ts == max_timestamp_up_to(l, start),
    base_ts + (count as int) > deadline,
  ensures
    exists |idx: int|
      start <= idx < end &&
      is_get_current_time_at(l, idx) &&
      get_current_timestamp(l[idx]) >= deadline,
{
  let ts_idx = nth_timestamp_at_least(l, start, end, base_ts, count);
  assert(get_current_timestamp(l[ts_idx]) >= base_ts + (count as int));
  assert(base_ts + (count as int) > deadline);
  assert(get_current_timestamp(l[ts_idx]) >= deadline);
}

}
