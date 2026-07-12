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
use crate::reactor::reactor_progress;
#[cfg(verus_keep_ghost)]
use crate::framework::module_spec::{progress_n, is_valid_trace};

verus! {

pub open spec fn extends_by_one_round(l: Log, l_prime: Log) -> bool {
  reactor_progress(l, l_prime)
}

pub open spec fn extends_by_k_rounds(l: Log, l_prime: Log, k: nat) -> bool
  decreases k
{
  if k == 0 {
    l == l_prime
  } else {
    exists |l_mid: Log|
      extends_by_one_round(l, l_mid) &&
      extends_by_k_rounds(l_mid, l_prime, (k - 1) as nat)
  }
}

pub open spec fn compute_bound(deadline: InstantView, current_max_ts: InstantView) -> nat {
  if deadline <= current_max_ts {
    1
  } else {
    let diff = (deadline - current_max_ts) as nat;
    diff + 1
  }
}

pub open spec fn count_get_current_time_in_range(l: Log, start: int, end: int) -> nat
  decreases end - start
{
  if start >= end || start < 0 || end > l.len() {
    0
  } else if is_get_current_time_at(l, start) {
    1 + count_get_current_time_in_range(l, start + 1, end)
  } else {
    count_get_current_time_in_range(l, start + 1, end)
  }
}

pub open spec fn has_at_least_k_timestamps(l: Log, l_prime: Log, k: nat) -> bool {
  is_prefix_of(l, l_prime) &&
  count_get_current_time_in_range(l_prime, l.len() as int, l_prime.len() as int) >= k
}

pub proof fn extends_by_k_rounds_implies_prefix(l: Log, l_prime: Log, k: nat)
  requires
    extends_by_k_rounds(l, l_prime, k),
  ensures
    is_prefix_of(l, l_prime),
  decreases k
{
  if k == 0 {
    assert(l == l_prime);
  } else {
    let l_mid: Log = choose |l_mid: Log|
      extends_by_one_round(l, l_mid) &&
      extends_by_k_rounds(l_mid, l_prime, (k - 1) as nat);
    assert(extends_by_one_round(l, l_mid));
    assert(reactor_progress(l, l_mid));
    assert(l =~= l_mid.subrange(0, l.len() as int));
    extends_by_k_rounds_implies_prefix(l_mid, l_prime, (k - 1) as nat);
    assert(l_mid =~= l_prime.subrange(0, l_mid.len() as int));
    assert(l.len() <= l_mid.len());
    assert(l_mid.len() <= l_prime.len());
  }
}

pub proof fn extends_by_k_rounds_preserves_inv(l: Log, l_prime: Log, k: nat)
  requires
    reactor_inv(l),
    extends_by_k_rounds(l, l_prime, k),
  ensures
    reactor_inv(l_prime),
  decreases k
{
  if k == 0 {
    assert(l == l_prime);
  } else {
    let l_mid: Log = choose |l_mid: Log|
      extends_by_one_round(l, l_mid) &&
      extends_by_k_rounds(l_mid, l_prime, (k - 1) as nat);
    extends_by_k_rounds_preserves_inv(l_mid, l_prime, (k - 1) as nat);
  }
}

proof fn find_last_park_begin_in_cycle(l: Log, start: int, i: int)
  requires
    0 <= start < l.len(),
    start <= i < l.len(),
    is_park_begin_at(l, start),
    forall |k: int| start < k <= i ==> !is_park_begin_at(l, k),
  ensures
    find_last_park_begin(l, i) == start,
  decreases i - start
{
  if i == start {
    assert(is_park_begin_at(l, i));
    assert(find_last_park_begin(l, i) == i);
  } else {
    assert(!is_park_begin_at(l, i));
    find_last_park_begin_in_cycle(l, start, i - 1);
  }
}

// Same, for the (now reactor-aligned) current_park_start, which scans from i-1
// and resets at park_end: inside a complete cycle (no park_begin/park_end in the
// interior) current_park_start(l, i) is the cycle's begin.
proof fn current_park_start_in_cycle(l: Log, start: int, i: int)
  requires
    0 <= start < l.len(),
    start < i < l.len(),
    is_park_begin_at(l, start),
    forall |k: int| start < k <= i ==> !is_park_begin_at(l, k),
    forall |k: int| start < k < i ==> !is_park_end_at(l, k),
  ensures
    current_park_start(l, i) == start,
  decreases i - start
{
  if i == start + 1 {
  } else {
    current_park_start_in_cycle(l, start, i - 1);
  }
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

pub proof fn one_round_has_at_least_one_timestamp(l: Log, l_prime: Log)
  requires
    reactor_inv(l),
    extends_by_one_round(l, l_prime),
  ensures
    count_get_current_time_in_range(l_prime, l.len() as int, l_prime.len() as int) >= 1,
{
  use crate::reactor::is_complete_park_cycle;
  use crate::reactor::invariants::{reactor_action_safety_inv, park_has_timestamp};
  use crate::framework::action_safety::action_safety_satisfied;

  assert(reactor_progress(l, l_prime));

  let (park_start, park_end): (int, int) = choose |park_start: int, park_end: int|
    #![trigger is_complete_park_cycle(l_prime, park_start, park_end)]
    l.len() as int <= park_start &&
    park_start < park_end &&
    park_end <= l_prime.len() as int &&
    is_complete_park_cycle(l_prime, park_start, park_end) &&
    (forall |i: int| l.len() as int <= i < park_start ==>
      crate::reactor::spec::events::is_inbound_non_park(#[trigger] l_prime[i])) &&
    (forall |i: int| park_end <= i < l_prime.len() as int ==>
      crate::reactor::spec::events::is_inbound_non_park(#[trigger] l_prime[i]));

  let park_end_idx = park_end - 1;
  assert(is_park_end_at(l_prime, park_end_idx));
  assert(is_park_begin_at(l_prime, park_start));

  assert(reactor_inv(l_prime));
  assert(reactor_action_safety_inv(l_prime));
  assert(action_safety_satisfied(park_has_timestamp::park_has_timestamp(), l_prime));

  let pht = park_has_timestamp::park_has_timestamp();
  assert(park_has_timestamp::action_fn(l_prime, park_end_idx));
  assert((pht.acceptance)(l_prime, park_end_idx));
  assert((pht.validity)(l_prime, park_end_idx));
  assert(park_has_timestamp::has_get_current_time_in_park(l_prime, park_end_idx));

  assert forall |k: int| park_start < k && k <= park_end_idx
    implies !is_park_begin_at(l_prime, k) by {
    if park_start < k && k < park_end_idx {
      assert(!is_park_begin_at(l_prime, k));
    } else if k == park_end_idx {
      assert(is_park_end_at(l_prime, k));
    }
  };

  assert forall |k: int| park_start < k < park_end_idx implies
    !is_park_end_at(l_prime, k) by {
    assert(park_start < k < park_end - 1);
    assert(!is_park_begin_at(l_prime, k));  // triggers is_complete_park_cycle's inner forall
  };
  current_park_start_in_cycle(l_prime, park_start, park_end_idx);
  let ps = current_park_start(l_prime, park_end_idx);
  assert(ps == park_start);

  let ts_idx: int = choose |j: int|
    #![trigger l_prime[j]]
    ps < j < park_end_idx &&
    is_get_current_time_at(l_prime, j);

  assert((l.len() as int) <= ts_idx);
  assert(ts_idx < l_prime.len() as int);
  count_ge_one_if_exists(l_prime, l.len() as int, l_prime.len() as int, ts_idx);
}

proof fn count_split_additive(l: Log, start: int, mid: int, end: int)
  requires
    0 <= start <= mid,
    mid <= end <= l.len(),
  ensures
    count_get_current_time_in_range(l, start, end) ==
      count_get_current_time_in_range(l, start, mid) +
      count_get_current_time_in_range(l, mid, end),
  decreases mid - start
{
  if start >= mid {
    assert(count_get_current_time_in_range(l, start, mid) == 0);
  } else {
    count_split_additive(l, start + 1, mid, end);
  }
}

proof fn count_on_prefix_eq(l: Log, l_prime: Log, start: int, end: int)
  requires
    is_prefix_of(l, l_prime),
    0 <= start <= end,
    end <= l.len(),
  ensures
    count_get_current_time_in_range(l, start, end) ==
    count_get_current_time_in_range(l_prime, start, end),
  decreases end - start
{
  if start >= end {
  } else {
    assert(l[start] == l_prime[start]);
    count_on_prefix_eq(l, l_prime, start + 1, end);
  }
}

// compute_bound is monotone-DECREASING in the current max timestamp: a later
// clock (larger max_ts) needs no more rounds. Used to bound timer_concrete_bound
// (which uses max_ts up to the log end) by env's timer_deadline_gap_bounded
// (stated at max_ts up to the registration), giving a UNIFORM chunk size.
pub proof fn compute_bound_monotone(d: InstantView, a: InstantView, b: InstantView)
  requires
    a >= b,
  ensures
    compute_bound(d, a) <= compute_bound(d, b),
{
}

// k >= 1 rounds strictly grow the log length (each round adds >= 1 timestamp).
pub proof fn k_rounds_len_growth(l: Log, l_prime: Log, k: nat)
  requires
    reactor_inv(l),
    extends_by_k_rounds(l, l_prime, k),
    k >= 1,
  ensures
    l.len() < l_prime.len(),
{
  k_rounds_imply_k_timestamps(l, l_prime, k);
  extends_by_k_rounds_implies_prefix(l, l_prime, k);
  if l.len() >= l_prime.len() {
    assert(l.len() == l_prime.len());
    assert(count_get_current_time_in_range(l_prime, l.len() as int, l_prime.len() as int) == 0);
    assert(false);
  }
}

pub proof fn k_rounds_imply_k_timestamps(l: Log, l_prime: Log, k: nat)
  requires
    reactor_inv(l),
    extends_by_k_rounds(l, l_prime, k),
  ensures
    has_at_least_k_timestamps(l, l_prime, k),
  decreases k
{
  extends_by_k_rounds_implies_prefix(l, l_prime, k);
  if k == 0 {
    assert(l == l_prime);
    assert(count_get_current_time_in_range(l_prime, l.len() as int, l_prime.len() as int) == 0);
  } else {
    let l_mid: Log = choose |l_mid: Log|
      extends_by_one_round(l, l_mid) &&
      extends_by_k_rounds(l_mid, l_prime, (k - 1) as nat);

    one_round_has_at_least_one_timestamp(l, l_mid);
    k_rounds_imply_k_timestamps(l_mid, l_prime, (k - 1) as nat);

    extends_by_k_rounds_implies_prefix(l_mid, l_prime, (k - 1) as nat);
    assert(l_mid.len() <= l_prime.len());

    count_split_additive(l_prime, l.len() as int, l_mid.len() as int, l_prime.len() as int);

    assert(count_get_current_time_in_range(l_mid, l.len() as int, l_mid.len() as int) >= 1);
    assert(count_get_current_time_in_range(l_prime, l_mid.len() as int, l_prime.len() as int) >= (k - 1) as nat);

    count_on_prefix_eq(l_mid, l_prime, l.len() as int, l_mid.len() as int);
  }
}

pub proof fn progress_n_implies_extends_by_k(l: Log, l_prime: Log, k: nat)
  requires
    progress_n(|a: Log, b: Log| reactor_progress(a, b), l, l_prime, k),
  ensures
    extends_by_k_rounds(l, l_prime, k),
  decreases k
{
  let progress_fn = |a: Log, b: Log| reactor_progress(a, b);
  let trace: Seq<Log> = choose |trace: Seq<Log>|
    #![trigger trace.len()]
    trace.len() == k + 1 &&
    trace.first() == l &&
    trace.last() == l_prime &&
    is_valid_trace(progress_fn, trace);

  if k == 0 {
    assert(trace.len() == 1);
    assert(trace[0] == l);
    assert(trace[trace.len() - 1] == l_prime);
    assert(trace[0] == trace[trace.len() - 1]);
    assert(l == l_prime);
  } else {
    let l_mid = trace[1];
    assert(progress_fn(trace[0], trace[1]));
    assert(reactor_progress(l, l_mid));
    assert(extends_by_one_round(l, l_mid));

    let subtrace: Seq<Log> = trace.subrange(1, trace.len() as int);
    assert(subtrace.len() == k);
    assert(subtrace.first() == l_mid);
    assert(subtrace.last() == l_prime) by {
      assert(subtrace[subtrace.len() - 1] == trace[trace.len() - 1]);
    };

    assert(is_valid_trace(progress_fn, subtrace)) by {
      assert(subtrace.len() >= 1);
      assert forall |i: int| 0 <= i < subtrace.len() - 1 implies
        progress_fn(#[trigger] subtrace[i], subtrace[i + 1]) by {
        assert(subtrace[i] == trace[i + 1]);
        assert(subtrace[i + 1] == trace[i + 2]);
        assert(0 <= i + 1 < trace.len() - 1);
        assert(progress_fn(trace[i + 1], trace[i + 2]));
      };
    };

    assert(progress_n(progress_fn, l_mid, l_prime, (k - 1) as nat)) by {
      assert(subtrace.len() == (k - 1) as nat + 1);
    };

    progress_n_implies_extends_by_k(l_mid, l_prime, (k - 1) as nat);
  }
}

pub proof fn extends_by_k_implies_progress_n(l: Log, l_prime: Log, k: nat)
  requires
    extends_by_k_rounds(l, l_prime, k),
  ensures
    progress_n(|a: Log, b: Log| reactor_progress(a, b), l, l_prime, k),
  decreases k
{
  let progress_fn = |a: Log, b: Log| reactor_progress(a, b);
  if k == 0 {
    assert(l == l_prime);
    let trace: Seq<Log> = seq![l];
    assert(trace.len() == k + 1);
    assert(trace.first() == l);
    assert(trace.last() == l_prime);
    assert(is_valid_trace(progress_fn, trace)) by {
      assert(trace.len() >= 1);
    };
  } else {
    let l_mid: Log = choose |l_mid: Log|
      extends_by_one_round(l, l_mid) &&
      extends_by_k_rounds(l_mid, l_prime, (k - 1) as nat);

    extends_by_k_implies_progress_n(l_mid, l_prime, (k - 1) as nat);

    let subtrace: Seq<Log> = choose |trace: Seq<Log>|
      #![trigger trace.len()]
      trace.len() == k &&
      trace.first() == l_mid &&
      trace.last() == l_prime &&
      is_valid_trace(progress_fn, trace);

    let trace: Seq<Log> = seq![l] + subtrace;

    assert(trace.len() == k + 1);
    assert(trace.first() == l);
    assert(trace.last() == l_prime) by {
      assert(trace[trace.len() - 1] == subtrace[subtrace.len() - 1]);
    };

    assert(is_valid_trace(progress_fn, trace)) by {
      assert(trace.len() >= 1);
      assert forall |i: int| 0 <= i < trace.len() - 1 implies
        progress_fn(#[trigger] trace[i], trace[i + 1]) by {
        if i == 0 {
          assert(trace[0] == l);
          assert(trace[1] == subtrace[0]);
          assert(subtrace[0] == l_mid);
          assert(reactor_progress(l, l_mid));
        } else {
          assert(trace[i] == subtrace[i - 1]);
          assert(trace[i + 1] == subtrace[i]);
          assert(progress_fn(subtrace[i - 1], subtrace[i]));
        }
      };
    };
  }
}

pub proof fn max_ts_upper_bounds_all(l: Log, i: int, j: int)
  requires
    0 <= j < i,
    i <= l.len(),
    is_get_current_time_at(l, j),
  ensures
    get_current_timestamp(l[j]) <= max_timestamp_up_to(l, i),
  decreases i - j
{
  if j == i - 1 {
    if is_get_current_time_at(l, i - 1) {
      let ts = get_current_timestamp(l[i - 1]);
      let prev_max = max_timestamp_up_to(l, i - 1);
      assert(max_timestamp_up_to(l, i) == if ts > prev_max { ts } else { prev_max });
    }
  } else {
    max_ts_upper_bounds_all(l, i - 1, j);
    if i - 1 >= 1 && is_get_current_time_at(l, i - 1) {
      let ts = get_current_timestamp(l[i - 1]);
      let prev_max = max_timestamp_up_to(l, i - 1);
      assert(max_timestamp_up_to(l, i) == if ts > prev_max { ts } else { prev_max });
      assert(max_timestamp_up_to(l, i) >= prev_max);
    } else {
      assert(max_timestamp_up_to(l, i) == max_timestamp_up_to(l, i - 1));
    }
  }
}

pub proof fn max_ts_witness(l: Log, i: int)
  requires
    i <= l.len(),
    i >= 1,
    max_timestamp_up_to(l, i) > 0,
  ensures
    exists |j: int|
      #![trigger l[j]]
      0 <= j < i &&
      is_get_current_time_at(l, j) &&
      get_current_timestamp(l[j]) == max_timestamp_up_to(l, i),
  decreases i
{
  if i <= 0 {
    assert(false);
  } else if is_get_current_time_at(l, i - 1) {
    let ts = get_current_timestamp(l[i - 1]);
    let prev_max = max_timestamp_up_to(l, i - 1);
    if ts > prev_max {
      assert(max_timestamp_up_to(l, i) == ts);
      assert(l[i - 1] == l[i - 1]);
    } else {
      assert(max_timestamp_up_to(l, i) == prev_max);
      assert(prev_max > 0);
      if i - 1 >= 1 {
        max_ts_witness(l, i - 1);
      } else {
        assert(max_timestamp_up_to(l, 0) == 0);
        assert(false);
      }
    }
  } else {
    assert(max_timestamp_up_to(l, i) == max_timestamp_up_to(l, i - 1));
    if i - 1 >= 1 {
      max_ts_witness(l, i - 1);
    } else {
      assert(max_timestamp_up_to(l, 0) == 0);
      assert(false);
    }
  }
}

proof fn max_ts_nonneg(l: Log, i: int)
  requires
    i <= l.len(),
  ensures
    max_timestamp_up_to(l, i) >= 0,
  decreases i
{
  if i <= 0 {
  } else if is_get_current_time_at(l, i - 1) {
    max_ts_nonneg(l, i - 1);
    let ts = get_current_timestamp(l[i - 1]);
    let prev_max = max_timestamp_up_to(l, i - 1);
    assert(max_timestamp_up_to(l, i) == if ts > prev_max { ts } else { prev_max });
  } else {
    max_ts_nonneg(l, i - 1);
  }
}

pub proof fn new_timestamp_exceeds_max(l: Log, ts_pos: int)
  requires
    0 <= ts_pos < l.len(),
    is_get_current_time_at(l, ts_pos),
    crate::reactor::timestamps_strictly_increasing(l),
    crate::reactor::timestamps_positive(l),
  ensures
    get_current_timestamp(l[ts_pos]) >= max_timestamp_up_to(l, ts_pos) + 1,
{
  let ts_val = get_current_timestamp(l[ts_pos]);
  if max_timestamp_up_to(l, ts_pos) == 0 {
    assert(ts_val >= 1);
  } else {
    if ts_pos >= 1 {
      max_ts_nonneg(l, ts_pos);
      assert(max_timestamp_up_to(l, ts_pos) > 0);
      max_ts_witness(l, ts_pos);
      let j: int = choose |j: int|
        #![trigger l[j]]
        0 <= j < ts_pos &&
        is_get_current_time_at(l, j) &&
        get_current_timestamp(l[j]) == max_timestamp_up_to(l, ts_pos);
      assert(ts_val > get_current_timestamp(l[j]));
    } else {
      assert(max_timestamp_up_to(l, 0) == 0);
      assert(false);
    }
  }
}

proof fn max_ts_grows_at_timestamp(l: Log, i: int)
  requires
    0 <= i < l.len(),
    is_get_current_time_at(l, i),
    crate::reactor::timestamps_strictly_increasing(l),
    crate::reactor::timestamps_positive(l),
  ensures
    max_timestamp_up_to(l, (i + 1) as int) >= max_timestamp_up_to(l, i) + 1,
{
  new_timestamp_exceeds_max(l, i);
  let ts = get_current_timestamp(l[i]);
  let prev_max = max_timestamp_up_to(l, i);
  assert(ts >= prev_max + 1);
  assert(max_timestamp_up_to(l, (i + 1) as int) == if ts > prev_max { ts } else { prev_max });
  assert(ts > prev_max);
  assert(max_timestamp_up_to(l, (i + 1) as int) == ts);
}

pub proof fn timestamps_grow_with_witness(
  l: Log,
  start: int,
  end: int,
  k: nat,
)
  requires
    0 <= start,
    start <= end,
    end <= l.len(),
    crate::reactor::timestamps_strictly_increasing(l),
    crate::reactor::timestamps_positive(l),
    count_get_current_time_in_range(l, start, end) >= k,
    k >= 1,
  ensures
    exists |ts_idx: int|
      #![trigger l[ts_idx]]
      start <= ts_idx < end &&
      is_get_current_time_at(l, ts_idx) &&
      get_current_timestamp(l[ts_idx]) >= max_timestamp_up_to(l, start) + k,
  decreases end - start
{
  if start >= end {
    assert(count_get_current_time_in_range(l, start, end) == 0);
    assert(false);
  } else if is_get_current_time_at(l, start) {
    if k == 1 {
      new_timestamp_exceeds_max(l, start);
      assert(get_current_timestamp(l[start]) >= max_timestamp_up_to(l, start) + 1);
      assert(l[start] == l[start]);
    } else {
      new_timestamp_exceeds_max(l, start);
      max_ts_grows_at_timestamp(l, start);
      assert(max_timestamp_up_to(l, (start + 1) as int) >= max_timestamp_up_to(l, start) + 1);
      let count_rest = count_get_current_time_in_range(l, start + 1, end);
      assert(count_get_current_time_in_range(l, start, end) == 1 + count_rest);
      assert(count_rest >= (k - 1) as nat);
      timestamps_grow_with_witness(l, start + 1, end, (k - 1) as nat);
      let ts_idx: int = choose |ts_idx: int|
        #![trigger l[ts_idx]]
        start + 1 <= ts_idx < end &&
        is_get_current_time_at(l, ts_idx) &&
        get_current_timestamp(l[ts_idx]) >= max_timestamp_up_to(l, (start + 1) as int) + ((k - 1) as nat);
      assert(get_current_timestamp(l[ts_idx]) >= max_timestamp_up_to(l, start) + 1 + ((k - 1) as nat));
      assert(max_timestamp_up_to(l, start) + 1 + ((k - 1) as nat) == max_timestamp_up_to(l, start) + k);
    }
  } else {
    assert(count_get_current_time_in_range(l, start, end) ==
      count_get_current_time_in_range(l, start + 1, end));
    assert(max_timestamp_up_to(l, (start + 1) as int) == max_timestamp_up_to(l, start));
    timestamps_grow_with_witness(l, start + 1, end, k);
  }
}

// Lemma: progress_n with reactor_progress implies is_prefix_of.
// (By induction on n: each step extends the log; reactor_progress requires
// l_prime.len() > l.len() and l = l_prime.subrange(0, l.len()).)
pub proof fn reactor_progress_n_implies_prefix(l: Log, l_prime: Log, n: nat)
  requires
    progress_n(crate::reactor::reactor_module_spec().progress, l, l_prime, n),
  ensures
    is_prefix_of(l, l_prime),
  decreases n,
{
  let trace: Seq<Log> = choose |trace: Seq<Log>|
    #![trigger trace.len()]
    trace.len() == n + 1 &&
    trace.first() == l &&
    trace.last() == l_prime &&
    is_valid_trace(crate::reactor::reactor_module_spec().progress, trace);

  if n == 0 {
    assert(l =~= l_prime);
  } else {
    let l_mid: Log = trace[1];
    assert(reactor_progress(l, l_mid));
    assert(is_prefix_of(l, l_mid));

    let sub_trace: Seq<Log> = trace.subrange(1, trace.len() as int);
    assert(sub_trace.len() == n);
    assert(sub_trace.first() == l_mid) by {
      assert(sub_trace[0] == trace[1]);
    };
    assert(sub_trace.last() == l_prime) by {
      assert(sub_trace[sub_trace.len() - 1] == trace[trace.len() - 1]);
    };
    assert(is_valid_trace(crate::reactor::reactor_module_spec().progress, sub_trace)) by {
      assert forall |i: int| 0 <= i < sub_trace.len() - 1 implies
        (crate::reactor::reactor_module_spec().progress)(#[trigger] sub_trace[i], sub_trace[i + 1])
      by {
        assert(sub_trace[i] == trace[i + 1]);
        assert(sub_trace[i + 1] == trace[i + 2]);
      };
    };
    assert(progress_n(crate::reactor::reactor_module_spec().progress, l_mid, l_prime, (n - 1) as nat));
    reactor_progress_n_implies_prefix(l_mid, l_prime, (n - 1) as nat);
    assert(is_prefix_of(l_mid, l_prime));
    assert(l =~= l_prime.subrange(0, l.len() as int));
  }
}

}
