use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::executor::spec::log::*;
#[cfg(verus_keep_ghost)]
use crate::executor::spec::types::*;
#[cfg(verus_keep_ghost)]
use crate::executor::spec::events::*;
#[cfg(verus_keep_ghost)]
use crate::executor::executor_module_spec;
#[cfg(verus_keep_ghost)]
use crate::executor::contracts::bounded_injection_poll::*;
#[cfg(verus_keep_ghost)]
use crate::executor::contracts::bounded_deferred_poll;
#[cfg(verus_keep_ghost)]
use crate::executor::contracts::bounded_task_wake_poll;
#[cfg(verus_keep_ghost)]
use crate::executor::contracts::bounded_reactor_wake_poll;
#[cfg(verus_keep_ghost)]
use crate::framework::async_contract::*;
#[cfg(verus_keep_ghost)]
use crate::framework::module_spec::{progress_n, progress_preserves_wf, is_valid_trace};

verus! {

// ============================================================================
// Per-instance bounded liveness proofs for each executor async contract.
//
// Status: structural scaffold. Each per-instance proof currently uses a
// targeted `assume` for the (trigger ∧ assumption → ensures_response)
// content. Top-level wrappers `bounded_X_satisfies_liveness` are
// fully discharged given the per-instance lemma.
// ============================================================================

// --- bounded_injection_poll ---

proof fn count_pop_subrange_eq(
  l_full: Log,
  l_sub: Log,
  start: int,
  end: int,
)
  requires
    0 <= start <= end <= l_sub.len(),
    l_sub.len() <= l_full.len(),
    forall |i: int| 0 <= i < l_sub.len() ==> l_sub[i] == l_full[i],
  ensures
    count_pop_injection_between(l_sub, start, end) ==
      count_pop_injection_between(l_full, start, end),
  decreases end - start
{
  if start >= end {
  } else {
    assert(l_sub[start] == l_full[start]);
    count_pop_subrange_eq(l_full, l_sub, start + 1, end);
  }
}

proof fn position_preserved_one_step(
  l: Log,
  i: int,
  pos: int,
  tid: TID,
)
  requires
    0 <= i < l.len(),
    !is_poll_task_at(l, i),
    ({
      let q = crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i);
      0 <= pos < q.len() && q[pos] == tid
    }),
  ensures
    ({
      let q_next = crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i + 1);
      pos < q_next.len() && q_next[pos] == tid
    }),
{
  use crate::executor::invariants::fifo_task_selection::*;
  use crate::executor::spec::events::*;
  let q = fifo_queue_at(l, i);
  let q_next = fifo_queue_at(l, i + 1);
  let e = l[i];
  if is_pop_injection(e) && get_pop_injection_task(e).is_some() {
    assert(q_next =~= q.push(get_pop_injection_task(e).unwrap().id));
    assert(q_next[pos] == q[pos]);
  } else if is_drain(e) {
    let drain_tids = get_drain_task_ids(e);
    assert(q_next =~= q + drain_tids);
    assert(q_next[pos] == q[pos]);
  } else {
    assert(q_next =~= q);
  }
}

// Multi-step position preservation from start until first PollTask.
proof fn position_preserved_until_poll(
  l: Log,
  start: int,
  end: int,
  pos: int,
  tid: TID,
)
  requires
    0 <= start <= end <= l.len(),
    forall |j: int| start <= j < end ==> !#[trigger] is_poll_task_at(l, j),
    ({
      let q = crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, start);
      0 <= pos < q.len() && q[pos] == tid
    }),
  ensures
    ({
      let q = crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, end);
      pos < q.len() && q[pos] == tid
    }),
  decreases end - start
{
  if start == end {
  } else {
    assert(!is_poll_task_at(l, start));
    position_preserved_one_step(l, start, pos, tid);
    position_preserved_until_poll(l, start + 1, end, pos, tid);
  }
}

// PollTask at poll_idx removes the head: queue at poll_idx+1 is queue at
// poll_idx with the first element dropped (when the polled tid equals
// the head).
proof fn poll_removes_head(l: Log, poll_idx: int)
  requires
    0 <= poll_idx < l.len(),
    is_poll_task_at(l, poll_idx),
    ({
      let q = crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, poll_idx);
      q.len() > 0 &&
        q[0] == get_poll_task_id(l[poll_idx])
    }),
  ensures
    ({
      let q = crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, poll_idx);
      let q_next = crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, poll_idx + 1);
      q_next =~= q.subrange(1, q.len() as int)
    }),
{
  use crate::executor::invariants::fifo_task_selection::*;
  use crate::executor::spec::events::*;
  let q = fifo_queue_at(l, poll_idx);
  let q_next = fifo_queue_at(l, poll_idx + 1);
  let polled = get_poll_task_id(l[poll_idx]);
  assert(is_poll_task(l[poll_idx]));
  assert(q_next =~= remove_first_occurrence(q, polled));
  // q[0] == polled, so remove_first_occurrence returns q.subrange(1, len).
  assert(q[0] == polled);
  assert(remove_first_occurrence(q, polled) =~= q.subrange(1, q.len() as int));
}

// count_poll_tasks_in_range split at a single PollTask boundary.
proof fn count_poll_tasks_split_at_idx(
  l: Log,
  start: int,
  idx: int,
  end: int,
)
  requires
    0 <= start <= idx < end <= l.len(),
    is_poll_task_at(l, idx),
    forall |j: int| start <= j < idx ==> !#[trigger] is_poll_task_at(l, j),
  ensures
    count_poll_tasks_in_range(l, start, end) ==
      1 + count_poll_tasks_in_range(l, idx + 1, end),
  decreases idx - start
{
  if start == idx {
  } else {
    assert(!is_poll_task_at(l, start));
    count_poll_tasks_split_at_idx(l, start + 1, idx, end);
  }
}

// count_poll_tasks_in_range > 0 implies a PollTask exists in [start, end).
proof fn count_poll_tasks_positive_implies_exists(
  l: Log,
  start: int,
  end: int,
)
  requires
    0 <= start <= end <= l.len(),
    count_poll_tasks_in_range(l, start, end) > 0,
  ensures
    exists |j: int| start <= j < end && is_poll_task_at(l, j),
  decreases end - start
{
  if start >= end {
    assert(count_poll_tasks_in_range(l, start, end) == 0);
    assert(false);
  } else if is_poll_task_at(l, start) {
    // start is the witness
  } else {
    count_poll_tasks_positive_implies_exists(l, start + 1, end);
  }
}

proof fn fifo_position_eventually_polled(
  l: Log,
  tid: TID,
  start: int,
  end: int,
  pos: int,
)
  requires
    crate::executor::invariants::executor_inv(l),
    0 < start <= end <= l.len(),
    0 <= pos,
    ({
      let q = crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, start);
      pos < q.len() && q[pos] == tid
    }),
    count_poll_tasks_in_range(l, start, end) > pos,
  ensures
    exists |poll_idx: int|
      start <= poll_idx < end &&
      is_poll_task_for_id_at(l, poll_idx, tid),
  decreases pos
{
  use crate::executor::invariants::fifo_task_selection::*;
  use crate::executor::proof::bounded_injection_poll::{
    find_first_poll_task, find_first_poll_task_valid, first_poll_polls_head,
  };

  // Pick the first PollTask in [start, end).
  count_poll_tasks_positive_implies_exists(l, start, end);
  find_first_poll_task_valid(l, start, end);
  let poll_idx = find_first_poll_task(l, start, end);
  assert(start <= poll_idx < end);
  assert(is_poll_task_at(l, poll_idx));
  assert(forall |j: int| start <= j < poll_idx ==> !#[trigger] is_poll_task_at(l, j));

  // Queue head at start == queue head at poll_idx (no PollTask between).
  let q_start = fifo_queue_at(l, start);
  let q_poll = fifo_queue_at(l, poll_idx);
  assert(q_start.len() > 0);
  first_poll_polls_head(l, poll_idx, start);
  assert(q_poll.len() > 0 && q_poll[0] == q_start[0]);

  // PollTask polls the head value (fifo_task_selection invariant).
  let fts = fifo_task_selection();
  assert(crate::executor::invariants::executor_action_safety_inv(l));
  assert(crate::framework::action_safety::action_safety_satisfied(fts, l));
  assert(action_fn(l, poll_idx));
  assert((fts.acceptance)(l, poll_idx));
  assert((fts.validity)(l, poll_idx));
  // validity says: is_fifo_head_at(l, poll_idx, get_poll_task_id(l[poll_idx]))
  // i.e., q_poll[0] == get_poll_task_id(l[poll_idx]).
  let polled_tid = get_poll_task_id(l[poll_idx]);
  assert(is_fifo_head_at(l, poll_idx, polled_tid));
  assert(q_poll[0] == polled_tid);

  if pos == 0 {
    // Base case: tid is head at start, hence head at poll_idx, hence polled.
    assert(q_start[0] == tid);
    assert(q_poll[0] == tid);
    assert(polled_tid == tid);
    assert(is_poll_task_for_id_at(l, poll_idx, tid));
  } else {
    // Inductive case: polled_tid = head ≠ tid (tid at pos > 0).
    // Step 1: position preservation [start, poll_idx]
    position_preserved_until_poll(l, start, poll_idx, pos, tid);
    assert(pos < q_poll.len() && q_poll[pos] == tid);

    // Step 2: poll removes head, q_next = q_poll.subrange(1, ...)
    poll_removes_head(l, poll_idx);
    let q_next = fifo_queue_at(l, poll_idx + 1);
    assert(q_next =~= q_poll.subrange(1, q_poll.len() as int));
    // tid at q_poll[pos] becomes q_next[pos - 1].
    assert(q_next[pos - 1] == q_poll[pos]);
    assert(q_next[pos - 1] == tid);
    assert(pos - 1 < q_next.len());

    // Step 3: count split
    count_poll_tasks_split_at_idx(l, start, poll_idx, end);
    assert(count_poll_tasks_in_range(l, poll_idx + 1, end) > pos - 1);

    // Step 4: recurse
    fifo_position_eventually_polled(l, tid, poll_idx + 1, end, pos - 1);
  }
}

pub proof fn fifo_member_eventually_polled_b(
  l_prime: Log,
  tid: TID,
  enter_idx: int,
  b: nat,
)
  requires
    crate::executor::invariants::executor_inv(l_prime),
    0 < enter_idx < l_prime.len(),
    crate::composed::proof::end_to_end::tid_in_fifo_queue_at(l_prime, enter_idx, tid),
    crate::executor::proof::queue_bound_single_state::queue_bound_at(l_prime, b),
    count_poll_tasks_in_range(l_prime, enter_idx, l_prime.len() as int) > b,
  ensures
    has_poll_task_for_id_after(l_prime, tid, enter_idx),
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  let q = fifo_queue_at(l_prime, enter_idx);
  let pos: int = choose |p: int| 0 <= p < q.len() && q[p] == tid;
  // queue_bound_at(l',b) instantiated at i = enter_idx bounds the queue length.
  assert(fifo_queue_at(l_prime, enter_idx).len() <= b);
  assert(q.len() <= b);
  assert(pos < b as int);
  fifo_position_eventually_polled(l_prime, tid, enter_idx, l_prime.len() as int, pos);
  let poll_idx: int = choose |idx: int|
    enter_idx <= idx < l_prime.len() &&
    is_poll_task_for_id_at(l_prime, idx, tid);
  assert(is_poll_task_for_id_at(l_prime, poll_idx, tid));
}

proof fn one_step_yields_one_poll_task_if_queue_nonempty(
  l_a: Log,
  l_b: Log,
)
  requires
    crate::executor::invariants::executor_inv(l_a),
    crate::executor::invariants::executor_inv(l_b),
    crate::executor::executor_progress(l_a, l_b),
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(
      l_b, l_a.len() as int
    ).len() > 0,
  ensures
    count_poll_tasks_in_range(l_b, l_a.len() as int, l_b.len() as int) >= 1,
{
  use crate::executor::invariants::*;
  use crate::framework::local_liveness::*;
  let start = l_a.len() as int;
  let end = l_b.len() as int;
  // is_complete_tick_cycle(l_b, start, end) gives Tick::Begin at start.
  assert(crate::executor::is_complete_tick_cycle(l_b, start, end));
  assert(is_tick_begin_at(l_b, start));
  // tick_polls_if_runnable trigger at start.
  let tpir = tick_polls_if_runnable::tick_polls_if_runnable();
  assert(executor_inv(l_b));
  assert(executor_local_liveness_inv(l_b));
  assert(local_liveness_satisfied(tpir, l_b));
  assert((tpir.acceptance)(l_b, start));
  let j: int = choose |j: int|
    #![trigger (tpir.fulfillment)(l_b, start, j)]
    j > start && (tpir.fulfillment)(l_b, start, j) && (tpir.timely)(l_b, start, j);
  assert(is_poll_task_at(l_b, j));
  assert(j < end);
  count_poll_tasks_positive_implies_exists_inverse(l_b, start, end, j);
}

// If a PollTask exists at position j in [start, end), then
// count_poll_tasks_in_range(l, start, end) >= 1.
proof fn count_poll_tasks_positive_implies_exists_inverse(
  l: Log,
  start: int,
  end: int,
  j: int,
)
  requires
    0 <= start <= j < end <= l.len(),
    is_poll_task_at(l, j),
  ensures
    count_poll_tasks_in_range(l, start, end) >= 1,
  decreases j - start
{
  if start == j {
    // Direct: count >= 1 because event at start is PollTask.
  } else {
    if is_poll_task_at(l, start) {
      // Direct from start.
    } else {
      count_poll_tasks_positive_implies_exists_inverse(l, start + 1, end, j);
    }
  }
}

// Disjunctive form: progress_n with k steps + tid in queue at start
// yields either has_poll_task_for_id (tid polled along the way) OR
// count_poll_tasks_in_range >= k (each step yielded ≥1 PollTask because
// queue stayed non-empty due to tid being there).
// Executor-level env-form DRAINAGE contract (bound-explicit): a queued tid (in the
// FIFO queue at l_a's end) is polled within b+1 progress steps on any trace whose
// endpoint keeps the queue bounded by b (queue_bound_at — the single-state env fact).
// Packages the module's own progress_yields_polled_or_count + fifo_member_eventually_polled_b
// so the composed proof consumes the executor's drainage guarantee through THIS
// module-level statement, not by reaching into the two internal lemmas directly.
pub proof fn executor_drain_env_response_within(l_a: Log, l_b: Log, tid: TID, b: nat, m: nat)
  requires
    crate::executor::invariants::executor_inv(l_a),
    crate::executor::invariants::executor_inv(l_b),
    0 < l_a.len(),
    m >= b + 1,
    progress_n(executor_module_spec().progress, l_a, l_b, m),
    crate::composed::proof::end_to_end::tid_in_fifo_queue_at(l_a, l_a.len() as int, tid),
    crate::executor::proof::queue_bound_single_state::queue_bound_at(l_b, b),
  ensures
    has_poll_task_for_id_after(l_b, tid, l_a.len() as int),
{
  progress_yields_polled_or_count(l_a, l_b, tid, m);
  if !has_poll_task_for_id_after(l_b, tid, l_a.len() as int) {
    assert(count_poll_tasks_in_range(l_b, l_a.len() as int, l_b.len() as int) >= m);
    assert(l_a.len() < l_b.len());
    crate::executor::proof::bounded_injection_poll::progress_n_implies_prefix(l_a, l_b, m);
    fifo_queue_prefix_eq(l_a, l_b, l_a.len() as int);
    fifo_member_eventually_polled_b(l_b, tid, l_a.len() as int, b);
  }
}

// The executor DRAINAGE contract as an AsyncContract, anchored at the state where
// tid enters the queue: acceptance = tid queued at anchor's end; fulfillment = tid
// polled after anchor's end.
pub open spec fn drain_contract(anchor: Log) -> AsyncContract<Log, TID> {
  AsyncContract {
    acceptance: |l: Log, tid: TID|
      l == anchor &&
      crate::composed::proof::end_to_end::tid_in_fifo_queue_at(anchor, anchor.len() as int, tid),
    fulfillment: |l: Log, tid: TID| has_poll_task_for_id_after(l, tid, anchor.len() as int),
    assumption: |l: Log, tid: TID| true,
  }
}

// THE ENV-FORM EXECUTOR DRAINAGE CONTRACT (module-proven, non-vacuous): the executor
// module satisfies bounded_liveness_env_without_arrival for drain_contract under the
// SATISFIABLE single-state env queue_bound_at(·, b). Composed consumes THIS
// bounded_liveness_env interface for the queue drainage (symmetric with the reactor
// timer contract), replacing the forall-ext queue_length_bounded_persistent.
pub proof fn executor_drain_satisfies_liveness_env(anchor: Log, b: nat)
  requires
    crate::executor::invariants::executor_inv(anchor),
    0 < anchor.len(),
  ensures
    bounded_liveness_env_without_arrival(
      executor_module_spec(), drain_contract(anchor),
      |l: Log, tid: TID| crate::executor::proof::queue_bound_single_state::queue_bound_at(l, b)),
{
  let env = |l: Log, tid: TID| crate::executor::proof::queue_bound_single_state::queue_bound_at(l, b);
  let ac = drain_contract(anchor);
  crate::executor::proof::bounded_injection_poll::progress_preserves_executor_inv();
  assert forall |tid: TID, l: Log|
    #![trigger env(l, tid)]
    (executor_module_spec().well_formed)(l) && (ac.acceptance)(l, tid) && env(l, tid)
    implies exists |n: nat| #[trigger] env_response_within_trace(l, tid, executor_module_spec(), ac, env, n) by {
    assert(l == anchor);
    let n: nat = (b + 1) as nat;
    assert(env_response_within_trace(anchor, tid, executor_module_spec(), ac, env, n)) by {
      assert forall |l2: Log|
        #[trigger] crate::framework::module_spec::env_progress_n(
          executor_module_spec().progress, anchor, l2, n, env, tid)
        implies (ac.fulfillment)(l2, tid) by {
        crate::framework::module_spec::env_progress_n_implies_progress_n(
          executor_module_spec().progress, anchor, l2, n, env, tid);
        crate::executor::proof::bounded_injection_poll::progress_n_preserves_inv(anchor, l2, n);
        crate::framework::module_spec::env_progress_n_gives_env_at_end(
          executor_module_spec().progress, anchor, l2, n, env, tid);
        executor_drain_env_response_within(anchor, l2, tid, b, n);
      };
    };
  };
}

pub proof fn progress_yields_polled_or_count(
  l_a: Log,
  l_b: Log,
  tid: TID,
  n: nat,
)
  requires
    crate::executor::invariants::executor_inv(l_a),
    crate::executor::invariants::executor_inv(l_b),
    progress_n(executor_module_spec().progress, l_a, l_b, n),
    crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
      l_a, l_a.len() as int, tid
    ),
  ensures
    has_poll_task_for_id_after(l_b, tid, l_a.len() as int)
    || count_poll_tasks_in_range(l_b, l_a.len() as int, l_b.len() as int) >= n,
  decreases n
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  use crate::composed::proof::end_to_end::{
    tid_in_fifo_queue_at, tid_survives_or_polled_in_range,
  };
  use crate::executor::proof::bounded_injection_poll::{
    progress_n_decompose, progress_n_implies_prefix,
  };

  if n == 0 {
    assert(l_a == l_b);
    assert(count_poll_tasks_in_range(l_b, l_a.len() as int, l_b.len() as int) == 0);
  } else {
    // One-step decomposition.
    let l_mid = progress_n_decompose(l_a, l_b, n);
    assert(crate::executor::executor_progress(l_a, l_mid));
    assert(is_prefix_of(l_a, l_mid));
    assert(is_prefix_of(l_mid, l_b));

    // tid persists through l_a → l_mid: tid_survives_or_polled_in_range.
    // We pass the prefix l_a → l_mid range. Need l_mid's executor_inv (have it).
    progress_n_first_step_invariant(l_a, l_mid, l_b, n);
    assert(crate::executor::invariants::executor_inv(l_mid));

    // tid_in_fifo_queue_at(l_a, l_a.len(), tid). l_mid extends l_a; queue at
    // l_a.len() in l_mid is the same (since l_a is prefix).
    queue_prefix_eq_at_len(l_a, l_mid);
    assert(tid_in_fifo_queue_at(l_mid, l_a.len() as int, tid));

    // Apply tid_survives_or_polled_in_range on l_mid, [l_a.len, l_mid.len).
    assert(0 < l_a.len() as int <= l_mid.len() as int);
    tid_survives_or_polled_in_range(l_mid, tid, l_a.len() as int, l_mid.len() as int);

    if exists |poll_idx: int|
      l_a.len() as int <= poll_idx < l_mid.len() as int &&
      is_poll_task_for_id_at(l_mid, poll_idx, tid)
    {
      // Case: polled in (l_a.len, l_mid.len). Lift to l_b via prefix.
      let poll_idx: int = choose |i: int|
        l_a.len() as int <= i < l_mid.len() as int &&
        is_poll_task_for_id_at(l_mid, i, tid);
      assert(l_mid[poll_idx] == l_b[poll_idx]);
      assert(is_poll_task_for_id_at(l_b, poll_idx, tid));
      assert(has_poll_task_for_id_after(l_b, tid, l_a.len() as int));
    } else {
      // Case: tid still in queue at l_mid.len.
      assert(tid_in_fifo_queue_at(l_mid, l_mid.len() as int, tid));
      // Queue non-empty at l_a.len in l_mid (because tid is there).
      let q = fifo_queue_at(l_mid, l_a.len() as int);
      assert(q.len() > 0);
      // First step yields ≥1 PollTask in [l_a.len, l_mid.len).
      one_step_yields_one_poll_task_if_queue_nonempty(l_a, l_mid);
      assert(count_poll_tasks_in_range(l_mid, l_a.len() as int, l_mid.len() as int) >= 1);

      // Recurse on l_mid → l_b with n - 1.
      if n > 1 {
        progress_yields_polled_or_count(l_mid, l_b, tid, (n - 1) as nat);
        if has_poll_task_for_id_after(l_b, tid, l_mid.len() as int) {
          // Lift to start from l_a.len.
          let poll_idx: int = choose |i: int|
            l_mid.len() as int <= i < l_b.len() as int &&
            is_poll_task_for_id_at(l_b, i, tid);
          assert(l_a.len() as int <= poll_idx);
        } else {
          // count(l_mid.len, l_b.len) >= n - 1.
          // count(l_a.len, l_b.len) = count(l_a.len, l_mid.len) + count(l_mid.len, l_b.len).
          // The first count is preserved on l_b (prefix).
          count_poll_tasks_prefix_eq(l_mid, l_b, l_a.len() as int, l_mid.len() as int);
          count_poll_tasks_split_additive(
            l_b, l_a.len() as int, l_mid.len() as int, l_b.len() as int
          );
          assert(count_poll_tasks_in_range(l_b, l_a.len() as int, l_b.len() as int)
                 >= 1 + (n - 1));
        }
      } else {
        // n == 1, l_mid == l_b.
        assert(l_mid == l_b);
      }
    }
  }
}

// PollTask count in a prefix range equals count in the extending log.
proof fn count_poll_tasks_prefix_eq(
  l_short: Log,
  l_long: Log,
  start: int,
  end: int,
)
  requires
    is_prefix_of(l_short, l_long),
    0 <= start <= end <= l_short.len(),
  ensures
    count_poll_tasks_in_range(l_short, start, end) ==
      count_poll_tasks_in_range(l_long, start, end),
  decreases end - start
{
  if start >= end {
  } else {
    assert(l_short[start] == l_long[start]);
    count_poll_tasks_prefix_eq(l_short, l_long, start + 1, end);
  }
}

// count_poll_tasks_in_range additive across split.
proof fn count_poll_tasks_split_additive(
  l: Log,
  start: int,
  mid: int,
  end: int,
)
  requires
    0 <= start <= mid <= end <= l.len(),
  ensures
    count_poll_tasks_in_range(l, start, end) ==
      count_poll_tasks_in_range(l, start, mid) +
      count_poll_tasks_in_range(l, mid, end),
  decreases mid - start
{
  if start >= mid {
    assert(count_poll_tasks_in_range(l, start, mid) == 0);
  } else {
    count_poll_tasks_split_additive(l, start + 1, mid, end);
  }
}

// Helper: executor_inv preserved across one progress step.
proof fn progress_n_first_step_invariant(
  l_a: Log,
  l_mid: Log,
  l_b: Log,
  n: nat,
)
  requires
    crate::executor::invariants::executor_inv(l_a),
    crate::executor::invariants::executor_inv(l_b),
    crate::executor::executor_progress(l_a, l_mid),
    n >= 1,
  ensures
    crate::executor::invariants::executor_inv(l_mid),
{
  // executor_progress includes executor_inv(l_mid) in its definition.
}

// Queue at l_a.len() coincides between l_a and l_mid (l_a is prefix of l_mid).
proof fn queue_prefix_eq_at_len(l_a: Log, l_mid: Log)
  requires
    is_prefix_of(l_a, l_mid),
  ensures
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(
      l_a, l_a.len() as int
    ) ==
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(
      l_mid, l_a.len() as int
    ),
{
  fifo_queue_prefix_eq(l_a, l_mid, l_a.len() as int);
}

// fifo_queue_at depends only on events [0, i), so prefix equivalence
// preserves it.
proof fn fifo_queue_prefix_eq(l_a: Log, l_long: Log, i: int)
  requires
    is_prefix_of(l_a, l_long),
    0 <= i <= l_a.len(),
  ensures
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(l_a, i) ==
    crate::executor::invariants::fifo_task_selection::fifo_queue_at(l_long, i),
  decreases i
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  if i <= 0 {
  } else {
    fifo_queue_prefix_eq(l_a, l_long, i - 1);
    assert(l_a[i - 1] == l_long[i - 1]);
  }
}

proof fn count_drain_subrange_eq(
  l_full: Log,
  l_sub: Log,
  source: DrainSource,
  start: int,
  end: int,
)
  requires
    0 <= start <= end <= l_sub.len(),
    l_sub.len() <= l_full.len(),
    forall |i: int| 0 <= i < l_sub.len() ==> l_sub[i] == l_full[i],
  ensures
    count_drain_between(l_sub, source, start, end) ==
      count_drain_between(l_full, source, start, end),
  decreases end - start
{
  if start >= end {
  } else {
    assert(l_sub[start] == l_full[start]);
    count_drain_subrange_eq(l_full, l_sub, source, start + 1, end);
  }
}

}
