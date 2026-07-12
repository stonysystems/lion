use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::composed::spec::state::*;
#[cfg(verus_keep_ghost)]
use crate::composed::spec::types::*;
#[cfg(verus_keep_ghost)]
use crate::composed::spec::progress::*;
#[cfg(verus_keep_ghost)]
use crate::composed::spec::contract::*;
#[cfg(verus_keep_ghost)]
use crate::composed::spec::assumptions::*;
#[cfg(verus_keep_ghost)]
use crate::framework::async_contract::*;
#[cfg(verus_keep_ghost)]
use crate::framework::module_spec::progress_preserves_wf;

verus! {

#[verifier::rlimit(800)]
pub proof fn composed_progress_preserves_wf_lemma(s: ComposedState, s_prime: ComposedState)
  requires
    composed_well_formed(s),
    composed_progress(s, s_prime),
  ensures
    composed_well_formed(s_prime),
{
  reveal(composed_progress);

  assert(crate::composed::spec::progress::executor_progress(s.executor_log, s_prime.executor_log));
  assert(crate::executor::executor_progress(s.executor_log, s_prime.executor_log));
  assert(crate::executor::invariants::executor_inv(s_prime.executor_log));

  assert(crate::composed::spec::progress::reactor_progress(s.reactor_log, s_prime.reactor_log));
  assert(crate::reactor::reactor_progress(s.reactor_log, s_prime.reactor_log));
  assert(crate::reactor::invariants::reactor_inv(s_prime.reactor_log));

  operation_alignment_preserved_lemma(s, s_prime);
  assert(crate::composed::spec::alignment::operation_alignment_inv(s_prime));

  pending_poll_inv_preserved_lemma(s, s_prime);
  assert(crate::composed::spec::alignment::pending_poll_inv(s_prime));

  polled_task_has_log_inv_preserved_lemma(s, s_prime);
  assert(crate::composed::spec::alignment::polled_task_has_log_inv(s_prime));

  assert(crate::composed::spec::progress::task_logs_preserve_utilities_inv(s, s_prime));

  // These come from composed_progress directly:
  assert(crate::composed::spec::alignment::monotonic_task_reactor_alignment(s_prime));

  // deregister_matches_own_registration comes from cross_module_alignment:
  reveal(crate::composed::spec::alignment::cross_module_alignment);
  assert(crate::composed::spec::alignment::deregister_matches_own_registration(s_prime));

  // succ_deregister_by_owner is derived:
  crate::composed::proof::deregister_ownership::derive_succ_deregister_by_owner(s_prime);

  // io twin: deregister_io_matches_own_registration comes from cross_module_alignment,
  // and succ_deregister_io_by_owner is DERIVED from it (symmetric to the timer path).
  assert(crate::composed::spec::alignment::deregister_io_matches_own_registration(s_prime));
  crate::composed::proof::deregister_ownership::derive_succ_deregister_io_by_owner(s_prime);
}

#[verifier::rlimit(50)]
proof fn operation_alignment_preserved_lemma(s: ComposedState, s_prime: ComposedState)
  requires
    composed_well_formed(s),
    composed_progress(s, s_prime),
  ensures
    crate::composed::spec::alignment::operation_alignment_inv(s_prime),
{
  reveal(composed_progress);
  use crate::composed::spec::alignment::*;
  reveal(cross_module_alignment);
  assert(cross_module_alignment(s, s_prime));

  assert(crate::reactor::reactor_progress(s.reactor_log, s_prime.reactor_log));
  assert(crate::reactor::invariants::reactor_inv(s_prime.reactor_log));

  assert(new_operation_alignment(s, s_prime));

  assert forall |tid: TaskId, i: int|
    s_prime.task_logs.contains_key(tid) &&
    0 <= i < s_prime.task_logs[tid].len() &&
    is_reactor_operation(#[trigger] s_prime.task_logs[tid][i])
    implies
    exists |j: int|
      0 <= j < s_prime.reactor_log.len() &&
      succ_reactor_event_matches_task_operation(s_prime.reactor_log[j], s_prime.task_logs[tid][i])
  by {
    if s_prime.task_logs.contains_key(tid) &&
       0 <= i < s_prime.task_logs[tid].len() &&
       is_reactor_operation(s_prime.task_logs[tid][i])
    {
      if s.task_logs.contains_key(tid) && i < s.task_logs[tid].len() {
        assert(operation_alignment_inv(s));
        assert(s.task_logs[tid][i] == s_prime.task_logs[tid][i]);
        let j: int = choose |j: int|
          0 <= j < s.reactor_log.len() &&
          succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid][i]);
        assert(s.reactor_log[j] == s_prime.reactor_log[j]);
        assert(succ_reactor_event_matches_task_operation(s_prime.reactor_log[j], s_prime.task_logs[tid][i]));
      } else {
        assert(is_new_task_operation(s, s_prime, tid, i));
        assert(new_operation_alignment(s, s_prime));
      }
    }
  };

  assert(operation_to_reactor_exists(s_prime));

  assert(new_operation_alignment(s, s_prime));
  assert(new_operation_uniqueness(s, s_prime));

  assert forall |tid1: TaskId, tid2: TaskId, task_idx1: int, task_idx2: int, reactor_idx: int|
    s_prime.task_logs.contains_key(tid1) &&
    s_prime.task_logs.contains_key(tid2) &&
    0 <= task_idx1 < s_prime.task_logs[tid1].len() &&
    0 <= task_idx2 < s_prime.task_logs[tid2].len() &&
    is_reactor_operation(#[trigger] s_prime.task_logs[tid1][task_idx1]) &&
    is_reactor_operation(#[trigger] s_prime.task_logs[tid2][task_idx2]) &&
    0 <= reactor_idx < s_prime.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(#[trigger] s_prime.reactor_log[reactor_idx], s_prime.task_logs[tid1][task_idx1]) &&
    succ_reactor_event_matches_task_operation(s_prime.reactor_log[reactor_idx], s_prime.task_logs[tid2][task_idx2])
    implies tid1 == tid2 && task_idx1 == task_idx2
  by {
    if s_prime.task_logs.contains_key(tid1) &&
       s_prime.task_logs.contains_key(tid2) &&
       0 <= task_idx1 < s_prime.task_logs[tid1].len() &&
       0 <= task_idx2 < s_prime.task_logs[tid2].len() &&
       is_reactor_operation(s_prime.task_logs[tid1][task_idx1]) &&
       is_reactor_operation(s_prime.task_logs[tid2][task_idx2]) &&
       0 <= reactor_idx < s_prime.reactor_log.len() &&
       succ_reactor_event_matches_task_operation(s_prime.reactor_log[reactor_idx], s_prime.task_logs[tid1][task_idx1]) &&
       succ_reactor_event_matches_task_operation(s_prime.reactor_log[reactor_idx], s_prime.task_logs[tid2][task_idx2])
    {
      assert(is_extension_of(s, s_prime));
      let is_old_1 = s.task_logs.contains_key(tid1) && task_idx1 < s.task_logs[tid1].len();
      let is_old_2 = s.task_logs.contains_key(tid2) && task_idx2 < s.task_logs[tid2].len();
      let is_old_reactor = reactor_idx < s.reactor_log.len() as int;

      if is_old_reactor {
        assert(s.reactor_log[reactor_idx] == s_prime.reactor_log[reactor_idx]);
        if !is_old_1 {
          assert(is_new_task_operation(s, s_prime, tid1, task_idx1));
          assert(new_op_matches_only_new_reactor(s, s_prime));
          assert(reactor_idx >= s.reactor_log.len());
          assert(false);
        }
        if !is_old_2 {
          assert(is_new_task_operation(s, s_prime, tid2, task_idx2));
          assert(new_op_matches_only_new_reactor(s, s_prime));
          assert(reactor_idx >= s.reactor_log.len());
          assert(false);
        }
        assert(is_old_1 && is_old_2);
        assert(s.task_logs[tid1][task_idx1] == s_prime.task_logs[tid1][task_idx1]);
        assert(s.task_logs[tid2][task_idx2] == s_prime.task_logs[tid2][task_idx2]);
        assert(reactor_to_operation_unique(s));
      } else {
        if is_old_1 {
          assert(operation_to_reactor_exists(s));
          assert(s.task_logs[tid1][task_idx1] == s_prime.task_logs[tid1][task_idx1]);
          let j_old: int = choose |j: int|
            0 <= j < s.reactor_log.len() &&
            succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid1][task_idx1]);
          assert(j_old < s.reactor_log.len());
          assert(reactor_idx >= s.reactor_log.len());
        }
        if is_old_2 {
          assert(operation_to_reactor_exists(s));
          assert(s.task_logs[tid2][task_idx2] == s_prime.task_logs[tid2][task_idx2]);
          let j_old: int = choose |j: int|
            0 <= j < s.reactor_log.len() &&
            succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid2][task_idx2]);
          assert(j_old < s.reactor_log.len());
          assert(reactor_idx >= s.reactor_log.len());
        }
        if !is_old_1 && !is_old_2 {
          assert(is_new_task_operation(s, s_prime, tid1, task_idx1));
          assert(is_new_task_operation(s, s_prime, tid2, task_idx2));
          assert(new_operation_uniqueness(s, s_prime));
        }
      }
    }
  };

  assert(reactor_to_operation_unique(s_prime));

  assert(reactor_outbound_has_task_operation(s, s_prime));

  assert forall |j: int|
    0 <= j < s_prime.reactor_log.len() &&
    (crate::reactor::spec::events::is_succ_register_timer(#[trigger] s_prime.reactor_log[j]) ||
     crate::reactor::spec::events::is_succ_io_syscall_register(s_prime.reactor_log[j]))
    implies
    exists |tid: TaskId, task_idx: int|
      s_prime.task_logs.contains_key(tid) &&
      0 <= task_idx < s_prime.task_logs[tid].len() &&
      succ_reactor_event_matches_task_operation(s_prime.reactor_log[j], s_prime.task_logs[tid][task_idx])
  by {
    if 0 <= j < s_prime.reactor_log.len() &&
       (crate::reactor::spec::events::is_succ_register_timer(s_prime.reactor_log[j]) ||
        crate::reactor::spec::events::is_succ_io_syscall_register(s_prime.reactor_log[j]))
    {
      if j < s.reactor_log.len() as int {
        assert(s.reactor_log[j] == s_prime.reactor_log[j]);
        assert(reactor_registration_to_task_exists(s));
        let tid: TaskId = choose |tid: TaskId|
          #![trigger s.task_logs[tid]]
          exists |task_idx: int|
            #![trigger s.task_logs[tid][task_idx]]
            s.task_logs.contains_key(tid) &&
            0 <= task_idx < s.task_logs[tid].len() &&
            succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid][task_idx]);
        let task_idx: int = choose |task_idx: int|
          #![trigger s.task_logs[tid][task_idx]]
          s.task_logs.contains_key(tid) &&
          0 <= task_idx < s.task_logs[tid].len() &&
          succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid][task_idx]);
        assert(is_extension_of(s, s_prime));
        assert(s_prime.task_logs.contains_key(tid));
        assert(is_task_log_prefix(s.task_logs[tid], s_prime.task_logs[tid]));
        assert(s_prime.task_logs[tid][task_idx] == s.task_logs[tid][task_idx]);
        assert(task_idx < s_prime.task_logs[tid].len());
        assert(succ_reactor_event_matches_task_operation(s_prime.reactor_log[j], s_prime.task_logs[tid][task_idx]));
      } else {
        assert(is_task_initiated_reactor_event(s_prime.reactor_log[j]));
        assert(reactor_outbound_has_task_operation(s, s_prime));
      }
    }
  };
  assert(reactor_registration_to_task_exists(s_prime));
  assert forall |j: int|
    0 <= j < s_prime.reactor_log.len() &&
    is_task_initiated_reactor_event(#[trigger] s_prime.reactor_log[j])
    implies
    exists |tid: TaskId, task_idx: int|
      s_prime.task_logs.contains_key(tid) &&
      0 <= task_idx < s_prime.task_logs[tid].len() &&
      succ_reactor_event_matches_task_operation(s_prime.reactor_log[j], s_prime.task_logs[tid][task_idx])
  by {
    if 0 <= j < s_prime.reactor_log.len() &&
       is_task_initiated_reactor_event(s_prime.reactor_log[j])
    {
      if j < s.reactor_log.len() as int {
        assert(s.reactor_log[j] == s_prime.reactor_log[j]);
        assert(reactor_outbound_to_task_exists(s));
        let tid: TaskId = choose |tid: TaskId|
          #![trigger s.task_logs[tid]]
          exists |task_idx: int|
            #![trigger s.task_logs[tid][task_idx]]
            s.task_logs.contains_key(tid) &&
            0 <= task_idx < s.task_logs[tid].len() &&
            succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid][task_idx]);
        let task_idx: int = choose |task_idx: int|
          #![trigger s.task_logs[tid][task_idx]]
          s.task_logs.contains_key(tid) &&
          0 <= task_idx < s.task_logs[tid].len() &&
          succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid][task_idx]);
        assert(is_extension_of(s, s_prime));
        assert(s_prime.task_logs.contains_key(tid));
        assert(is_task_log_prefix(s.task_logs[tid], s_prime.task_logs[tid]));
        assert(s_prime.task_logs[tid][task_idx] == s.task_logs[tid][task_idx]);
        assert(task_idx < s_prime.task_logs[tid].len());
        assert(succ_reactor_event_matches_task_operation(s_prime.reactor_log[j], s_prime.task_logs[tid][task_idx]));
      } else {
        assert(reactor_outbound_has_task_operation(s, s_prime));
      }
    }
  };
  assert(reactor_outbound_to_task_exists(s_prime));
}

proof fn find_last_poll_scan(
  l: crate::executor::spec::log::Log,
  tid: TaskId,
  pos: int,
  best: int,
)
  requires
    0 <= best < l.len(),
    crate::executor::spec::log::is_poll_task_for_id_at(l, best, tid),
    forall |j: int| best < j < pos ==>
      !crate::executor::spec::log::is_poll_task_for_id_at(l, j, tid),
    0 <= pos <= l.len(),
    best < pos,
  ensures
    exists |i: int|
      0 <= i < l.len() &&
      crate::executor::spec::log::is_poll_task_for_id_at(l, i, tid) &&
      forall |j: int| i < j < l.len() ==>
        !crate::executor::spec::log::is_poll_task_for_id_at(l, j, tid),
  decreases l.len() - pos,
{
  if pos == l.len() as int {
  } else if crate::executor::spec::log::is_poll_task_for_id_at(l, pos, tid) {
    find_last_poll_scan(l, tid, pos + 1, pos);
  } else {
    find_last_poll_scan(l, tid, pos + 1, best);
  }
}

pub proof fn last_poll_idx_properties(
  l: crate::executor::spec::log::Log,
  tid: TaskId,
)
  requires
    crate::executor::spec::log::has_poll_for_id(l, tid),
  ensures
    ({
      let idx = crate::executor::spec::log::last_poll_idx_for_id(l, tid);
      0 <= idx < l.len() &&
      crate::executor::spec::log::is_poll_task_for_id_at(l, idx, tid) &&
      forall |j: int| idx < j < l.len() ==>
        !crate::executor::spec::log::is_poll_task_for_id_at(l, j, tid)
    }),
{
  let first: int = choose |i: int|
    #![trigger l[i]]
    0 <= i < l.len() && crate::executor::spec::log::is_poll_task_for_id_at(l, i, tid);
  find_last_poll_scan(l, tid, first + 1, first);
}

// If a's last poll of tid is Pending and b (a prefix-extension of a) adds NO new
// poll of tid, then b's last poll of tid is still that same Pending poll. The
// "unconsumed" preservation used by the P4b window wake-delivery clause.
pub proof fn last_poll_pending_prefix_stable(
  a: crate::executor::spec::log::Log,
  b: crate::executor::spec::log::Log,
  tid: TaskId,
)
  requires
    crate::executor::spec::log::is_prefix_of(a, b),
    crate::executor::spec::log::last_poll_is_pending(a, tid),
    !crate::executor::spec::log::has_poll_task_for_id_after(b, tid, a.len() as int),
  ensures
    crate::executor::spec::log::last_poll_is_pending(b, tid),
{
  use crate::executor::spec::log::*;
  let p = last_poll_idx_for_id(a, tid);
  last_poll_idx_properties(a, tid);
  assert(0 <= p < a.len());
  assert(is_poll_pending_for_id_at(a, p, tid));
  assert(a[p] == b[p]);
  assert(is_poll_task_for_id_at(b, p, tid));
  assert(has_poll_for_id(b, tid));
  assert forall |j: int| p < j < b.len() implies !is_poll_task_for_id_at(b, j, tid) by {
    if j < a.len() {
      assert(a[j] == b[j]);
      assert(!is_poll_task_for_id_at(a, j, tid));
    } else {
      assert(a.len() as int <= j < b.len());
      assert(!is_poll_task_for_id_at(b, j, tid));
    }
  }
  last_poll_idx_properties(b, tid);
  let q = last_poll_idx_for_id(b, tid);
  assert(q == p) by {
    if q > p {
      assert(is_poll_task_for_id_at(b, q, tid));
    } else if q < p {
      assert(is_poll_task_for_id_at(b, p, tid));
    }
  }
  assert(b[p] == a[p]);
}

#[verifier::rlimit(40)]
proof fn pending_poll_inv_old_event_helper(
  s: ComposedState,
  s_prime: ComposedState,
  tid: TaskId,
  last_idx: int,
)
  requires
    composed_well_formed(s),
    composed_progress(s, s_prime),
    s_prime.task_logs.contains_key(tid),
    crate::executor::spec::log::last_poll_is_pending(s_prime.executor_log, tid),
    last_idx == crate::executor::spec::log::last_poll_idx_for_id(s_prime.executor_log, tid),
    last_idx < s.executor_log.len(),
    crate::executor::spec::log::is_poll_pending_for_id_at(s.executor_log, last_idx, tid),
  ensures
    crate::composed::spec::alignment::task_log_ends_with_pending(s_prime.task_logs[tid]),
{
  reveal(composed_progress);
  use crate::composed::spec::alignment::*;
  reveal(cross_module_alignment);
  assert(is_extension_of(s, s_prime));
  assert(polled_task_has_log_inv(s));
  assert(pending_poll_inv(s));

  // Extract "no later poll" from last_poll_idx_for_id(s_prime.executor_log, tid)
  last_poll_idx_properties(s_prime.executor_log, tid);
  assert(forall |j: int| last_idx < j < s_prime.executor_log.len() ==>
    !crate::executor::spec::log::is_poll_task_for_id_at(s_prime.executor_log, j, tid));

  assert(crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, last_idx, tid));
  assert(crate::executor::spec::log::has_poll_for_id(s.executor_log, tid));
  assert(s.task_logs.contains_key(tid));

  // last_poll_is_pending(s.executor_log, tid): use last_poll_idx_properties for s too
  last_poll_idx_properties(s.executor_log, tid);
  let s_last = crate::executor::spec::log::last_poll_idx_for_id(s.executor_log, tid);

  // s_last <= last_idx: if s_last > last_idx, s_last is after last_idx in s, hence also in s_prime,
  // contradicting last_idx being the last poll in s_prime
  assert(s_last <= last_idx) by {
    if s_last > last_idx {
      assert(s_last < s.executor_log.len());
      assert(s.executor_log[s_last] == s_prime.executor_log[s_last]);
      assert(crate::executor::spec::log::is_poll_task_for_id_at(s_prime.executor_log, s_last, tid));
      assert(!crate::executor::spec::log::is_poll_task_for_id_at(s_prime.executor_log, s_last, tid));
    }
  };

  // s_last >= last_idx: last_idx is a poll in s, and s_last is the last poll in s
  assert(s_last >= last_idx) by {
    if s_last < last_idx {
      assert(crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, last_idx, tid));
      assert(!crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, last_idx, tid));
    }
  };

  assert(crate::executor::spec::log::last_poll_is_pending(s.executor_log, tid));
  assert(task_log_ends_with_pending(s.task_logs[tid]));

  // No poll for tid in new events → task log unchanged
  assert(poll_alignment(s, s_prime));
  assert(!task_polled_during_progress(s_prime.executor_log, tid, s.executor_log.len() as int)) by {
    assert forall |k: int| s.executor_log.len() as int <= k < s_prime.executor_log.len()
      implies !crate::executor::spec::log::is_poll_task_for_id_at(s_prime.executor_log, k, tid)
    by {
      assert(k > last_idx);
    };
  };
  let old_len = s.task_logs[tid].len();
  let new_len = s_prime.task_logs[tid].len();
  assert(is_task_log_prefix(s.task_logs[tid], s_prime.task_logs[tid]));
  assert(old_len <= new_len);
  assert(old_len >= new_len) by {
    if old_len < new_len {
      assert(task_polled_during_progress(s_prime.executor_log, tid, s.executor_log.len() as int));
    }
  };
  assert(s.task_logs[tid].last() == s_prime.task_logs[tid].last()) by {
    assert(s.task_logs[tid][old_len - 1] == s_prime.task_logs[tid][old_len - 1]);
  };
}

proof fn pending_poll_inv_preserved_lemma(s: ComposedState, s_prime: ComposedState)
  requires
    composed_well_formed(s),
    composed_progress(s, s_prime),
  ensures
    crate::composed::spec::alignment::pending_poll_inv(s_prime),
{
  reveal(composed_progress);
  use crate::composed::spec::alignment::*;
  reveal(cross_module_alignment);
  assert(cross_module_alignment(s, s_prime));
  assert(pending_poll_alignment(s, s_prime));
  assert(pending_poll_inv(s));

  assert forall |tid: TaskId|
    s_prime.task_logs.contains_key(tid) &&
    crate::executor::spec::log::last_poll_is_pending(s_prime.executor_log, tid)
    implies
    task_log_ends_with_pending(#[trigger] s_prime.task_logs[tid])
  by {
    if s_prime.task_logs.contains_key(tid) &&
       crate::executor::spec::log::last_poll_is_pending(s_prime.executor_log, tid)
    {
      let last_idx = crate::executor::spec::log::last_poll_idx_for_id(s_prime.executor_log, tid);
      if last_idx >= s.executor_log.len() as int {
        assert(crate::executor::spec::log::is_poll_pending_for_id_at(s_prime.executor_log, last_idx, tid));
        assert(pending_poll_alignment(s, s_prime));
      } else {
        assert(crate::executor::spec::log::is_poll_pending_for_id_at(s_prime.executor_log, last_idx, tid));
        assert(s_prime.executor_log[last_idx] == s.executor_log[last_idx]);
        assert(crate::executor::spec::log::is_poll_pending_for_id_at(s.executor_log, last_idx, tid));

        assert(crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, last_idx, tid));
        assert(crate::executor::spec::log::has_poll_for_id(s.executor_log, tid));

        assert(polled_task_has_log_inv(s));
        assert(s.task_logs.contains_key(tid));

        pending_poll_inv_old_event_helper(s, s_prime, tid, last_idx);
      }
    }
  };
}


proof fn polled_task_has_log_inv_preserved_lemma(s: ComposedState, s_prime: ComposedState)
  requires
    composed_well_formed(s),
    composed_progress(s, s_prime),
  ensures
    crate::composed::spec::alignment::polled_task_has_log_inv(s_prime),
{
  reveal(composed_progress);
  use crate::composed::spec::alignment::*;
  reveal(cross_module_alignment);
  assert(is_extension_of(s, s_prime));
  assert(polled_task_has_log_inv(s));
  assert(new_poll_has_task_log(s, s_prime));

  assert forall |tid: TaskId|
    crate::executor::spec::log::has_poll_for_id(s_prime.executor_log, tid)
    implies
    s_prime.task_logs.contains_key(tid)
  by {
    if crate::executor::spec::log::has_poll_for_id(s_prime.executor_log, tid) {
      let poll_idx: int = choose |i: int|
        #![trigger s_prime.executor_log[i]]
        0 <= i < s_prime.executor_log.len() &&
        crate::executor::spec::log::is_poll_task_for_id_at(s_prime.executor_log, i, tid);
      if poll_idx < s.executor_log.len() as int {
        assert(s.executor_log[poll_idx] == s_prime.executor_log[poll_idx]);
        assert(crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, poll_idx, tid));
        assert(crate::executor::spec::log::has_poll_for_id(s.executor_log, tid));
        assert(s.task_logs.contains_key(tid));
        assert(s_prime.task_logs.contains_key(tid));
      } else {
        assert(new_poll_has_task_log(s, s_prime));
        // Explicitly put trigger terms in scope
        assert(s_prime.executor_log[poll_idx] == s_prime.executor_log[poll_idx]);
        let _tl = s_prime.task_logs[tid];
        assert(s.executor_log.len() as int <= poll_idx);
        assert(crate::executor::spec::log::is_poll_task_for_id_at(s_prime.executor_log, poll_idx, tid));
      }
    }
  };
}

pub proof fn progress_preserves_wf_helper()
  ensures
    progress_preserves_wf(composed_module_spec()),
{
  assert forall |s: ComposedState, s_prime: ComposedState|
    composed_well_formed(s) && composed_progress(s, s_prime)
    implies composed_well_formed(s_prime)
  by {
    composed_progress_preserves_wf_lemma(s, s_prime);
  };
}

proof fn extends_k_then_one(
  l: crate::reactor::spec::log::Log,
  l_mid: crate::reactor::spec::log::Log,
  l_prime: crate::reactor::spec::log::Log,
  k: nat,
)
  requires
    crate::reactor::proof::round_extension::extends_by_k_rounds(l, l_mid, k),
    crate::reactor::proof::round_extension::extends_by_one_round(l_mid, l_prime),
  ensures
    crate::reactor::proof::round_extension::extends_by_k_rounds(l, l_prime, k + 1),
  decreases k,
{
  reveal(composed_progress);
  use crate::reactor::proof::round_extension::{extends_by_k_rounds, extends_by_one_round};
  if k == 0 {
    assert(l == l_mid);
    assert(extends_by_one_round(l, l_prime));
    assert(extends_by_k_rounds(l_prime, l_prime, 0nat));
  } else {
    let l_first: crate::reactor::spec::log::Log = choose |l_first: crate::reactor::spec::log::Log|
      extends_by_one_round(l, l_first) &&
      extends_by_k_rounds(l_first, l_mid, (k - 1) as nat);
    extends_k_then_one(l_first, l_mid, l_prime, (k - 1) as nat);
  }
}

pub proof fn composed_progress_n_implies_reactor_k_rounds(
  s: ComposedState, s_prime: ComposedState, n: nat,
)
  requires
    crate::framework::module_spec::progress_n(composed_module_spec().progress, s, s_prime, n),
  ensures
    crate::reactor::proof::round_extension::extends_by_k_rounds(
      s.reactor_log, s_prime.reactor_log, n
    ),
  decreases n,
{
  reveal(composed_progress);
  use crate::reactor::proof::round_extension::extends_by_k_rounds;
  use crate::framework::module_spec::{progress_n, is_valid_trace};
  if n == 0 {
    assert(s == s_prime);
  } else {
    let trace: Seq<ComposedState> = choose |trace: Seq<ComposedState>|
      #![trigger trace.len()]
      trace.len() == n + 1 &&
      trace.first() == s &&
      trace.last() == s_prime &&
      is_valid_trace(composed_module_spec().progress, trace);

    let s_prev = trace[n as int - 1];
    assert(composed_progress(s_prev, s_prime));
    assert(crate::reactor::reactor_progress(s_prev.reactor_log, s_prime.reactor_log));

    let subtrace = trace.subrange(0, n as int);
    assert(subtrace.len() == n);
    assert(subtrace.first() == s);
    assert(subtrace.last() == s_prev);
    assert(is_valid_trace(composed_module_spec().progress, subtrace)) by {
      assert forall |i: int| 0 <= i < subtrace.len() - 1 implies
        (composed_module_spec().progress)(#[trigger] subtrace[i], subtrace[i + 1])
      by {
        assert(subtrace[i] == trace[i]);
        assert(subtrace[i + 1] == trace[i + 1]);
      };
    };
    composed_progress_n_implies_reactor_k_rounds(s, s_prev, (n - 1) as nat);
    extends_k_then_one(s.reactor_log, s_prev.reactor_log, s_prime.reactor_log, (n - 1) as nat);
  }
}

pub proof fn progress_n_implies_extension(s: ComposedState, s_prime: ComposedState, n: nat)
  requires
    crate::framework::module_spec::progress_n(composed_module_spec().progress, s, s_prime, n),
  ensures
    is_extension_of(s, s_prime),
{
  reveal(composed_progress);
  if n == 0 {
    assert(s == s_prime);
  } else {
    let trace: Seq<ComposedState> = choose |trace: Seq<ComposedState>|
      #![trigger trace.len()]
      trace.len() == n + 1 &&
      trace.first() == s &&
      trace.last() == s_prime &&
      crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, trace);

    assert forall |i: int| 0 <= i < trace.len() - 1 implies
      is_extension_of(#[trigger] trace[i], trace[i + 1])
    by {
      assert(composed_progress(trace[i], trace[i + 1]));
    };

    extension_transitive_trace(trace);
  }
}

proof fn extension_transitive_trace(trace: Seq<ComposedState>)
  requires
    trace.len() >= 1,
    forall |i: int| 0 <= i < trace.len() - 1 ==>
      is_extension_of(#[trigger] trace[i], trace[i + 1]),
  ensures
    is_extension_of(trace.first(), trace.last()),
  decreases trace.len()
{
  if trace.len() == 1 {
    assert(trace.first() == trace.last());
  } else if trace.len() == 2 {
    assert(is_extension_of(trace[0], trace[1]));
    assert(trace.first() == trace[0]);
    assert(trace.last() == trace[1]);
  } else {
    let subtrace = trace.subrange(1, trace.len() as int);
    assert(subtrace.len() == trace.len() - 1);
    assert(subtrace.first() == trace[1]);
    assert(subtrace.last() == trace.last());

    assert forall |i: int| 0 <= i < subtrace.len() - 1 implies
      is_extension_of(#[trigger] subtrace[i], subtrace[i + 1])
    by {
      assert(subtrace[i] == trace[i + 1]);
      assert(subtrace[i + 1] == trace[i + 2]);
      assert(is_extension_of(trace[i + 1], trace[i + 2]));
    };

    extension_transitive_trace(subtrace);
    assert(is_extension_of(trace[1], trace.last()));
    assert(is_extension_of(trace[0], trace[1]));
    extension_transitive(trace[0], trace[1], trace.last());
  }
}

proof fn extension_transitive(a: ComposedState, b: ComposedState, c: ComposedState)
  requires
    is_extension_of(a, b),
    is_extension_of(b, c),
  ensures
    is_extension_of(a, c),
{
}

// ============================================================================
// Step-Counting Induction: bound = n * max_wakeup_bound provides n polls
// ============================================================================
//
// This section contains the core step-counting argument decomposed into
// sub-lemmas. The proof proceeds by induction on n:
//
// Base case (n = 0): Trivially satisfied (0 polls needed)
//
// Inductive case (n > 0):
//   1. First poll from bounded_injection_poll (arrival → first poll)
//   2. If poll returns Ready: done (n = 1 suffices)
//   3. If poll returns Pending:
//      - wakeup_guarantee → active wakeup source exists
//      - timer/io/defer/taskwake → path fires within max_wakeup_bound steps
//      - contract_chaining → WakeTask leads to queue arrival
//      - bounded_drain_poll → next poll within bounded steps
//   4. By IH on (n-1), remaining (n-1) * max_wakeup_bound steps give (n-1) more polls
//
// ============================================================================

// (Removed: `first_poll_from_arrival` — replaced by
// `contract_bridges::first_poll_from_arrival_via_contract`, which consumes
// the verified `bounded_injection_poll_per_instance` executor lemma
// instead of re-deriving the injection-arrival-to-poll argument inline.)

// ============================================================================
// Wakeup Cycle Sub-Lemmas
// ============================================================================
//
// The wakeup cycle is decomposed into sub-lemmas:
//
// 1. pending_has_wakeup_source: Pending → has_active_wakeup_source
//    (from wakeup_guarantee in utilities_inv)
//
// 2. timer_io_case_leads_to_poll: Timer/IO source → poll
//    (reactor liveness → WakeTask → drain → poll)
//
// 3. wake_task_leads_to_poll: WakeTask → poll
//    (from new_wake_new_drain_alignment + tick_drains_queue)
//
// ============================================================================

// Sub-lemma 1: Pending implies active wakeup source
// Uses pending_poll_inv + wakeup_guarantee from utilities_inv
pub proof fn pending_has_wakeup_source(
  s: ComposedState,
  tid: TaskId,
  pending_idx: int,
)
  requires
    composed_well_formed(s),
    is_task_pending_at(s, tid, pending_idx),
    s.task_logs.contains_key(tid),
    forall |j: int| pending_idx < j < s.executor_log.len() ==>
      !crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, j, tid),
  ensures
    crate::utilities::spec::log::has_active_wakeup_source(
      s.task_logs[tid],
      (s.task_logs[tid].len() - 1) as int
    ),
{
  use crate::executor::spec::log::*;
  use crate::composed::spec::alignment::*;
  use crate::utilities::spec::events::is_poll_end_pending;

  // Step 1: pending_idx is the last poll for tid
  // Show has_poll_for_id(s.executor_log, tid)
  assert(is_poll_pending_for_id_at(s.executor_log, pending_idx, tid));
  assert(is_poll_task_for_id_at(s.executor_log, pending_idx, tid));
  assert(has_poll_for_id(s.executor_log, tid));

  // Step 2: Show last_poll_is_pending(s.executor_log, tid)
  // pending_idx is a poll for tid with no later poll → it equals last_poll_idx_for_id
  let last_idx = last_poll_idx_for_id(s.executor_log, tid);
  // last_idx satisfies: is_poll_task_for_id_at(l, last_idx, tid) and no later poll
  // pending_idx also satisfies this. By uniqueness of "last", last_idx == pending_idx
  // (both are polls for tid with no later poll; if last_idx != pending_idx, one is after the other, contradiction)
  assert(is_poll_task_for_id_at(s.executor_log, last_idx, tid));
  assert(forall |j: int| last_idx < j < s.executor_log.len() ==>
    !is_poll_task_for_id_at(s.executor_log, j, tid));
  // Since pending_idx is a poll and no poll exists after pending_idx,
  // last_idx <= pending_idx (last_idx can't be after pending_idx since no later poll exists)
  // And last_idx >= pending_idx (pending_idx is a poll, and last_idx is the last one)
  // Therefore last_idx == pending_idx
  if last_idx < pending_idx {
    // Contradiction: pending_idx is a poll after last_idx, but last_idx has no later polls
    assert(is_poll_task_for_id_at(s.executor_log, pending_idx, tid));
    assert(last_idx < pending_idx);
    assert(pending_idx < s.executor_log.len());
    assert(false);
  }
  if last_idx > pending_idx {
    // Contradiction: last_idx is after pending_idx, but no poll exists after pending_idx
    assert(!is_poll_task_for_id_at(s.executor_log, last_idx, tid));
    assert(false);
  }
  assert(last_idx == pending_idx);
  assert(is_poll_pending_for_id_at(s.executor_log, last_idx, tid));
  assert(last_poll_is_pending(s.executor_log, tid));

  // Step 3: By pending_poll_inv(s), task_log_ends_with_pending
  assert(pending_poll_inv(s));
  assert(task_log_ends_with_pending(s.task_logs[tid]));

  // Step 4: task_log_ends_with_pending means is_poll_end_pending(l.last())
  let task_log = s.task_logs[tid];
  let last_task_idx = (task_log.len() - 1) as int;
  assert(is_poll_end_pending(task_log.last()));
  assert(is_poll_end_pending(task_log[last_task_idx]));

  // Step 5: By wakeup_guarantee from utilities_inv
  assert(crate::utilities::invariants::wakeup_guarantee::utilities_inv(task_log));
  assert(crate::framework::action_safety::action_safety_satisfied(
    crate::utilities::invariants::wakeup_guarantee::wakeup_guarantee(),
    task_log
  ));
  let wg = crate::utilities::invariants::wakeup_guarantee::wakeup_guarantee();
  assert((wg.acceptance)(task_log, last_task_idx));
  assert((wg.validity)(task_log, last_task_idx));
}

// Helper: Drain event adds its tasks to the queue
pub proof fn drain_adds_tid_to_queue(
  l: crate::executor::spec::log::Log,
  tid: TaskId,
  drain_idx: int,
)
  requires
    0 <= drain_idx < l.len(),
    crate::executor::spec::log::is_drain_at(l, drain_idx),
    crate::executor::spec::log::task_id_in_drain_at(l, drain_idx, tid),
  ensures
    tid_in_fifo_queue_at(l, drain_idx + 1, tid),
{
  use crate::executor::invariants::fifo_task_selection::fifo_queue_at;
  use crate::executor::spec::log::*;
  use crate::executor::spec::events::*;

  let queue_before = fifo_queue_at(l, drain_idx);
  let queue_after = fifo_queue_at(l, drain_idx + 1);
  let e = l[drain_idx];

  // fifo_queue_at definition: if is_drain(e), queue_after = queue_before + drain_tids
  assert(is_drain(e));
  let drain_tids = get_drain_task_ids(e);
  assert(queue_after =~= queue_before + drain_tids);

  // task_id_in_drain_at means tid is in drain_tids
  let k: int = choose |k: int| 0 <= k < drain_tids.len() && drain_tids[k] == tid;

  // tid is at position queue_before.len() + k in queue_after
  let new_pos = (queue_before.len() + k) as int;
  assert(queue_after[new_pos] == drain_tids[k]);
  assert(queue_after[new_pos] == tid);
}

// Helper: tid in queue at start → either polled in [start, end) or still in queue at end
pub proof fn tid_survives_or_polled_in_range(
  l: crate::executor::spec::log::Log,
  tid: TaskId,
  start: int,
  end: int,
)
  requires
    0 < start <= end <= l.len(),
    tid_in_fifo_queue_at(l, start, tid),
  ensures
    (exists |poll_idx: int|
      start <= poll_idx < end &&
      crate::executor::spec::log::is_poll_task_for_id_at(l, poll_idx, tid))
    ||
    tid_in_fifo_queue_at(l, end, tid),
  decreases end - start
{
  if start == end {
  } else {
    if crate::executor::spec::log::is_poll_task_at(l, start) &&
       crate::executor::spec::events::get_poll_task_id(l[start]) == tid {
      assert(crate::executor::spec::log::is_poll_task_for_id_at(l, start, tid));
    } else {
      tid_preserved_in_queue_step(l, tid, start);
      tid_survives_or_polled_in_range(l, tid, start + 1, end);
    }
  }
}

// Helper: Check if tid is in the FIFO queue at position i
pub open spec fn tid_in_fifo_queue_at(
  l: crate::executor::spec::log::Log,
  i: int,
  tid: TaskId
) -> bool {
  let queue = crate::executor::invariants::fifo_task_selection::fifo_queue_at(l, i);
  exists |k: int| 0 <= k < queue.len() && #[trigger] queue[k] == tid
}

// Helper: If tid is in queue at i and event at i is not PollTask(tid), tid is in queue at i+1
pub proof fn tid_preserved_in_queue_step(
  l: crate::executor::spec::log::Log,
  tid: TaskId,
  i: int,
)
  requires
    0 <= i < l.len(),
    tid_in_fifo_queue_at(l, i, tid),
    !(crate::executor::spec::log::is_poll_task_at(l, i) &&
      crate::executor::spec::events::get_poll_task_id(l[i]) == tid),
  ensures
    tid_in_fifo_queue_at(l, i + 1, tid),
{
  use crate::executor::invariants::fifo_task_selection::*;
  use crate::executor::spec::log::*;
  use crate::executor::spec::events::*;

  let queue_i = fifo_queue_at(l, i);
  let queue_next = fifo_queue_at(l, i + 1);
  let e = l[i];

  // tid is in queue_i
  let k: int = choose |k: int| 0 <= k < queue_i.len() && queue_i[k] == tid;

  if is_pop_injection(e) && get_pop_injection_task(e).is_some() {
    // Entry: queue_next = queue_i + [new_tid]
    // tid was in queue_i, so tid is in queue_next
    assert(queue_next =~= queue_i.push(get_pop_injection_task(e).unwrap().id));
    assert(queue_next[k] == queue_i[k]);
    assert(queue_next[k] == tid);
  } else if is_drain(e) {
    // Entry: queue_next = queue_i + drain_tids
    let drain_tids = get_drain_task_ids(e);
    assert(queue_next =~= queue_i + drain_tids);
    assert(queue_next[k] == queue_i[k]);
    assert(queue_next[k] == tid);
  } else if is_poll_task(e) {
    // Removal: queue_next = remove_first_occurrence(queue_i, polled_tid)
    let polled_tid = get_poll_task_id(e);
    assert(polled_tid != tid);  // From precondition
    assert(queue_next =~= remove_first_occurrence(queue_i, polled_tid));
    // tid is still in queue_next because we removed a different task
    remove_other_preserves_member(queue_i, polled_tid, tid, k);
  } else {
    // Other events don't affect queue
    assert(queue_next =~= queue_i);
    assert(queue_next[k] == tid);
  }
}

// Helper: Progress chain preserves well-formedness
proof fn progress_n_preserves_wf_chain(trace: Seq<ComposedState>, k: int)
  requires
    trace.len() >= 1,
    0 <= k < trace.len(),
    composed_well_formed(trace[0]),
    crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, trace),
  ensures
    composed_well_formed(trace[k]),
  decreases k
{
  if k == 0 {
    // Base case
  } else {
    progress_n_preserves_wf_chain(trace, k - 1);
    assert(composed_progress(trace[k - 1], trace[k]));
    composed_progress_preserves_wf_lemma(trace[k - 1], trace[k]);
  }
}

#[verifier::rlimit(100)]

// Helper: trace[0].executor_log is prefix of trace[k].executor_log
proof fn trace_executor_log_extension(
  trace: Seq<ComposedState>,
  k: int,
)
  requires
    trace.len() >= 1,
    0 <= k < trace.len(),
    crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, trace),
  ensures
    crate::executor::spec::log::is_prefix_of(
      trace[0].executor_log,
      trace[k].executor_log
    ),
  decreases k
{
  reveal(composed_progress);
  if k == 0 {
    // trace[0].executor_log is prefix of itself
  } else {
    trace_executor_log_extension(trace, k - 1);
    assert(composed_progress(trace[k - 1], trace[k]));
    assert(is_extension_of(trace[k - 1], trace[k]));
    // is_extension_of implies executor_log prefix
    assert(crate::executor::spec::log::is_prefix_of(
      trace[k - 1].executor_log,
      trace[k].executor_log
    ));
    // Transitivity of prefix
    prefix_transitive(trace[0].executor_log, trace[k - 1].executor_log, trace[k].executor_log);
  }
}

// Helper: Prefix is transitive for executor logs
proof fn prefix_transitive(
  a: crate::executor::spec::log::Log,
  b: crate::executor::spec::log::Log,
  c: crate::executor::spec::log::Log,
)
  requires
    crate::executor::spec::log::is_prefix_of(a, b),
    crate::executor::spec::log::is_prefix_of(b, c),
  ensures
    crate::executor::spec::log::is_prefix_of(a, c),
{
  // a is prefix of b: a.len() <= b.len() and forall i < a.len(): a[i] == b[i]
  // b is prefix of c: b.len() <= c.len() and forall i < b.len(): b[i] == c[i]
  // Therefore: a.len() <= c.len() and forall i < a.len(): a[i] == c[i]
}

proof fn trace_preserves_task_log_key(
  trace: Seq<ComposedState>,
  tid: TaskId,
  k: int,
)
  requires
    trace.len() >= 1,
    0 <= k < trace.len(),
    crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, trace),
    trace[0].task_logs.contains_key(tid),
  ensures
    trace[k].task_logs.contains_key(tid),
    trace[k].task_logs[tid].len() >= trace[0].task_logs[tid].len(),
  decreases k
{
  reveal(composed_progress);
  if k == 0 {
  } else {
    trace_preserves_task_log_key(trace, tid, k - 1);
    assert(composed_progress(trace[k - 1], trace[k]));
    assert(is_extension_of(trace[k - 1], trace[k]));
  }
}

proof fn extract_poll_from_progress(
  s: ComposedState,
  s_prime: ComposedState,
  tid: TaskId,
)
  requires
    composed_progress(s, s_prime),
    s.task_logs.contains_key(tid),
    s_prime.task_logs.contains_key(tid),
    s_prime.task_logs[tid].len() > s.task_logs[tid].len(),
  ensures
    crate::composed::spec::alignment::task_polled_during_progress(
      s_prime.executor_log, tid, s.executor_log.len() as int
    ),
{
  reveal(composed_progress);
  reveal(crate::composed::spec::alignment::cross_module_alignment);
  assert(crate::composed::spec::alignment::cross_module_alignment(s, s_prime));
  assert(crate::composed::spec::alignment::poll_alignment(s, s_prime));
}

// Helper: poll found in step [n-1,n] is valid in trace[n]
#[verifier::rlimit(50)]
proof fn poll_in_current_step(
  trace: Seq<ComposedState>,
  tid: TaskId,
  n: int,
)
  requires
    trace.len() > n,
    n >= 1,
    crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, trace),
    composed_well_formed(trace[0]),
    trace[0].task_logs.contains_key(tid),
    trace[n].task_logs[tid].len() > trace[n - 1].task_logs[tid].len(),
  ensures
    exists |poll_idx: int|
      #![trigger trace[n].executor_log[poll_idx]]
      trace[n - 1].executor_log.len() as int <= poll_idx < trace[n].executor_log.len() &&
      crate::executor::spec::log::is_poll_task_for_id_at(trace[n].executor_log, poll_idx, tid),
{
  reveal(composed_progress);
  trace_preserves_task_log_key(trace, tid, (n - 1) as int);
  assert(trace[n].task_logs.contains_key(tid));
  assert(composed_progress(trace[n - 1], trace[n]));
  extract_poll_from_progress(trace[n - 1], trace[n], tid);
}

// Helper: poll found in trace[n-1] is preserved in trace[n]
#[verifier::rlimit(50)]
proof fn poll_preserved_by_progress(
  trace: Seq<ComposedState>,
  tid: TaskId,
  poll_idx: int,
  n: int,
)
  requires
    trace.len() > n,
    n >= 1,
    crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, trace),
    trace[0].executor_log.len() as int <= poll_idx < trace[n - 1].executor_log.len(),
    crate::executor::spec::log::is_poll_task_for_id_at(trace[n - 1].executor_log, poll_idx, tid),
  ensures
    poll_idx < trace[n].executor_log.len(),
    crate::executor::spec::log::is_poll_task_for_id_at(trace[n].executor_log, poll_idx, tid),
{
  reveal(composed_progress);
  assert(composed_progress(trace[n - 1], trace[n]));
  assert(is_extension_of(trace[n - 1], trace[n]));
  assert(crate::executor::spec::log::is_prefix_of(trace[n - 1].executor_log, trace[n].executor_log));
  assert(trace[n].executor_log[poll_idx] == trace[n - 1].executor_log[poll_idx]);
}

// Recursive proof: task log growth implies poll exists.
#[verifier::rlimit(50)]
pub proof fn task_log_growth_implies_poll(
  trace: Seq<ComposedState>,
  tid: TaskId,
  n: int,
)
  requires
    trace.len() > n,
    n >= 1,
    crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, trace),
    composed_well_formed(trace[0]),
    trace[0].task_logs.contains_key(tid),
    trace[n].task_logs[tid].len() > trace[0].task_logs[tid].len(),
  ensures
    exists |poll_idx: int|
      #![trigger trace[n].executor_log[poll_idx]]
      trace[0].executor_log.len() as int <= poll_idx < trace[n].executor_log.len() &&
      crate::executor::spec::log::is_poll_task_for_id_at(trace[n].executor_log, poll_idx, tid),
  decreases n
{
  reveal(composed_progress);
  trace_preserves_task_log_key(trace, tid, (n - 1) as int);
  assert(composed_progress(trace[n - 1], trace[n]));
  assert(is_extension_of(trace[n - 1], trace[n]));
  assert(is_task_log_prefix(trace[n - 1].task_logs[tid], trace[n].task_logs[tid]));

  if trace[n].task_logs[tid].len() > trace[n - 1].task_logs[tid].len() {
    // Poll happened in step [n-1, n]
    poll_in_current_step(trace, tid, n);
    trace_executor_log_extension(trace, (n - 1) as int);
  } else {
    // Recurse: poll in earlier step
    assert(trace[n].task_logs[tid].len() == trace[n - 1].task_logs[tid].len());
    progress_n_preserves_wf_chain(trace, (n - 1) as int);
    task_log_growth_implies_poll(trace, tid, n - 1);
    let poll_idx: int = choose |poll_idx: int|
      #![trigger trace[n - 1].executor_log[poll_idx]]
      trace[0].executor_log.len() as int <= poll_idx < trace[n - 1].executor_log.len() &&
      crate::executor::spec::log::is_poll_task_for_id_at(trace[n - 1].executor_log, poll_idx, tid);
    poll_preserved_by_progress(trace, tid, poll_idx, n);
  }
}

// Tick-end counting lemma (wake-routing Phase C):
// an n-step valid composed trace has AT LEAST n tick-ends in its new executor content
// (exactly n, since each step is one complete tick cycle — but >= n is all we need).
// This is the honest "n scheduler ticks elapsed" clock for the TaskWake arrival clause.
pub proof fn progress_n_has_n_tick_ends(
  trace: Seq<ComposedState>,
  n: nat,
)
  requires
    trace.len() == (n + 1) as int,
    crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, trace),
  ensures
    crate::executor::spec::log::count_tick_ends_between(
      trace[n as int].executor_log,
      trace[0].executor_log.len() as int,
      trace[n as int].executor_log.len() as int,
    ) >= n,
  decreases n
{
  use crate::executor::spec::log::*;

  if n == 0 {
  } else {
    let prev = (n - 1) as int;
    let sub = trace.subrange(0, n as int);
    assert(sub.len() == n as int);
    assert(sub.first() == trace[0]) by { assert(sub[0] == trace[0]); };
    assert(sub.last() == trace[prev]) by { assert(sub[prev] == trace[prev]); };
    assert(crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, sub)) by {
      assert forall |i: int| 0 <= i < sub.len() - 1 implies
        (composed_module_spec().progress)(#[trigger] sub[i], sub[i + 1])
      by {
        assert(sub[i] == trace[i]);
        assert(sub[i + 1] == trace[i + 1]);
      };
    };
    progress_n_has_n_tick_ends(sub, (n - 1) as nat);

    assert((composed_module_spec().progress)(trace[prev], trace[n as int]));
    assert(composed_progress(trace[prev], trace[n as int]));
    reveal(composed_progress);
    assert(crate::composed::spec::progress::executor_progress(
      trace[prev].executor_log, trace[n as int].executor_log
    ));
    assert(crate::executor::executor_progress(
      trace[prev].executor_log, trace[n as int].executor_log
    ));

    crate::executor::proof::bounded_drain_poll::single_progress_has_tick_end(
      trace[prev].executor_log, trace[n as int].executor_log
    );

    let base = trace[0].executor_log.len() as int;
    let mid = trace[prev].executor_log.len() as int;
    let end = trace[n as int].executor_log.len() as int;

    crate::executor::proof::bounded_drain_poll::count_tick_ends_prefix_equals(
      trace[prev].executor_log, trace[n as int].executor_log, base, mid
    );
    crate::executor::proof::bounded_drain_poll::count_tick_ends_additivity_range(
      trace[n as int].executor_log, base, mid, end
    );
  }
}

// Helper: task_polled_to_ready persists through log extension
pub proof fn task_polled_to_ready_persists(
  l: crate::executor::spec::log::Log,
  l_prime: crate::executor::spec::log::Log,
  tid: TaskId,
)
  requires
    task_polled_to_ready(l, tid),
    crate::executor::spec::log::is_prefix_of(l, l_prime),
  ensures
    task_polled_to_ready(l_prime, tid),
{
  let i: int = choose |i: int|
    #![trigger l[i]]
    0 <= i < l.len() &&
    crate::executor::spec::log::is_poll_ready_for_id_at(l, i, tid);
  assert(l_prime[i] == l[i]);
  assert(crate::executor::spec::log::is_poll_ready_for_id_at(l_prime, i, tid));
}

// Helper: composed_well_formed preserved by n progress steps
pub proof fn progress_n_preserves_wf(
  s: ComposedState,
  s_prime: ComposedState,
  n: nat,
)
  requires
    composed_well_formed(s),
    crate::framework::module_spec::progress_n(composed_module_spec().progress, s, s_prime, n),
  ensures
    composed_well_formed(s_prime),
  decreases n
{
  if n == 0 {
    assert(s == s_prime);
  } else {
    let trace: Seq<ComposedState> = choose |trace: Seq<ComposedState>|
      #![trigger trace.len()]
      trace.len() == n + 1 &&
      trace.first() == s &&
      trace.last() == s_prime &&
      crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, trace);

    let s_mid = trace[1];
    assert(composed_progress(s, s_mid));
    composed_progress_preserves_wf_lemma(s, s_mid);
    assert(composed_well_formed(s_mid));

    let subtrace = trace.subrange(1, trace.len() as int);
    assert(subtrace.len() == n);
    assert(subtrace.first() == s_mid);
    assert(subtrace.last() == s_prime);
    assert(crate::framework::module_spec::is_valid_trace(composed_module_spec().progress, subtrace)) by {
      assert forall |i: int| 0 <= i < subtrace.len() - 1 implies
        (composed_module_spec().progress)(#[trigger] subtrace[i], subtrace[i + 1])
      by {
        assert(subtrace[i] == trace[i + 1]);
        assert(subtrace[i + 1] == trace[i + 2]);
      };
    };
    assert(crate::framework::module_spec::progress_n(composed_module_spec().progress, s_mid, s_prime, (n - 1) as nat));
    progress_n_preserves_wf(s_mid, s_prime, (n - 1) as nat);
  }
}

// Helper: extract last pending poll from count >= 1 && !Ready
pub proof fn last_pending_poll_from_count(
  s: ComposedState,
  tid: TaskId,
)
  requires
    composed_well_formed(s),
    crate::executor::spec::log::has_poll_for_id(s.executor_log, tid),
    !task_polled_to_ready(s.executor_log, tid),
  ensures
    exists |pidx: int|
      is_task_pending_at(s, tid, pidx) &&
      s.task_logs.contains_key(tid) &&
      (forall |j: int| pidx < j < s.executor_log.len() ==>
        !crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, j, tid)),
{
  last_poll_idx_properties(s.executor_log, tid);
  let pidx = crate::executor::spec::log::last_poll_idx_for_id(s.executor_log, tid);

  assert(crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, pidx, tid));
  assert(!crate::executor::spec::log::is_poll_ready_for_id_at(s.executor_log, pidx, tid)) by {
    if crate::executor::spec::log::is_poll_ready_for_id_at(s.executor_log, pidx, tid) {
      assert(task_polled_to_ready(s.executor_log, tid));
    }
  };
  // PollResult exhaustiveness: poll_task_for_id && !Ready && !Invalid → Pending
  // Invalid is ruled out by VALID_TASK_POLLING:
  //   validity_fn gives tid_was_injected_before && (Invalid ⟺ tid_is_invalid)
  //   !task_polled_to_ready → !tid_returned_ready_before
  //   tid_was_injected_before ∧ !tid_returned_ready_before → !tid_is_invalid → !Invalid
  assert(crate::executor::spec::log::is_poll_pending_for_id_at(s.executor_log, pidx, tid)) by {
    let l = s.executor_log;
    let e = l[pidx];
    assert(crate::executor::spec::events::is_poll_task(e));
    let result = crate::executor::spec::events::get_poll_result(e);

    // Instantiate VALID_TASK_POLLING at pidx
    assert(crate::executor::invariants::executor_action_safety_inv(l));
    let vtp = crate::executor::invariants::valid_task_polling::valid_task_polling();
    assert(crate::framework::action_safety::action_safety_satisfied(vtp, l));
    assert((vtp.acceptance)(l, pidx));
    assert((vtp.validity)(l, pidx));
    assert(crate::executor::invariants::valid_task_polling::validity_fn(l, pidx));
    assert(crate::executor::invariants::valid_task_polling::tid_was_injected_before(l, pidx, tid));

    match result {
      crate::executor::spec::types::PollResult::Ready(u) => {
        assert(u == ());
        assert(result == crate::executor::spec::types::PollResult::Ready(()));
        assert(crate::executor::spec::log::is_poll_ready_for_id_at(l, pidx, tid));
        assert(false);
      },
      crate::executor::spec::types::PollResult::Pending => {
        assert(crate::executor::spec::log::is_poll_pending_for_id_at(l, pidx, tid));
      },
      crate::executor::spec::types::PollResult::Invalid => {
        // Invalid ⟺ tid_is_invalid = tid_returned_ready_before || !tid_was_injected_before
        // We have tid_was_injected_before (from validity_fn), so !tid_was_injected_before is false
        // We have !task_polled_to_ready, so !tid_returned_ready_before
        // Therefore !tid_is_invalid, contradicting Invalid
        assert(crate::executor::invariants::valid_task_polling::tid_is_invalid(l, pidx, tid));
        if crate::executor::invariants::valid_task_polling::tid_returned_ready_before(l, pidx, tid) {
          let j: int = choose |j: int|
            #![trigger l[j]]
            0 <= j < pidx &&
            crate::executor::spec::log::is_poll_task_at(l, j) &&
            crate::executor::spec::events::get_poll_task_id(l[j]) == tid &&
            crate::executor::spec::events::get_poll_result(l[j]) == crate::executor::spec::types::PollResult::Ready(());
          assert(crate::executor::spec::log::is_poll_ready_for_id_at(l, j, tid));
          assert(task_polled_to_ready(l, tid));
        }
        assert(false);
      },
    }
  };
  assert(is_task_pending_at(s, tid, pidx));

  assert(crate::composed::spec::alignment::polled_task_has_log_inv(s));
  assert(s.task_logs.contains_key(tid));
}

}
