use vstd::prelude::*;
use crate::composed::spec::state::*;
#[allow(unused_imports)]
use crate::composed::spec::types::*;
use crate::executor::spec::log as executor_log;
#[allow(unused_imports)]
use crate::executor::spec::events::*;
use crate::reactor::spec::log as reactor_log;
use crate::reactor::spec::events as reactor_events;
use crate::utilities::spec::log as task_log;
use crate::utilities::spec::events as utilities_events;

verus! {

pub open spec fn count_park_events_in(l: executor_log::Log, start: int, end: int) -> nat
  decreases (if end > start { end - start } else { 0 }) as nat
{
  if start >= end || start < 0 || end > l.len() {
    0
  } else if executor_log::is_park_at(l, start) {
    1 + count_park_events_in(l, start + 1, end)
  } else {
    count_park_events_in(l, start + 1, end)
  }
}

pub open spec fn count_park_cycles_in(l: reactor_log::Log, start: int, end: int) -> nat
  decreases (if end > start { end - start } else { 0 }) as nat
{
  if start >= end || start < 0 || end > l.len() {
    0
  } else if reactor_log::is_park_end_at(l, start) {
    1 + count_park_cycles_in(l, start + 1, end)
  } else {
    count_park_cycles_in(l, start + 1, end)
  }
}

pub open spec fn park_alignment(s: ComposedState, s_prime: ComposedState) -> bool {
  let exec_start = s.executor_log.len() as int;
  let exec_end = s_prime.executor_log.len() as int;
  let reactor_start = s.reactor_log.len() as int;
  let reactor_end = s_prime.reactor_log.len() as int;

  count_park_events_in(s_prime.executor_log, exec_start, exec_end) ==
  count_park_cycles_in(s_prime.reactor_log, reactor_start, reactor_end)
}

pub open spec fn poll_alignment(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId|
    s_prime.task_logs.contains_key(tid) ==> {
      let old_len = if s.task_logs.contains_key(tid) {
        s.task_logs[tid].len()
      } else {
        0
      };
      let new_len = s_prime.task_logs[tid].len();
      old_len < new_len ==>
        task_polled_during_progress(s_prime.executor_log, tid, s.executor_log.len() as int)
    }
}

pub open spec fn task_polled_during_progress(l: executor_log::Log, tid: TaskId, start: int) -> bool {
  exists |i: int|
    #![trigger l[i]]
    start <= i < l.len() &&
    executor_log::is_poll_task_for_id_at(l, i, tid)
}

// NOTE: the `0 <= i` bound is essential. Without it, when tid's task log is
// NEW this step (the !contains branch), negative i satisfied the antecedent
// and s_prime.task_logs[tid][i] read an arbitrary out-of-range value — making
// new_operation_alignment (and with it composed_progress) UNPROVABLE for any
// step that first-polls a task; surfaced during witness construction.
pub open spec fn is_new_task_operation(s: ComposedState, s_prime: ComposedState, tid: TaskId, i: int) -> bool {
  0 <= i &&
  (!s.task_logs.contains_key(tid) || i >= s.task_logs[tid].len()) &&
  s_prime.task_logs.contains_key(tid) &&
  i < s_prime.task_logs[tid].len()
}

pub open spec fn new_operation_alignment(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId, i: int|
    is_new_task_operation(s, s_prime, tid, i) &&
    is_reactor_operation(#[trigger] s_prime.task_logs[tid][i])
    ==>
    exists |j: int|
      s.reactor_log.len() as int <= j < s_prime.reactor_log.len() &&
      succ_reactor_event_matches_task_operation(s_prime.reactor_log[j], s_prime.task_logs[tid][i])
}

pub open spec fn new_operation_uniqueness(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid1: TaskId, tid2: TaskId, task_idx1: int, task_idx2: int, reactor_idx: int|
    is_new_task_operation(s, s_prime, tid1, task_idx1) &&
    is_new_task_operation(s, s_prime, tid2, task_idx2) &&
    is_reactor_operation(#[trigger] s_prime.task_logs[tid1][task_idx1]) &&
    is_reactor_operation(#[trigger] s_prime.task_logs[tid2][task_idx2]) &&
    s.reactor_log.len() as int <= reactor_idx < s_prime.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(#[trigger] s_prime.reactor_log[reactor_idx], s_prime.task_logs[tid1][task_idx1]) &&
    succ_reactor_event_matches_task_operation(s_prime.reactor_log[reactor_idx], s_prime.task_logs[tid2][task_idx2])
    ==> tid1 == tid2 && task_idx1 == task_idx2
}

pub open spec fn new_op_matches_only_new_reactor(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId, task_idx: int, reactor_idx: int|
    is_new_task_operation(s, s_prime, tid, task_idx) &&
    is_reactor_operation(#[trigger] s_prime.task_logs[tid][task_idx]) &&
    0 <= reactor_idx < s_prime.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(#[trigger] s_prime.reactor_log[reactor_idx], s_prime.task_logs[tid][task_idx])
    ==> reactor_idx >= s.reactor_log.len()
}

pub open spec fn is_reactor_operation(e: utilities_events::UtilityEvent) -> bool {
  utilities_events::is_register_timer(e) ||
  utilities_events::is_deregister_timer(e) ||
  utilities_events::is_register_io(e) ||
  utilities_events::is_deregister_io(e) ||
  utilities_events::is_succ_set_waker(e)
}

pub open spec fn is_task_initiated_reactor_event(e: reactor_events::ReactorEvent) -> bool {
  reactor_events::is_succ_register_timer(e) ||
  reactor_events::is_deregister_timer(e) ||
  reactor_events::is_succ_io_syscall_register(e) ||
  reactor_events::is_io_syscall_deregister(e) ||
  reactor_events::is_succ_set_waker(e)
}

pub closed spec fn composed_active_rid(s: ComposedState, tid: TaskId, rid: utilities_events::RID) -> bool {
  s.task_logs.contains_key(tid) &&
  has_registered_rid(s.task_logs[tid], rid) &&
  exists |task_reg_idx: int, reactor_reg_idx: int|
    0 <= task_reg_idx < s.task_logs[tid].len() &&
    (utilities_events::is_register_timer(s.task_logs[tid][task_reg_idx]) ||
     utilities_events::is_register_io(s.task_logs[tid][task_reg_idx])) &&
    utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]) == Some(rid) &&
    0 <= reactor_reg_idx < s.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_reg_idx], s.task_logs[tid][task_reg_idx]) &&
    (utilities_events::is_register_timer(s.task_logs[tid][task_reg_idx]) ==>
      forall |j: int| reactor_reg_idx < j < s.reactor_log.len() ==>
        !reactor_log::timer_retired_at(s.reactor_log, rid, j)) &&
    (utilities_events::is_register_io(s.task_logs[tid][task_reg_idx]) ==>
      forall |j: int| reactor_reg_idx < j < s.reactor_log.len() ==>
        !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
          reactor_events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid))
}

pub proof fn reveal_composed_active_rid(
  s: ComposedState, tid: TaskId, rid: utilities_events::RID,
  task_reg_idx: int, reactor_reg_idx: int,
)
  requires
    s.task_logs.contains_key(tid),
    has_registered_rid(s.task_logs[tid], rid),
    0 <= task_reg_idx < s.task_logs[tid].len(),
    utilities_events::is_register_timer(s.task_logs[tid][task_reg_idx]) ||
      utilities_events::is_register_io(s.task_logs[tid][task_reg_idx]),
    utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]) == Some(rid),
    0 <= reactor_reg_idx < s.reactor_log.len(),
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_reg_idx], s.task_logs[tid][task_reg_idx]),
    utilities_events::is_register_timer(s.task_logs[tid][task_reg_idx]) ==>
      forall |j: int| reactor_reg_idx < j < s.reactor_log.len() ==>
        !reactor_log::timer_retired_at(s.reactor_log, rid, j),
    utilities_events::is_register_io(s.task_logs[tid][task_reg_idx]) ==>
      forall |j: int| reactor_reg_idx < j < s.reactor_log.len() ==>
        !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
          reactor_events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid),
  ensures composed_active_rid(s, tid, rid),
{ reveal(composed_active_rid); }

pub proof fn composed_active_rid_witness(s: ComposedState, tid: TaskId, rid: utilities_events::RID)
  -> (result: (int, int))
  requires composed_active_rid(s, tid, rid),
  ensures ({
    let (task_reg_idx, reactor_reg_idx) = result;
    s.task_logs.contains_key(tid) &&
    has_registered_rid(s.task_logs[tid], rid) &&
    0 <= task_reg_idx < s.task_logs[tid].len() &&
    (utilities_events::is_register_timer(s.task_logs[tid][task_reg_idx]) ||
     utilities_events::is_register_io(s.task_logs[tid][task_reg_idx])) &&
    utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]) == Some(rid) &&
    0 <= reactor_reg_idx < s.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_reg_idx], s.task_logs[tid][task_reg_idx]) &&
    (utilities_events::is_register_timer(s.task_logs[tid][task_reg_idx]) ==>
      forall |j: int| reactor_reg_idx < j < s.reactor_log.len() ==>
        !reactor_log::timer_retired_at(s.reactor_log, rid, j)) &&
    (utilities_events::is_register_io(s.task_logs[tid][task_reg_idx]) ==>
      forall |j: int| reactor_reg_idx < j < s.reactor_log.len() ==>
        !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
          reactor_events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid))
  }),
{
  reveal(composed_active_rid);
  let task_reg_idx = choose |t: int|
    #![trigger s.task_logs[tid][t]]
    exists |r: int|
    #![trigger s.reactor_log[r]]
    0 <= t < s.task_logs[tid].len() &&
    (utilities_events::is_register_timer(s.task_logs[tid][t]) ||
     utilities_events::is_register_io(s.task_logs[tid][t])) &&
    utilities_events::get_resource_id(s.task_logs[tid][t]) == Some(rid) &&
    0 <= r < s.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(s.reactor_log[r], s.task_logs[tid][t]) &&
    (utilities_events::is_register_timer(s.task_logs[tid][t]) ==>
      forall |j: int| r < j < s.reactor_log.len() ==>
        !reactor_log::timer_retired_at(s.reactor_log, rid, j)) &&
    (utilities_events::is_register_io(s.task_logs[tid][t]) ==>
      forall |j: int| r < j < s.reactor_log.len() ==>
        !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
          reactor_events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid));
  let reactor_reg_idx = choose |r: int|
    0 <= r < s.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(s.reactor_log[r], s.task_logs[tid][task_reg_idx]) &&
    (utilities_events::is_register_timer(s.task_logs[tid][task_reg_idx]) ==>
      forall |j: int| r < j < s.reactor_log.len() ==>
        !reactor_log::timer_retired_at(s.reactor_log, rid, j)) &&
    (utilities_events::is_register_io(s.task_logs[tid][task_reg_idx]) ==>
      forall |j: int| r < j < s.reactor_log.len() ==>
        !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
          reactor_events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid));
  (task_reg_idx, reactor_reg_idx)
}

pub open spec fn has_registered_rid(l: task_log::Log, rid: utilities_events::RID) -> bool {
  exists |i: int|
    #![trigger l[i]]
    0 <= i < l.len() &&
    (utilities_events::is_register_timer(l[i]) || utilities_events::is_register_io(l[i])) &&
    utilities_events::get_resource_id(l[i]) == Some(rid)
}

// MODELING NOTE (P6, resolved): this excludes an execution where, within a
// SINGLE step, tid is polled Pending and then (same step) woken and re-polled to
// a non-pending result — because that step's task log would NOT end with Pending
// while still containing a new pending poll. This is INTENDED, not a bug: the
// executor model does at most ONE poll of a given task per tick (see
// tick_polls_if_runnable / fifo_task_selection; the P5a/P5b witnesses each poll
// once per tick), so "new pending poll in this step" ⟹ it is the step's last
// poll ⟹ the task log ends with Pending. A model that polled a task twice in one
// tick would need this weakened to "the LAST new poll's result matches".
pub open spec fn pending_poll_alignment(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId, i: int|
    #![trigger s_prime.executor_log[i], s_prime.task_logs[tid]]
    s.executor_log.len() as int <= i < s_prime.executor_log.len() &&
    executor_log::is_poll_pending_for_id_at(s_prime.executor_log, i, tid) &&
    s_prime.task_logs.contains_key(tid)
    ==>
    task_log_ends_with_pending(s_prime.task_logs[tid])
}

pub open spec fn task_log_ends_with_pending(l: task_log::Log) -> bool {
  l.len() > 0 &&
  utilities_events::is_poll_end_pending(l.last())
}

pub open spec fn new_poll_has_task_log(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId, i: int|
    #![trigger s_prime.executor_log[i], s_prime.task_logs[tid]]
    s.executor_log.len() as int <= i < s_prime.executor_log.len() &&
    executor_log::is_poll_task_for_id_at(s_prime.executor_log, i, tid)
    ==>
    s_prime.task_logs.contains_key(tid)
}

pub open spec fn reactor_outbound_has_task_operation(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |j: int|
    #![trigger s_prime.reactor_log[j]]
    s.reactor_log.len() as int <= j < s_prime.reactor_log.len() &&
    is_task_initiated_reactor_event(s_prime.reactor_log[j])
    ==>
    exists |tid: TaskId, task_idx: int|
      s_prime.task_logs.contains_key(tid) &&
      0 <= task_idx < s_prime.task_logs[tid].len() &&
      succ_reactor_event_matches_task_operation(s_prime.reactor_log[j], s_prime.task_logs[tid][task_idx])
}

// A new task-initiated reactor event's source task op is itself NEW (added this
// step). Justification: a reactor event is emitted by the op the task executes in
// the current poll, recorded in that tid's task_log this step — it cannot originate
// from a pre-existing op (that op emitted its own event in its own step). Tightens
// reactor_outbound_has_task_operation's source op from `0 <=` to `s.len() <=`;
// dual of new_operation_alignment (new op ⟹ new event). Needed for the io find_last
// link: new SetWaker ⟹ tid's task_log grew ⟹ tid polled.
pub open spec fn new_reactor_event_has_new_op(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |j: int|
    #![trigger s_prime.reactor_log[j]]
    s.reactor_log.len() as int <= j < s_prime.reactor_log.len() &&
    is_task_initiated_reactor_event(s_prime.reactor_log[j])
    ==>
    exists |tid: TaskId, task_idx: int|
      s_prime.task_logs.contains_key(tid) &&
      // Guard the s-side read: a task that is FRESH this step (spawned + first
      // poll registers a resource — the normal case) has no prior log, so its
      // lower bound is 0. Without this guard, s.task_logs[tid] on a missing key
      // is arbitrary, making the predicate's truth depend on unspecified data and
      // rejecting legitimate spawn+register steps (P6 fix).
      (if s.task_logs.contains_key(tid) { s.task_logs[tid].len() as int } else { 0int })
        <= task_idx < s_prime.task_logs[tid].len() &&
      succ_reactor_event_matches_task_operation(s_prime.reactor_log[j], s_prime.task_logs[tid][task_idx])
}

// ============================================================================
// deregister_matches_own_registration
//
// When a task deregisters a timer (its first DeregisterTimer(rid) in the task
// log), the corresponding reactor SuccDeregisterTimer retires the timer that
// the task itself registered. In Rust, this is guaranteed by linear handle
// ownership: a task can only deregister a timer whose handle it holds, and
// that handle corresponds to a specific reactor registration.
// ============================================================================
#[verifier::opaque]
pub open spec fn deregister_matches_own_registration(s: ComposedState) -> bool {
  forall |tid: TaskId, task_reg_idx: int, task_dereg_idx: int,
          reactor_reg_idx: int, reactor_dereg_idx: int|
    #![auto]
    s.task_logs.contains_key(tid) &&
    0 <= task_reg_idx < task_dereg_idx &&
    task_dereg_idx < s.task_logs[tid].len() &&
    utilities_events::is_register_timer(s.task_logs[tid][task_reg_idx]) &&
    utilities_events::is_deregister_timer(s.task_logs[tid][task_dereg_idx]) &&
    utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]) ==
      utilities_events::get_resource_id(s.task_logs[tid][task_dereg_idx]) &&
    !crate::utilities::spec::log::is_timer_deregistered_before(
      s.task_logs[tid],
      utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]).unwrap(),
      task_dereg_idx as int) &&
    0 <= reactor_reg_idx < s.reactor_log.len() &&
    0 <= reactor_dereg_idx < s.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid][task_reg_idx]) &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid][task_dereg_idx])
    ==>
    reactor_log::timer_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx)
}

pub proof fn deregister_matches_own_registration_use(
  s: ComposedState,
  tid: TaskId, task_reg_idx: int, task_dereg_idx: int,
  reactor_reg_idx: int, reactor_dereg_idx: int,
)
  requires
    deregister_matches_own_registration(s),
    s.task_logs.contains_key(tid),
    0 <= task_reg_idx < task_dereg_idx,
    task_dereg_idx < s.task_logs[tid].len(),
    utilities_events::is_register_timer(s.task_logs[tid][task_reg_idx]),
    utilities_events::is_deregister_timer(s.task_logs[tid][task_dereg_idx]),
    utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]) ==
      utilities_events::get_resource_id(s.task_logs[tid][task_dereg_idx]),
    !crate::utilities::spec::log::is_timer_deregistered_before(
      s.task_logs[tid],
      utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]).unwrap(),
      task_dereg_idx as int),
    0 <= reactor_reg_idx < s.reactor_log.len(),
    0 <= reactor_dereg_idx < s.reactor_log.len(),
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid][task_reg_idx]),
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid][task_dereg_idx]),
  ensures
    reactor_log::timer_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx),
{ reveal(deregister_matches_own_registration); }

// ============================================================================
// deregister_io_matches_own_registration  (io twin of the timer version above)
//
// When a task deregisters an io resource (its DeregisterIo(rid), with rid still
// active in the task log), the corresponding reactor SuccDeregisterIo retires the
// io registration that the task itself registered. Linear handle ownership at the
// task-log level — the io analog of deregister_matches_own_registration. This is
// the ASSUMED task-shape base from which succ_deregister_io_by_owner is DERIVED
// (see deregister_ownership::derive_succ_deregister_io_by_owner).
// ============================================================================
#[verifier::opaque]
pub open spec fn deregister_io_matches_own_registration(s: ComposedState) -> bool {
  forall |tid: TaskId, task_reg_idx: int, task_dereg_idx: int,
          reactor_reg_idx: int, reactor_dereg_idx: int|
    #![auto]
    s.task_logs.contains_key(tid) &&
    0 <= task_reg_idx < task_dereg_idx &&
    task_dereg_idx < s.task_logs[tid].len() &&
    utilities_events::is_register_io(s.task_logs[tid][task_reg_idx]) &&
    utilities_events::is_deregister_io(s.task_logs[tid][task_dereg_idx]) &&
    utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]) ==
      utilities_events::get_resource_id(s.task_logs[tid][task_dereg_idx]) &&
    !crate::utilities::spec::log::is_io_deregistered_before(
      s.task_logs[tid],
      utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]).unwrap(),
      task_dereg_idx as int) &&
    0 <= reactor_reg_idx < s.reactor_log.len() &&
    0 <= reactor_dereg_idx < s.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid][task_reg_idx]) &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid][task_dereg_idx])
    ==>
    reactor_log::io_syscall_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx)
}

pub proof fn deregister_io_matches_own_registration_use(
  s: ComposedState,
  tid: TaskId, task_reg_idx: int, task_dereg_idx: int,
  reactor_reg_idx: int, reactor_dereg_idx: int,
)
  requires
    deregister_io_matches_own_registration(s),
    s.task_logs.contains_key(tid),
    0 <= task_reg_idx < task_dereg_idx,
    task_dereg_idx < s.task_logs[tid].len(),
    utilities_events::is_register_io(s.task_logs[tid][task_reg_idx]),
    utilities_events::is_deregister_io(s.task_logs[tid][task_dereg_idx]),
    utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]) ==
      utilities_events::get_resource_id(s.task_logs[tid][task_dereg_idx]),
    !crate::utilities::spec::log::is_io_deregistered_before(
      s.task_logs[tid],
      utilities_events::get_resource_id(s.task_logs[tid][task_reg_idx]).unwrap(),
      task_dereg_idx as int),
    0 <= reactor_reg_idx < s.reactor_log.len(),
    0 <= reactor_dereg_idx < s.reactor_log.len(),
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid][task_reg_idx]),
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid][task_dereg_idx]),
  ensures
    reactor_log::io_syscall_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx),
{ reveal(deregister_io_matches_own_registration); }

// ============================================================================
// succ_deregister_by_owner
//
// DERIVED from: deregister_matches_own_registration, strengthened
// resource_ownership (is_timer_active), reactor_inv, operation_alignment_inv,
// and monotonic_task_reactor_alignment.
//
// When a successful DeregisterTimer retires an active timer, the deregistering
// task is the same task that registered the timer.
// ============================================================================
#[verifier::opaque]
pub open spec fn succ_deregister_by_owner(s: ComposedState) -> bool {
  forall |reactor_reg_idx: int, reactor_dereg_idx: int,
          tid_reg: TaskId, task_reg_idx: int,
          tid_dereg: TaskId, task_dereg_idx: int|
    #![auto]
    0 <= reactor_reg_idx < reactor_dereg_idx &&
    reactor_dereg_idx < s.reactor_log.len() &&
    reactor_events::is_succ_register_timer(s.reactor_log[reactor_reg_idx]) &&
    reactor_events::is_succ_deregister_timer(s.reactor_log[reactor_dereg_idx]) &&
    reactor_events::get_register_timer_rid(s.reactor_log[reactor_reg_idx]) ==
      reactor_events::get_deregister_timer_rid(s.reactor_log[reactor_dereg_idx]) &&
    reactor_log::timer_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx) &&
    s.task_logs.contains_key(tid_reg) &&
    0 <= task_reg_idx < s.task_logs[tid_reg].len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid_reg][task_reg_idx]) &&
    s.task_logs.contains_key(tid_dereg) &&
    0 <= task_dereg_idx < s.task_logs[tid_dereg].len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid_dereg][task_dereg_idx])
    ==>
    tid_reg == tid_dereg
}

// ============================================================================
// succ_deregister_io_by_owner  (io twin of succ_deregister_by_owner)
//
// When a reactor DeregisterIo(rid) retires the io registration that was active
// since a SuccRegisterIo(rid), the deregistering task is the same task that
// registered it. Same semantic justification as the timer twin: linear handle
// ownership — a task can only deregister an io resource whose handle it holds,
// and that handle corresponds to a specific reactor registration. ASSUMED at the
// reactor level (rather than derived from a task-shape twin as the timer path
// does) — it encodes the identical linear-ownership fact and is vacuous on every
// witness (no io deregisters there). Load-bearing for the reuse-tolerant io
// keystone (setwaker_op_owner_is_tid): rules out a cross-task-reuse trace where
// another task deregisters tid's io resource.
// ============================================================================
#[verifier::opaque]
pub open spec fn succ_deregister_io_by_owner(s: ComposedState) -> bool {
  forall |reactor_reg_idx: int, reactor_dereg_idx: int,
          tid_reg: TaskId, task_reg_idx: int,
          tid_dereg: TaskId, task_dereg_idx: int|
    #![auto]
    0 <= reactor_reg_idx < reactor_dereg_idx &&
    reactor_dereg_idx < s.reactor_log.len() &&
    reactor_events::is_succ_io_syscall_register(s.reactor_log[reactor_reg_idx]) &&
    reactor_log::io_syscall_deregistered_at(s.reactor_log, reactor_dereg_idx) &&
    reactor_events::get_io_syscall_register_rid(s.reactor_log[reactor_reg_idx]) ==
      reactor_events::get_io_syscall_deregister_rid(s.reactor_log[reactor_dereg_idx]) &&
    reactor_log::io_syscall_active_at(s.reactor_log, reactor_reg_idx, reactor_dereg_idx) &&
    s.task_logs.contains_key(tid_reg) &&
    0 <= task_reg_idx < s.task_logs[tid_reg].len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_reg_idx], s.task_logs[tid_reg][task_reg_idx]) &&
    s.task_logs.contains_key(tid_dereg) &&
    0 <= task_dereg_idx < s.task_logs[tid_dereg].len() &&
    succ_reactor_event_matches_task_operation(
      s.reactor_log[reactor_dereg_idx], s.task_logs[tid_dereg][task_dereg_idx])
    ==>
    tid_reg == tid_dereg
}

pub open spec fn action_mediation_state(s: ComposedState) -> bool {
  // (1) Domain: every task op has a matching reactor event
  operation_to_reactor_exists(s) &&
  // (2) Functional in task → reactor: same (tid, i) maps to same reactor idx
  // (one task op corresponds to one reactor event)
  //
  // Captured implicitly: combined with (3) and (5) below, every (tid, i)
  // determines a unique reactor index. Verus does not need this as a
  // separate axiom — derivable from succ_reactor_event_matches_task_operation.
  //
  // (3) Injective in reactor → task: distinct reactor events have distinct sources
  reactor_to_operation_unique(s) &&
  // (4) Surjective: every task-initiated reactor event has a source task op
  reactor_outbound_to_task_exists(s) &&
  // (5) Surjective restricted: every successful registration has a source.
  // (Redundant — subsumed by (4) reactor_outbound_to_task_exists, since every
  // succ_register is a task-initiated reactor event; kept explicit for clarity
  // and to avoid rippling its removal through the producer proofs. P7 hygiene.)
  reactor_registration_to_task_exists(s) &&
  // (6) Order-preserving per task: task_idx order ⟹ reactor_idx order
  monotonic_task_reactor_alignment(s) &&
  // (7) Same-task: register/deregister of a timer share tid (ownership)
  succ_deregister_by_owner(s) &&
  // (8) Same-task at the log shape level: a deregister in task log
  //     matches a registration earlier in the same task log
  deregister_matches_own_registration(s) &&
  // (8-io) io twin of (8): task-shape base for the io deregister-owner keystone
  deregister_io_matches_own_registration(s) &&
  // (9) io twin of (7): a reactor DeregisterIo retiring an active io
  //     registration shares tid with that registration (io ownership).
  //     DERIVED from (8-io) — see deregister_ownership::derive_succ_deregister_io_by_owner.
  succ_deregister_io_by_owner(s)
}

// A_step — Action Mediation, step form.
// New task ops added in this step ⟷ new reactor events added in this step.
pub open spec fn action_mediation_step(s: ComposedState, s_prime: ComposedState) -> bool {
  // (1) New task ops have a matching new reactor event
  new_operation_alignment(s, s_prime) &&
  // (2) Distinct new task ops map to distinct new reactor events (injective)
  new_operation_uniqueness(s, s_prime) &&
  // (3) A new task op's match is among the new reactor events (not old)
  new_op_matches_only_new_reactor(s, s_prime) &&
  // (4) Every new task-initiated reactor event has a source task op
  reactor_outbound_has_task_operation(s, s_prime) &&
  // (5) That source task op is itself new (added this step) — needed for io find_last
  new_reactor_event_has_new_op(s, s_prime)
}

// B_state — Observation Consistency, state form at s.
// executor poll observation projects faithfully to task_logs.
pub open spec fn observation_consistency_state(s: ComposedState) -> bool {
  // (1) Polled tasks have a task log
  polled_task_has_log_inv(s) &&
  // (2) Pending result in executor ⟹ task log ends with pending
  pending_poll_inv(s)
}

// B_step — Observation Consistency, step form.
// task_log grows ⟺ executor polled it; new polls extend log + agree with results.
pub open spec fn observation_consistency_step(s: ComposedState, s_prime: ComposedState) -> bool {
  // (1) task_log grows ⟹ executor polled the task in this step
  poll_alignment(s, s_prime) &&
  // (2) New poll with Pending result ⟹ task log ends with Pending
  pending_poll_alignment(s, s_prime) &&
  // (3) New poll ⟹ task log entry exists
  new_poll_has_task_log(s, s_prime) &&
  // (4) New poll strictly extends task log
  new_poll_changes_task_log(s, s_prime)
}

// C_state — Wakeup Routing, state form. RETIRED (Phase D): this category carried NO
// state-form content (was `≡ true`). All wake routing is now DERIVED (timer/io via the
// reactor-wake queue, deferred via the deferred queue) or bounded-assumed (taskwake via
// taskwake_arrival_within), so the placeholder conjunct is dropped from
// cross_module_alignment and the predicate deleted.

// C_step — Wakeup Routing, step form.
// Park sync between executor and reactor. The wake-routing "which task a drain
// delivers" content used to be stated here too (waker_queue_alignment /
// new_wake_new_drain_alignment / pending_defer_drain_alignment), but delivery
// is now derived (fire→drain→FIFO→poll, with drain membership modeled by the
// *_drain_step clauses of composed_progress) — the free-delivery predicate
// this comment once pointed to (wake_routing_consequence_holds) is RETIRED.
// Those alignment clauses were dead (only the never-called contract_chaining
// consumed them), so they were removed.
pub open spec fn wakeup_routing_step(s: ComposedState, s_prime: ComposedState) -> bool {
  // Park sync: count of executor Park events == count of reactor park cycles
  park_alignment(s, s_prime)
}

#[verifier::opaque]
pub open spec fn cross_module_alignment(s: ComposedState, s_prime: ComposedState) -> bool {
  // A. Action Mediation
  action_mediation_state(s_prime) &&
  action_mediation_step(s, s_prime) &&
  // B. Observation Consistency
  observation_consistency_state(s_prime) &&
  observation_consistency_step(s, s_prime) &&
  // C. Wakeup Routing (state form retired in Phase D — was content-free `true`)
  wakeup_routing_step(s, s_prime)
}

pub open spec fn pending_poll_inv(s: ComposedState) -> bool {
  forall |tid: TaskId|
    #![trigger s.task_logs[tid]]
    s.task_logs.contains_key(tid) &&
    executor_log::last_poll_is_pending(s.executor_log, tid)
    ==>
    task_log_ends_with_pending(s.task_logs[tid])
}

pub open spec fn polled_task_has_log_inv(s: ComposedState) -> bool {
  forall |tid: TaskId|
    executor_log::has_poll_for_id(s.executor_log, tid)
    ==>
    s.task_logs.contains_key(tid)
}

pub closed spec fn monotonic_task_reactor_alignment(s: ComposedState) -> bool {
  forall |tid: TaskId, a: int, b: int, ra: int, rb: int|
    s.task_logs.contains_key(tid) &&
    0 <= a < b && b < s.task_logs[tid].len() &&
    is_reactor_operation(s.task_logs[tid][a]) &&
    is_reactor_operation(s.task_logs[tid][b]) &&
    0 <= ra < s.reactor_log.len() &&
    0 <= rb < s.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(s.reactor_log[ra], s.task_logs[tid][a]) &&
    succ_reactor_event_matches_task_operation(s.reactor_log[rb], s.task_logs[tid][b])
    ==> ra < rb
}

// Producer lemma for the inhabitation witness: when a state has no task logs,
// monotonic_task_reactor_alignment holds vacuously. Lives in this module so it
// can see the closed body of monotonic_task_reactor_alignment.
pub proof fn monotonic_alignment_holds_empty(s: ComposedState)
  requires
    forall |tid: TaskId| !s.task_logs.contains_key(tid),
  ensures
    monotonic_task_reactor_alignment(s),
{
}

// Producer for task logs with at most one reactor op: the monotonicity forall
// needs TWO distinct reactor ops (a < b) in one task log, so "no two reactor
// ops" makes its antecedent vacuous. Used by the P5b witness (a single
// RegisterTimer per task log).
pub proof fn monotonic_alignment_holds_no_two_ops(s: ComposedState)
  requires
    forall |tid: TaskId, a: int, b: int|
      #![trigger s.task_logs[tid][a], s.task_logs[tid][b]]
      s.task_logs.contains_key(tid) && 0 <= a < b < s.task_logs[tid].len() &&
      is_reactor_operation(s.task_logs[tid][a]) ==>
      !is_reactor_operation(s.task_logs[tid][b]),
  ensures
    monotonic_task_reactor_alignment(s),
{
}

// General fold producer: any state satisfying the ordering condition directly
// (used by the io witness, whose task log has TWO ordered reactor ops). Lives in
// this module so it can see the closed body.
pub proof fn intro_monotonic_task_reactor_alignment(s: ComposedState)
  requires
    forall |tid: TaskId, a: int, b: int, ra: int, rb: int|
      #![trigger succ_reactor_event_matches_task_operation(s.reactor_log[ra], s.task_logs[tid][a]),
                 succ_reactor_event_matches_task_operation(s.reactor_log[rb], s.task_logs[tid][b])]
      s.task_logs.contains_key(tid) &&
      0 <= a < b && b < s.task_logs[tid].len() &&
      is_reactor_operation(s.task_logs[tid][a]) &&
      is_reactor_operation(s.task_logs[tid][b]) &&
      0 <= ra < s.reactor_log.len() &&
      0 <= rb < s.reactor_log.len() &&
      succ_reactor_event_matches_task_operation(s.reactor_log[ra], s.task_logs[tid][a]) &&
      succ_reactor_event_matches_task_operation(s.reactor_log[rb], s.task_logs[tid][b])
      ==> ra < rb,
  ensures
    monotonic_task_reactor_alignment(s),
{
}

pub proof fn monotonic_alignment_use(
  s: ComposedState, tid: TaskId, a: int, b: int, ra: int, rb: int,
)
  requires
    monotonic_task_reactor_alignment(s),
    s.task_logs.contains_key(tid),
    0 <= a < b, b < s.task_logs[tid].len(),
    is_reactor_operation(s.task_logs[tid][a]),
    is_reactor_operation(s.task_logs[tid][b]),
    0 <= ra < s.reactor_log.len(),
    0 <= rb < s.reactor_log.len(),
    succ_reactor_event_matches_task_operation(s.reactor_log[ra], s.task_logs[tid][a]),
    succ_reactor_event_matches_task_operation(s.reactor_log[rb], s.task_logs[tid][b]),
  ensures ra < rb,
{ reveal(monotonic_task_reactor_alignment); }

pub open spec fn reactor_registration_to_task_exists(s: ComposedState) -> bool {
  forall |j: int|
    #![trigger s.reactor_log[j]]
    0 <= j < s.reactor_log.len() &&
    (reactor_events::is_succ_register_timer(s.reactor_log[j]) ||
     reactor_events::is_succ_io_syscall_register(s.reactor_log[j]))
    ==>
    exists |tid: TaskId, task_idx: int|
      s.task_logs.contains_key(tid) &&
      0 <= task_idx < s.task_logs[tid].len() &&
      succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid][task_idx])
}

pub open spec fn reactor_outbound_to_task_exists(s: ComposedState) -> bool {
  forall |j: int|
    #![trigger s.reactor_log[j]]
    0 <= j < s.reactor_log.len() &&
    is_task_initiated_reactor_event(s.reactor_log[j])
    ==>
    exists |tid: TaskId, task_idx: int|
      s.task_logs.contains_key(tid) &&
      0 <= task_idx < s.task_logs[tid].len() &&
      succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid][task_idx])
}

pub open spec fn operation_alignment_inv(s: ComposedState) -> bool {
  operation_to_reactor_exists(s) &&
  reactor_to_operation_unique(s) &&
  reactor_registration_to_task_exists(s) &&
  reactor_outbound_to_task_exists(s)
}

pub open spec fn operation_to_reactor_exists(s: ComposedState) -> bool {
  forall |tid: TaskId, i: int|
    s.task_logs.contains_key(tid) &&
    0 <= i < s.task_logs[tid].len() &&
    is_reactor_operation(#[trigger] s.task_logs[tid][i])
    ==>
    exists |j: int|
      0 <= j < s.reactor_log.len() &&
      succ_reactor_event_matches_task_operation(s.reactor_log[j], s.task_logs[tid][i])
}

pub open spec fn reactor_to_operation_unique(s: ComposedState) -> bool {
  forall |tid1: TaskId, tid2: TaskId, task_idx1: int, task_idx2: int, reactor_idx: int|
    #![trigger s.task_logs[tid1][task_idx1], s.task_logs[tid2][task_idx2], s.reactor_log[reactor_idx]]
    s.task_logs.contains_key(tid1) &&
    s.task_logs.contains_key(tid2) &&
    0 <= task_idx1 < s.task_logs[tid1].len() &&
    0 <= task_idx2 < s.task_logs[tid2].len() &&
    is_reactor_operation(s.task_logs[tid1][task_idx1]) &&
    is_reactor_operation(s.task_logs[tid2][task_idx2]) &&
    0 <= reactor_idx < s.reactor_log.len() &&
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx], s.task_logs[tid1][task_idx1]) &&
    succ_reactor_event_matches_task_operation(s.reactor_log[reactor_idx], s.task_logs[tid2][task_idx2])
    ==> tid1 == tid2 && task_idx1 == task_idx2
}

pub open spec fn succ_reactor_event_matches_task_operation(
  re: reactor_events::ReactorEvent,
  pe: utilities_events::UtilityEvent
) -> bool {
  match pe {
    utilities_events::UtilityEvent::Outbound(
      utilities_events::OutboundCall::RegisterTimer { resource_id, deadline }
    ) => {
      reactor_events::is_succ_register_timer(re) &&
      reactor_events::get_register_timer_rid(re) == resource_id
    },
    utilities_events::UtilityEvent::Outbound(
      utilities_events::OutboundCall::DeregisterTimer { resource_id, .. }
    ) => {
      reactor_events::is_deregister_timer(re) &&
      reactor_events::get_deregister_timer_rid(re) == resource_id
    },
    utilities_events::UtilityEvent::Outbound(
      utilities_events::OutboundCall::RegisterIo { resource_id, .. }
    ) => {
      reactor_events::is_succ_io_syscall_register(re) &&
      reactor_events::get_io_syscall_register_rid(re) == resource_id
    },
    utilities_events::UtilityEvent::Outbound(
      utilities_events::OutboundCall::DeregisterIo { resource_id }
    ) => {
      reactor_events::is_io_syscall_deregister(re) &&
      reactor_events::get_io_syscall_deregister_rid(re) == resource_id
    },
    utilities_events::UtilityEvent::Outbound(
      utilities_events::OutboundCall::SetWaker { resource_id, result, .. }
    ) => {
      result == Some(()) &&
      reactor_events::is_succ_set_waker(re) &&
      reactor_events::get_set_waker_rid(re) == resource_id
    },
    _ => false,
  }
}

pub open spec fn new_poll_changes_task_log(s: ComposedState, s_prime: ComposedState) -> bool {
  forall |tid: TaskId, i: int|
    #![trigger s_prime.executor_log[i], s_prime.task_logs[tid]]
    s.executor_log.len() as int <= i < s_prime.executor_log.len() &&
    executor_log::is_poll_task_for_id_at(s_prime.executor_log, i, tid) &&
    s.task_logs.contains_key(tid)
    ==>
    s.task_logs[tid].len() < s_prime.task_logs[tid].len()
}

}
