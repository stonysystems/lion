use vstd::prelude::*;
use crate::composed::spec::state::*;
use crate::composed::spec::types::*;
use crate::composed::spec::progress::*;
use crate::composed::spec::assumptions::*;
use crate::executor::spec::log as executor_log;
use crate::executor::spec::events::*;
use crate::framework::async_contract::*;

verus! {

pub open spec fn task_spawned_in(l: executor_log::Log, tid: TaskId) -> bool {
  exists |i: int|
    #![trigger l[i]]
    0 <= i < l.len() &&
    executor_log::is_pop_injection_at(l, i) &&
    get_pop_injection_task(l[i]).is_some() &&
    get_pop_injection_task(l[i]).unwrap().id == tid
}

// Despite living in the arrival trigger: this does NOT test queue membership —
// it says tid is delivered by the VERY NEXT tick (every one-step successor has
// popped tid). The theorem is thus stated from the moment tid reaches the head
// of the injection schedule. Vacuously true at progress-dead-end states.
pub open spec fn task_delivered_next_tick(s: ComposedState, tid: TaskId) -> bool {
  forall |s_prime: ComposedState|
    #![trigger composed_progress(s, s_prime)]
    composed_progress(s, s_prime) ==>
    task_spawned_in(s_prime.executor_log, tid)
}

// Depth-k generalization of the arrival trigger : tid is the
// k-th UNDELIVERED entry of the committed injection schedule (k = 0 is the entry
// the next Some-pop must deliver). Unlike task_delivered_next_tick this covers
// tasks at ARBITRARY schedule depth; delivery within a budget growing with the
// schedule length is DERIVED (tick_has_pop_injection gives one pop per tick,
// pops_deliver_schedule converts schedule-many pops into full delivery) — see
// composed::proof::depth_generalization.
pub open spec fn task_scheduled_at(s: ComposedState, tid: TaskId, k: nat) -> bool {
  let delivered = crate::executor::spec::injection_schedule::injected_tasks(s.executor_log).len();
  delivered + k < s.injection_schedule.len() &&
  s.injection_schedule[(delivered + k) as int].id == tid
}

pub open spec fn end_to_end_trigger(s: ComposedState, tid: TaskId) -> bool {
  task_spawned_in(s.executor_log, tid)
}

pub open spec fn end_to_end_response(s: ComposedState, tid: TaskId) -> bool {
  task_polled_to_ready(s.executor_log, tid)
}

pub open spec fn end_to_end_arrival(s: ComposedState, tid: TaskId) -> bool {
  task_delivered_next_tick(s, tid)
}

}
