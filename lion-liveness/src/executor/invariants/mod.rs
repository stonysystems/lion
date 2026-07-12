pub mod park_drain_reactor_wake;
pub mod tick_polls_if_runnable;
pub mod tick_has_park;
pub mod tick_has_pop_injection;
pub mod tick_has_drain_deferred;
pub mod tick_has_drain_task_wake;
pub mod fifo_task_selection;
pub mod valid_task_polling;

use vstd::prelude::*;
use crate::executor::spec::log::Log;
use crate::framework::local_liveness::*;
use crate::framework::action_safety::*;

verus! {

pub open spec fn executor_local_liveness_inv(l: Log) -> bool {
  local_liveness_satisfied(park_drain_reactor_wake::park_drain_reactor_wake(), l) &&
  local_liveness_satisfied(tick_polls_if_runnable::tick_polls_if_runnable(), l)
}

pub open spec fn executor_action_safety_inv(l: Log) -> bool {
  action_safety_satisfied(fifo_task_selection::fifo_task_selection(), l) &&
  action_safety_satisfied(valid_task_polling::valid_task_polling(), l) &&
  action_safety_satisfied(tick_has_park::tick_has_park(), l) &&
  action_safety_satisfied(tick_has_pop_injection::tick_has_pop_injection(), l) &&
  action_safety_satisfied(tick_has_drain_deferred::tick_has_drain_deferred(), l) &&
  action_safety_satisfied(tick_has_drain_task_wake::tick_has_drain_task_wake(), l)
}

pub open spec fn executor_inv(l: Log) -> bool {
  executor_local_liveness_inv(l) &&
  executor_action_safety_inv(l)
}

}
