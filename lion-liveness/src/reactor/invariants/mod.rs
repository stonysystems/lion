pub mod timer_deadline_future;
pub mod park_has_timestamp;
pub mod park_poll_once;
pub mod io_ready_in_park;
pub mod timer_waker_validity;
pub mod io_waker_validity;
pub mod timer_reg_uniqueness;
pub mod io_reg_uniqueness;
pub mod timer_io_disjoint;
pub mod register_io_in_cycle;
pub mod deregister_io_in_cycle;
pub mod inbound_register_io_result;
pub mod inbound_deregister_io_result;
pub mod wake_on_expired;
pub mod wake_on_io_ready;
pub mod wake_has_registration;
pub mod set_waker_active_io;

use vstd::prelude::*;
use crate::reactor::spec::log::Log;
use crate::framework::action_safety::*;
use crate::framework::local_liveness::*;

verus! {

pub open spec fn reactor_action_safety_inv(l: Log) -> bool {
  action_safety_satisfied(timer_deadline_future::timer_deadline_future(), l) &&
  action_safety_satisfied(park_has_timestamp::park_has_timestamp(), l) &&
  action_safety_satisfied(park_poll_once::park_poll_once(), l) &&
  action_safety_satisfied(io_ready_in_park::io_ready_in_park(), l) &&
  action_safety_satisfied(timer_waker_validity::timer_waker_validity(), l) &&
  action_safety_satisfied(io_waker_validity::io_waker_validity(), l) &&
  action_safety_satisfied(timer_reg_uniqueness::timer_reg_uniqueness(), l) &&
  action_safety_satisfied(io_reg_uniqueness::io_reg_uniqueness(), l) &&
  action_safety_satisfied(timer_io_disjoint::timer_io_disjoint_at_timer(), l) &&
  action_safety_satisfied(timer_io_disjoint::timer_io_disjoint_at_io(), l) &&
  action_safety_satisfied(register_io_in_cycle::register_io_in_cycle(), l) &&
  action_safety_satisfied(deregister_io_in_cycle::deregister_io_in_cycle(), l) &&
  action_safety_satisfied(inbound_register_io_result::inbound_register_io_result(), l) &&
  action_safety_satisfied(inbound_deregister_io_result::inbound_deregister_io_result(), l) &&
  action_safety_satisfied(wake_has_registration::wake_has_registration(), l) &&
  action_safety_satisfied(set_waker_active_io::set_waker_active_io(), l)
}

pub open spec fn reactor_local_liveness_inv(l: Log) -> bool {
  local_liveness_satisfied(wake_on_expired::wake_on_expired(), l) &&
  local_liveness_satisfied(wake_on_io_ready::wake_on_io_ready_readable(), l) &&
  local_liveness_satisfied(wake_on_io_ready::wake_on_io_ready_writable(), l)
}

pub open spec fn reactor_inv(l: Log) -> bool {
  reactor_action_safety_inv(l) &&
  reactor_local_liveness_inv(l)
}

}
