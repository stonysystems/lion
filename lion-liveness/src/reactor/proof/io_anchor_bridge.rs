use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::log::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::events::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::invariants::reactor_action_safety_inv;
#[cfg(verus_keep_ghost)]
use crate::reactor::invariants::{inbound_register_io_result, inbound_deregister_io_result};
#[cfg(verus_keep_ghost)]
use crate::framework::action_safety::action_safety_satisfied;
#[cfg(verus_keep_ghost)]
use lion_reactor_spec::bridge::*;

verus! {

// F-K closure witness (mechanized, via the shared crate): under this crate's
// own reactor_action_safety_inv (whose R12/R13 records lion-reactor proves
// against its executable code), the two io registration anchors coincide per
// call cycle — every API-anchored registration (io_api_registered_at, the
// lion-reactor convention) has a same-rid syscall-anchored registration
// (io_syscall_registered_at, this crate's convention) inside the enclosing
// inbound call window, and dually for deregistration.
#[verifier::rlimit(50)]
pub proof fn reactor_inv_implies_io_anchor_bridge(l: Log)
  requires
    reactor_action_safety_inv(l),
  ensures
    io_anchor_bridge(l),
{
  let r12 = inbound_register_io_result::inbound_register_io_result();
  let r13 = inbound_deregister_io_result::inbound_deregister_io_result();
  assert(action_safety_satisfied(r12, l));
  assert(action_safety_satisfied(r13, l));
  assert forall |i: int| #![auto] io_api_registered_at(l, i) implies
    inbound_register_io_result::register_io_result_valid(l, i)
  by {
    assert((r12.acceptance)(l, i));
    assert((r12.validity)(l, i));
  }
  assert forall |i: int| #![auto] is_inbound_deregister_io_end_at(l, i) implies
    inbound_deregister_io_result::deregister_io_result_valid(l, i)
  by {
    assert((r13.acceptance)(l, i));
    assert((r13.validity)(l, i));
  }
  io_anchor_bridge_from_result_valid(l);
}

}
