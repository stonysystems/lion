use vstd::prelude::*;
use crate::utilities::spec::events::*;
use crate::utilities::spec::log::*;
use crate::framework::action_safety::*;

verus! {

// WakeupGuarantee: when Poll returns Pending, there must be an active wakeup source
pub open spec fn wakeup_guarantee_action(l: Log, i: int) -> bool {
  0 <= i < l.len() && is_poll_end_pending(l[i])
}

pub open spec fn wakeup_guarantee_validity(l: Log, i: int) -> bool {
  has_active_wakeup_source(l, i)
}

pub open spec fn wakeup_guarantee() -> ActionSafety<Log> {
  ActionSafety {
    acceptance: |l: Log, i: int| wakeup_guarantee_action(l, i),
    validity: |l: Log, i: int| wakeup_guarantee_validity(l, i),
  }
}

pub open spec fn utilities_inv(l: Log) -> bool {
  action_safety_satisfied(wakeup_guarantee(), l) &&
  action_safety_satisfied(super::resource_ownership::resource_ownership(), l)
}

}
