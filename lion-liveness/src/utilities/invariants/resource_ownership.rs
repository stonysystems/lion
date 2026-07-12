use vstd::prelude::*;
use crate::utilities::spec::events::*;
use crate::utilities::spec::log::*;
use crate::framework::action_safety::*;

verus! {

// ResourceOwnership: operations on a resource (Deregister, SetWaker) must target
// a resource that was previously registered by this task

pub open spec fn is_resource_operation(e: UtilityEvent) -> bool {
  is_deregister_timer(e) ||
  is_deregister_io(e) ||
  is_set_waker(e)
}

pub open spec fn io_owned_before(l: Log, rid: RID, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    0 <= j < i &&
    is_register_io(l[j]) &&
    get_resource_id(l[j]) == Some(rid)
}

// Check if resource was registered as IO and still active (not deregistered) before index i
pub open spec fn io_active_before(l: Log, rid: RID, i: int) -> bool {
  exists |j: int|
    #![trigger l[j]]
    0 <= j < i &&
    is_register_io(l[j]) &&
    get_resource_id(l[j]) == Some(rid) &&
    !(exists |k: int|
        #![trigger l[k]]
        j < k < i &&
        is_deregister_io(l[k]) &&
        get_resource_id(l[k]) == Some(rid))
}

// Check if the resource operation at index i targets an owned resource
pub open spec fn resource_operation_valid(l: Log, i: int) -> bool {
  let e = l[i];
  let rid_opt = get_resource_id(e);
  rid_opt.is_some() ==> {
    let rid = rid_opt.unwrap();
    if is_deregister_timer(e) {
      is_timer_active(l, rid, i)
    } else if is_deregister_io(e) {
      is_io_active(l, rid, i)
    } else if is_set_waker(e) {
      io_active_before(l, rid, i)
    } else {
      true
    }
  }
}

pub open spec fn resource_ownership_action(l: Log, i: int) -> bool {
  0 <= i < l.len() && is_resource_operation(l[i])
}

pub open spec fn resource_ownership_validity(l: Log, i: int) -> bool {
  resource_operation_valid(l, i)
}

pub open spec fn resource_ownership() -> ActionSafety<Log> {
  ActionSafety {
    acceptance: |l: Log, i: int| resource_ownership_action(l, i),
    validity: |l: Log, i: int| resource_ownership_validity(l, i),
  }
}

}
