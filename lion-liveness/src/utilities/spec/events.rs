use vstd::prelude::*;

verus! {

pub type RID = nat;
pub type Timestamp = nat;
// Utility-instance id: identifies one cross-task utility (channel, semaphore, …)
// that a task owns/awaits on. Used by the per-utility pass-waker contract.
pub type UID = nat;

#[derive(PartialEq, Eq)]
pub enum Interest {
  Readable,
  Writable,
  ReadableWritable,
}

#[derive(PartialEq, Eq)]
pub enum PollResult {
  Ready,
  Pending,
}

// Inbound: external calls into Utility (has Begin/End phases)
// Following Reactor's Inbound design: result=None means Begin, Some means End
// Note: no TID needed since Utilities log is per-TID (Map<TID, Log>)
#[derive(PartialEq, Eq)]
pub enum InboundCall {
  Poll { result: Option<PollResult> },
}

// Outbound: operations initiated by Utility (no phases, atomic)
// Note: no TID needed, TID info maintained via Map<TID, Log> at composition layer
#[derive(PartialEq, Eq)]
#[allow(inconsistent_fields)]
pub enum OutboundCall {
  // To Reactor: Timer
  RegisterTimer { resource_id: RID, deadline: Timestamp },
  DeregisterTimer { resource_id: RID, result: bool },

  // To Reactor: IO
  RegisterIo { resource_id: RID, interest: Interest },
  DeregisterIo { resource_id: RID },

  // To Reactor: Waker
  SetWaker { resource_id: RID, interest: Interest, result: Option<()> },

  // To Executor Queues
  Defer,
  // Cross-task wakeup: register this task's waker on utility `uid` (acceptance
  // of the pass-waker contract).
  PassWaker { uid: UID },
  // The waker registered on utility `uid` was invoked (fulfillment of the
  // pass-waker contract); the owning task is enqueued to the task-wake queue.
  Woken { uid: UID },
}

#[derive(PartialEq, Eq)]
pub enum UtilityEvent {
  Inbound(InboundCall),
  Outbound(OutboundCall),
}

// === Inbound predicates ===

pub open spec fn is_poll_begin(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Inbound(InboundCall::Poll { result: None }))
}

pub open spec fn is_poll_end(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Inbound(InboundCall::Poll { result: Some(_) }))
}

pub open spec fn is_poll_end_pending(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Inbound(InboundCall::Poll { result: Some(PollResult::Pending) }))
}

pub open spec fn is_register_timer(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Outbound(OutboundCall::RegisterTimer { .. }))
}

pub open spec fn is_deregister_timer(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Outbound(OutboundCall::DeregisterTimer { .. }))
}

pub open spec fn is_succ_deregister_timer(e: UtilityEvent) -> bool {
  match e {
    UtilityEvent::Outbound(OutboundCall::DeregisterTimer { result: true, .. }) => true,
    _ => false,
  }
}

pub proof fn succ_deregister_timer_is_deregister_timer(e: UtilityEvent)
  requires is_succ_deregister_timer(e),
  ensures is_deregister_timer(e),
{}

pub open spec fn is_register_io(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Outbound(OutboundCall::RegisterIo { .. }))
}

pub open spec fn is_deregister_io(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Outbound(OutboundCall::DeregisterIo { .. }))
}

pub open spec fn is_set_waker(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Outbound(OutboundCall::SetWaker { .. }))
}

pub open spec fn is_succ_set_waker(e: UtilityEvent) -> bool {
  match e {
    UtilityEvent::Outbound(OutboundCall::SetWaker { result: Some(()), .. }) => true,
    _ => false,
  }
}

pub open spec fn is_defer(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Outbound(OutboundCall::Defer))
}

pub open spec fn is_pass_waker(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Outbound(OutboundCall::PassWaker { .. }))
}

pub open spec fn is_woken(e: UtilityEvent) -> bool {
  matches!(e, UtilityEvent::Outbound(OutboundCall::Woken { .. }))
}

pub open spec fn get_pass_waker_uid(e: UtilityEvent) -> UID {
  match e {
    UtilityEvent::Outbound(OutboundCall::PassWaker { uid }) => uid,
    _ => arbitrary(),
  }
}

pub open spec fn get_woken_uid(e: UtilityEvent) -> UID {
  match e {
    UtilityEvent::Outbound(OutboundCall::Woken { uid }) => uid,
    _ => arbitrary(),
  }
}

// === Common predicates ===

pub open spec fn get_resource_id(e: UtilityEvent) -> Option<RID> {
  match e {
    UtilityEvent::Outbound(OutboundCall::RegisterTimer { resource_id, .. }) => Some(resource_id),
    UtilityEvent::Outbound(OutboundCall::DeregisterTimer { resource_id, .. }) => Some(resource_id),
    UtilityEvent::Outbound(OutboundCall::RegisterIo { resource_id, .. }) => Some(resource_id),
    UtilityEvent::Outbound(OutboundCall::DeregisterIo { resource_id }) => Some(resource_id),
    UtilityEvent::Outbound(OutboundCall::SetWaker { resource_id, .. }) => Some(resource_id),
    _ => None,
  }
}

}
