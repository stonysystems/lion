use crate::reactor::Reactor;
use crate::spec::log::*;
use crate::types::{
  Duration, Instant, Interest, IoEvent, IoMode, IoResult,
  IoError, ResourceId, Source, Waker,
};
use vstd::prelude::*;

// The rid<->token codec, VERIFIED as an exact roundtrip (for any rid that
// fits a usize, i.e. always on the 64-bit targets lion supports). Both the
// registration and the poll-decode paths below go through this pair, so a
// token seen by the OS decodes to exactly the rid that was registered; the
// residual poll_events trust is mio itself (tokens returned faithfully,
// readable/writable flags matching real readiness).
verus! {

pub fn encode_token_raw(rid: u64) -> (result: usize)
  requires rid <= usize::MAX as u64,
  ensures result as u64 == rid,
{
  rid as usize
}

pub fn decode_token_raw(raw: usize) -> (result: u64)
  ensures result == raw as u64,
{
  raw as u64
}

pub proof fn token_roundtrip(rid: u64)
  requires rid <= usize::MAX as u64,
  ensures (rid as usize) as u64 == rid,
{
}

}

pub(crate) fn interest_to_mio(interest: Interest) -> mio::Interest {
  match (interest.readable, interest.writable) {
    (true, true) => mio::Interest::READABLE.add(mio::Interest::WRITABLE),
    (true, false) => mio::Interest::READABLE,
    (false, true) => mio::Interest::WRITABLE,
    (false, false) => mio::Interest::READABLE,
  }
}

fn collect_io_events(mio_events: &mio::event::Events) -> Vec<IoEvent> {
  let mut events = Vec::with_capacity(64);
  for e in mio_events.iter() {
    let resource_id = ResourceId(decode_token_raw(e.token().0));
    let error = e.is_error();
    let read_closed = e.is_read_closed();
    let write_closed = e.is_write_closed();
    if e.is_readable() {
      events.push(IoEvent {
        resource_id,
        mode: IoMode::Readable,
        error,
        read_closed,
        write_closed,
      });
    }
    if e.is_writable() {
      events.push(IoEvent {
        resource_id,
        mode: IoMode::Writable,
        error,
        read_closed,
        write_closed,
      });
    }
  }
  events
}

// Ghost-log action macro: the ONE definition of the "ghost-log shape" trusted
// on the reactor side. Every expansion is an external_body method whose whole
// contract is (a) append exactly the given event to the log and (b) leave every
// other Reactor field (next_resource_id / wheel / resources / free_rids)
// unchanged. Auditing the frame clauses of all begin/end log actions reduces
// to auditing this macro body once.
//
// macro_rules! cannot live inside verus! (proc macro), so each expansion emits
// its own `verus! { impl Reactor { .. } }` block; the event is captured as raw
// token trees because verus spec syntax (`@`, deep_view) is not plain rust expr.
macro_rules! reactor_log_action {
  ($(#[$attr:meta])* $vis:vis fn $name:ident(&mut self $(, $arg:ident: $ty:ty)* $(,)?) => $($event:tt)*) => {
    verus! {
      impl Reactor {
        $(#[$attr])*
        #[verifier::external_body]
        $vis fn $name(&mut self $(, $arg: $ty)*)
          ensures
            self.log@ == old(self).log@.push($($event)*),
            self.next_resource_id == old(self).next_resource_id,
            self.wheel == old(self).wheel,
            self.resources == old(self).resources,
            self.free_rids == old(self).free_rids,
        { }
      }
    }
  };
}

reactor_log_action! {
  pub fn park_begin_action(&mut self, timeout: Option<Duration>) =>
    ReactorEvent::Inbound(InboundCall::Park {
      timeout: timeout.deep_view(), result: None,
    })
}

reactor_log_action! {
  pub fn park_end_action(&mut self, timeout: Option<Duration>, result: &IoResult<()>) =>
    ReactorEvent::Inbound(InboundCall::Park {
      timeout: timeout.deep_view(), result: Some(result@),
    })
}

reactor_log_action! {
  pub fn register_io_begin_action(&mut self, source: &Source, interest: Interest) =>
    ReactorEvent::Inbound(InboundCall::RegisterIoResource {
      source: source@, interest: interest@, result: None,
    })
}

reactor_log_action! {
  pub fn register_io_end_action(&mut self, source: &Source, interest: Interest, result: &IoResult<ResourceId>) =>
    ReactorEvent::Inbound(InboundCall::RegisterIoResource {
      source: source@, interest: interest@, result: Some(result@),
    })
}

reactor_log_action! {
  pub fn deregister_io_begin_action(&mut self, resource_id: ResourceId) =>
    ReactorEvent::Inbound(InboundCall::DeregisterIoResource {
      resource_id: resource_id@, result: None,
    })
}

reactor_log_action! {
  pub fn deregister_io_end_action(&mut self, resource_id: ResourceId, result: &IoResult<()>) =>
    ReactorEvent::Inbound(InboundCall::DeregisterIoResource {
      resource_id: resource_id@, result: Some(result@),
    })
}

reactor_log_action! {
  pub fn set_waker_begin_action(&mut self, resource_id: ResourceId, interest: Interest, waker: &Waker) =>
    ReactorEvent::Inbound(InboundCall::SetWaker {
      resource_id: resource_id@, interest: interest@, waker: waker@, result: None,
    })
}

reactor_log_action! {
  pub fn set_waker_end_action(&mut self, resource_id: ResourceId, interest: Interest, waker: &Waker) =>
    ReactorEvent::Inbound(InboundCall::SetWaker {
      resource_id: resource_id@, interest: interest@, waker: waker@,
      result: Some(crate::spec::types::IoResultView::Ok(())),
    })
}

reactor_log_action! {
  #[inline]
  pub fn register_timer_begin_action(&mut self, deadline: Instant, waker: &Waker) =>
    ReactorEvent::Inbound(InboundCall::RegisterTimer {
      deadline: deadline@, waker: waker@, result: None,
    })
}

reactor_log_action! {
  #[inline]
  pub fn register_timer_end_action(&mut self, deadline: Instant, waker: &Waker, result: &IoResult<ResourceId>) =>
    ReactorEvent::Inbound(InboundCall::RegisterTimer {
      deadline: deadline@, waker: waker@, result: Some(result@),
    })
}

reactor_log_action! {
  #[inline]
  pub fn deregister_timer_begin_action(&mut self, resource_id: ResourceId) =>
    ReactorEvent::Inbound(InboundCall::DeregisterTimer {
      resource_id: resource_id@,
      result: true,
    })
}

// Ghost-log shape trust only: appends the GetCurrentTime event recording `t`,
// touches nothing else. No semantic claim about the timestamp value.
reactor_log_action! {
  fn log_get_current_time_action(&mut self, t: Instant) =>
    ReactorEvent::Outbound(OutboundCall::GetCurrentTime {
      timestamp: t@,
    })
}

verus! {

impl Reactor {
  #[verifier::external_body]
  pub fn register_io_source_action(
    &mut self,
    source: &mut Source,
    resource_id: ResourceId,
    interest: Interest,
  ) -> (result: IoResult<()>)
    ensures
      source@ == old(source)@,
      self.log@ == old(self).log@.push(ReactorEvent::Outbound(OutboundCall::RegisterIoResource {
        source: source@, resource_id: resource_id@, interest: interest@, result: result@,
      })),
      self.next_resource_id == old(self).next_resource_id,
      self.wheel == old(self).wheel,
      self.resources == old(self).resources,
      self.free_rids == old(self).free_rids,
  {
    let registry = self.poll.inner.registry();
    let mio_token = mio::Token(encode_token_raw(resource_id.0));
    let mio_interest = interest_to_mio(interest);
    match registry.register(source.inner, mio_token, mio_interest) {
      Ok(()) => IoResult::Ok(()),
      Err(e) => IoResult::Err(IoError { inner: e }),
    }
  }

  #[verifier::external_body]
  pub fn deregister_io_source_action(
    &mut self,
    source: &mut Source,
    resource_id: ResourceId,
  ) -> (result: IoResult<()>)
    ensures
      source@ == old(source)@,
      self.log@ == old(self).log@.push(ReactorEvent::Outbound(OutboundCall::DeregisterIoResource {
        source: source@, resource_id: resource_id@, result: result@,
      })),
      self.next_resource_id == old(self).next_resource_id,
      self.wheel == old(self).wheel,
      self.resources == old(self).resources,
      self.free_rids == old(self).free_rids,
  {
    let registry = self.poll.inner.registry();
    match registry.deregister(source.inner) {
      Ok(()) => IoResult::Ok(()),
      Err(e) => IoResult::Err(IoError { inner: e }),
    }
  }

  #[verifier::external_body]
  pub fn poll_events_action(&mut self, timeout: Option<Duration>)
    -> (result: IoResult<Vec<IoEvent>>)
    ensures
      self.log@ == old(self).log@.push(ReactorEvent::Outbound(OutboundCall::PollEvents {
        timeout: timeout.deep_view(),
        result: match result@ {
          crate::spec::types::IoResultView::Ok(_) => crate::spec::types::IoResultView::Ok(
            match result {
              IoResult::Ok(ref evs) => evs@.len() as nat,
              IoResult::Err(_) => 0nat,
            }
          ),
          crate::spec::types::IoResultView::Err(e) => crate::spec::types::IoResultView::Err(e),
        },
      })),
      self.next_resource_id == old(self).next_resource_id,
      self.wheel == old(self).wheel,
      self.resources == old(self).resources,
      self.free_rids == old(self).free_rids,
  {
    let std_timeout = timeout.map(|d| std::time::Duration::from_millis(d.as_millis()));
    match self.poll.inner.poll(&mut self.events.inner, std_timeout) {
      Ok(()) => {
        let lion_events: Vec<IoEvent> = collect_io_events(&self.events.inner);
        IoResult::Ok(lion_events)
      }
      Err(e) => IoResult::Err(IoError { inner: e }),
    }
  }

  #[verifier::external_body]
  pub fn io_event_ready_action(&mut self, event: &IoEvent)
    ensures
      self.log@ == old(self).log@.push(ReactorEvent::Outbound(OutboundCall::IoEventReady {
        event: event@,
      })),
      self.next_resource_id == old(self).next_resource_id,
      self.wheel == old(self).wheel,
      self.resources == old(self).resources,
      self.free_rids == old(self).free_rids,
  { }

  // Publishes the park-cycle clock observation to the thread-local cache in
  // the trusted handle layer (see handle.rs CACHED_NOW). No claims: the cache
  // lives entirely outside the verified state; readers treat it as an
  // optimization hint with a real-clock fallback.
  #[inline]
  #[verifier::external_body]
  fn publish_cached_now(now: Instant) {
    crate::handle::store_cached_now(now.inner);
  }

  // VERIFIED monotonicity by construction: the raw clock reading is clamped to
  // wheel.elapsed, so `result.inner >= wheel.elapsed` is proven, not trusted.
  // On a well-behaved platform clock (std::time::Instant is monotonic) the
  // clamp branch is dead and behavior is bit-identical to returning now();
  // if the clock ever regressed, time holds at `elapsed` (conservative for
  // timer liveness: never fires a timer early, never moves time backward).
  pub fn get_current_time_action(&mut self) -> (result: Instant)
    ensures
      self.log@ == old(self).log@.push(ReactorEvent::Outbound(OutboundCall::GetCurrentTime {
        timestamp: result@,
      })),
      self.next_resource_id == old(self).next_resource_id,
      self.wheel == old(self).wheel,
      self.resources == old(self).resources,
      self.free_rids == old(self).free_rids,
      result.inner >= old(self).wheel.elapsed,
  {
    let raw = Instant::now();
    let now = if raw.inner >= self.wheel.elapsed {
      raw
    } else {
      Instant { inner: self.wheel.elapsed }
    };
    Self::publish_cached_now(now);
    self.log_get_current_time_action(now);
    now
  }

  #[inline]
  #[verifier::external_body]
  pub fn wake_task_action(&mut self, waker: &Waker, source_rid: ResourceId)
    ensures
      self.log@ == old(self).log@.push(ReactorEvent::Outbound(OutboundCall::WakeTask {
        waker: waker@, source_rid: source_rid@,
      })),
      self.next_resource_id == old(self).next_resource_id,
      self.wheel == old(self).wheel,
      self.resources == old(self).resources,
      self.free_rids == old(self).free_rids,
  {
    waker.inner.wake_by_ref();
  }
}

} // end verus!
