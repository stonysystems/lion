use vstd::prelude::*;

verus! {

// ── Verified data state machine for oneshot (§1b) ──
// The value-transfer protocol, decided in verified code (the WaiterKernel handles
// the receiver's wakeup separately). Ghost counters `sent`/`delivered` make the
// headline guarantees checkable: send-once and at-most-once delivery with no
// delivery without a matching send (delivered <= sent <= 1).

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum OState {
  Empty,   // no value yet
  Full,    // a value is present, not yet taken
  Taken,   // the value has been delivered to the receiver
  Closed,  // sender dropped before sending — no value will ever arrive
}

pub enum RecvDecision {
  Ready,   // a value is available; glue takes it
  Closed,  // no value will arrive; glue returns RecvError
  Park,    // nothing yet; glue parks the receiver (via the WaiterKernel)
}

pub struct OneshotKernel {
  pub st: OState,
  pub sent: Ghost<nat>,
  pub delivered: Ghost<nat>,
}

pub open spec fn ok_wf(k: OneshotKernel) -> bool {
  &&& k.sent@ <= 1
  &&& k.delivered@ <= k.sent@
  &&& (k.st is Empty ==> k.sent@ == 0 && k.delivered@ == 0)
  &&& (k.st is Full ==> k.sent@ == 1 && k.delivered@ == 0)
  &&& (k.st is Taken ==> k.sent@ == 1 && k.delivered@ == 1)
  &&& (k.st is Closed ==> k.sent@ == 0 && k.delivered@ == 0)
}

impl OneshotKernel {
  pub fn new() -> (k: OneshotKernel)
    ensures
      ok_wf(k),
      k.st is Empty,
      k.sent@ == 0,
      k.delivered@ == 0,
  {
    OneshotKernel { st: OState::Empty, sent: Ghost(0), delivered: Ghost(0) }
  }

  // Accept the value iff this is the first send into an Empty channel; otherwise
  // (already sent, or closed) reject and the glue hands the value back.
  pub fn send_step(&mut self) -> (ok: bool)
    requires
      ok_wf(*old(self)),
    ensures
      ok_wf(*self),
      ok == (old(self).st is Empty),
      ok ==> self.st is Full && self.sent@ == old(self).sent@ + 1,
      !ok ==> self.st == old(self).st && self.sent@ == old(self).sent@,
  {
    if matches!(self.st, OState::Empty) {
      self.st = OState::Full;
      self.sent = Ghost(self.sent@ + 1);
      true
    } else {
      false
    }
  }

  // One receiver poll: deliver the value (Full), report closed, or park.
  pub fn recv_step(&mut self) -> (d: RecvDecision)
    requires
      ok_wf(*old(self)),
    ensures
      ok_wf(*self),
      (d is Ready) == (old(self).st is Full),
      d is Ready ==> self.st is Taken && self.delivered@ == old(self).delivered@ + 1,
      d is Park ==> old(self).st is Empty,
      !(d is Ready) ==> self.st == old(self).st && self.delivered@ == old(self).delivered@,
  {
    if matches!(self.st, OState::Full) {
      self.st = OState::Taken;
      self.delivered = Ghost(self.delivered@ + 1);
      RecvDecision::Ready
    } else if matches!(self.st, OState::Empty) {
      RecvDecision::Park
    } else {
      // Taken (value already delivered) or Closed: nothing (more) to deliver.
      RecvDecision::Closed
    }
  }

  // Sender dropped: if no value was ever sent, the channel is permanently closed.
  // (If a value is already present it stays deliverable.)
  pub fn close_step(&mut self)
    requires
      ok_wf(*old(self)),
    ensures
      ok_wf(*self),
      self.sent@ == old(self).sent@,
      self.delivered@ == old(self).delivered@,
  {
    if matches!(self.st, OState::Empty) {
      self.st = OState::Closed;
    }
  }
}

// ── Headline guarantee ──
// Documentation theorem (intentionally uncalled): at-most-once delivery — the
// receiver can never observe more than one value (delivered <= sent <= 1).
pub proof fn lemma_at_most_once_delivery(k: OneshotKernel)
  requires ok_wf(k),
  ensures k.delivered@ <= 1,
{
}

}
