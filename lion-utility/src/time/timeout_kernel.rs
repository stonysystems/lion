use vstd::prelude::*;

verus! {

// ── Verified decision for timeout (§1c compositional well-formedness) ──
// timeout races a future against the verified Sleep. The headline guarantee is
// that timeout returns Pending ONLY when both sub-futures are Pending — so every
// Pending it produces carries a wake source (the wrapped future's own waker, or
// the verified Sleep's timer). The glue observes the two readiness bits and lets
// this verified decision choose; it never decides to suspend on its own.

pub enum TimeoutAction {
  ReadyOk,       // the wrapped future completed
  ReadyElapsed,  // the deadline fired first
  Pending,       // neither is ready yet
}

pub fn poll_step(fut_ready: bool, sleep_ready: bool) -> (a: TimeoutAction)
  ensures
    (a is ReadyOk) == fut_ready,
    (a is ReadyElapsed) == (!fut_ready && sleep_ready),
    // The crucial one: Pending implies BOTH sub-futures are Pending.
    (a is Pending) == (!fut_ready && !sleep_ready),
{
  if fut_ready {
    TimeoutAction::ReadyOk
  } else if sleep_ready {
    TimeoutAction::ReadyElapsed
  } else {
    TimeoutAction::Pending
  }
}

}
