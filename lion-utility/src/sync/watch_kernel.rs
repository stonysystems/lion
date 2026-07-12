use vstd::prelude::*;

verus! {

// ── Verified data state machine for watch (§1b) ──
// watch is a single shared value plus a monotonically increasing version. The
// kernel owns the version; the proof guarantees it never regresses and advances
// by exactly one per publish (so a receiver comparing its `seen` version against
// the current one cannot miss or mis-order updates). The glue holds the real T
// and updates it in lockstep with send_step.

pub struct WatchKernel {
  pub version: u64,
  pub vsent: Ghost<nat>,
}

pub open spec fn w_wf(k: WatchKernel) -> bool {
  k.version as nat == 1 + k.vsent@
}

impl WatchKernel {
  pub fn new() -> (k: WatchKernel)
    ensures
      w_wf(k),
      k.version == 1,
      k.vsent@ == 0,
  {
    WatchKernel { version: 1, vsent: Ghost(0) }
  }

  // Publish a new value: the version strictly increases (monotonic, +1).
  pub fn send_step(&mut self) -> (v: u64)
    requires
      w_wf(*old(self)),
      old(self).version < u64::MAX,
    ensures
      w_wf(*self),
      self.version == old(self).version + 1,
      self.version > old(self).version,
      self.vsent@ == old(self).vsent@ + 1,
      v == self.version,
  {
    self.version = self.version + 1;
    self.vsent = Ghost(self.vsent@ + 1);
    self.version
  }

  // Has the holder of `seen` missed an update? (Pure query, no state change.)
  pub fn changed_step(&self, seen: u64) -> (b: bool)
    requires
      w_wf(*self),
    ensures
      b == (self.version != seen),
  {
    self.version != seen
  }

  // The current version a receiver adopts after observing (borrow_and_update).
  pub fn current(&self) -> (v: u64)
    requires
      w_wf(*self),
    ensures
      v == self.version,
  {
    self.version
  }
}

}
