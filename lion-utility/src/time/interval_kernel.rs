use vstd::prelude::*;

verus! {

// ── Verified deadline ledger for interval (§1c) ──
// An interval fires periodically. The kernel owns the next-fire deadline and
// proves it advances by exactly `period` on every tick and is therefore strictly
// monotonic — deadline == first + fires * period — so ticks neither drift nor go
// backwards. The glue performs one verified Sleep per tick in lockstep.

pub struct IntervalKernel {
  pub deadline: u64,
  pub period: u64,
  pub first: Ghost<nat>,
  pub fires: Ghost<nat>,
}

pub open spec fn iv_wf(k: IntervalKernel) -> bool {
  k.deadline as nat == k.first@ + k.fires@ * (k.period as nat)
}

impl IntervalKernel {
  pub fn new(start: u64, period: u64) -> (k: IntervalKernel)
    ensures
      iv_wf(k),
      k.deadline == start,
      k.period == period,
      k.fires@ == 0,
  {
    IntervalKernel { deadline: start, period, first: Ghost(start as nat), fires: Ghost(0) }
  }

  // Advance to the next tick: deadline += period (strictly increasing).
  pub fn tick_step(&mut self) -> (d: u64)
    requires
      iv_wf(*old(self)),
      old(self).period > 0,
      old(self).deadline as nat + old(self).period as nat <= u64::MAX as nat,
    ensures
      iv_wf(*self),
      self.deadline == old(self).deadline + old(self).period,
      self.deadline > old(self).deadline,
      self.period == old(self).period,
      self.fires@ == old(self).fires@ + 1,
      d == self.deadline,
  {
    let ghost f = self.fires@;
    self.deadline = self.deadline + self.period;
    self.fires = Ghost(self.fires@ + 1);
    proof {
      assert((f + 1) * (self.period as nat) == f * (self.period as nat) + (self.period as nat)) by (nonlinear_arith);
    }
    self.deadline
  }
}

}
