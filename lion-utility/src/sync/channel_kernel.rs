use vstd::prelude::*;

verus! {

// ── Verified data state machine for a bounded mpsc channel (§1b) ──
// The buffer is modelled abstractly by sequence numbers: `sent` = how many values
// have entered the buffer (the next seq to assign), `recvd` = how many have been
// delivered, and the ghost `buf` is the seqs currently buffered, in order. The
// invariant pins `buf` to the contiguous block [recvd, sent), which is exactly
// what proves FIFO order (buf[i] == recvd + i), no-loss / no-dup (every seq in
// [0,sent) is delivered or buffered, each once), and the capacity bound. The glue
// holds the real T VecDeque and moves values in lockstep with these decisions.

pub struct ChannelKernel {
  pub buffered: u64,
  pub reserved: u64,
  pub capacity: u64,
  pub sent: Ghost<nat>,
  pub recvd: Ghost<nat>,
  pub buf: Ghost<Seq<nat>>,
}

pub open spec fn ch_wf(k: ChannelKernel) -> bool {
  &&& k.buffered as nat == k.buf@.len()
  &&& k.sent@ == k.recvd@ + k.buf@.len()
  &&& (forall |i: int| 0 <= i < k.buf@.len() ==> k.buf@[i] == k.recvd@ + i)
  &&& k.buffered as nat + k.reserved as nat <= k.capacity as nat
}

impl ChannelKernel {
  pub fn new(capacity: u64) -> (k: ChannelKernel)
    ensures
      ch_wf(k),
      k.buffered == 0,
      k.reserved == 0,
      k.capacity == capacity,
      k.sent@ == 0,
      k.recvd@ == 0,
  {
    let k = ChannelKernel {
      buffered: 0,
      reserved: 0,
      capacity,
      sent: Ghost(0),
      recvd: Ghost(0),
      buf: Ghost(Seq::empty()),
    };
    proof {
      assert(k.buf@.len() == 0);
    }
    k
  }

  // Try to enqueue a value (try_send): succeeds iff there is free capacity.
  pub fn try_push(&mut self) -> (ok: bool)
    requires
      ch_wf(*old(self)),
    ensures
      ch_wf(*self),
      ok == (old(self).buffered + old(self).reserved < old(self).capacity),
      ok ==> self.buffered == old(self).buffered + 1 && self.sent@ == old(self).sent@ + 1
        && self.recvd@ == old(self).recvd@,
      !ok ==> self.buffered == old(self).buffered && self.sent@ == old(self).sent@,
  {
    if self.buffered + self.reserved < self.capacity {
      let ghost s = self.sent@;
      self.buffered = self.buffered + 1;
      self.buf = Ghost(self.buf@.push(s));
      self.sent = Ghost(self.sent@ + 1);
      proof {
        assert forall |i: int| 0 <= i < self.buf@.len() implies self.buf@[i] == self.recvd@ + i by {}
      }
      true
    } else {
      false
    }
  }

  // Dequeue the oldest value (recv): succeeds iff the buffer is non-empty. The
  // delivered seq is exactly the oldest one, buf[0] == recvd (FIFO).
  pub fn pop(&mut self) -> (ok: bool)
    requires
      ch_wf(*old(self)),
    ensures
      ch_wf(*self),
      ok == (old(self).buffered > 0),
      ok ==> old(self).buf@[0] == old(self).recvd@
        && self.recvd@ == old(self).recvd@ + 1
        && self.buffered == old(self).buffered - 1,
      !ok ==> self.recvd@ == old(self).recvd@ && self.buffered == old(self).buffered,
  {
    if self.buffered > 0 {
      self.buffered = self.buffered - 1;
      self.buf = Ghost(self.buf@.drop_first());
      self.recvd = Ghost(self.recvd@ + 1);
      proof {
        assert forall |i: int| 0 <= i < self.buf@.len() implies self.buf@[i] == self.recvd@ + i by {}
      }
      true
    } else {
      false
    }
  }

  // Reserve a slot (Sender::reserve): succeeds iff there is free capacity.
  pub fn reserve(&mut self) -> (ok: bool)
    requires
      ch_wf(*old(self)),
    ensures
      ch_wf(*self),
      ok == (old(self).buffered + old(self).reserved < old(self).capacity),
      ok ==> self.reserved == old(self).reserved + 1,
      !ok ==> self.reserved == old(self).reserved,
      self.buffered == old(self).buffered && self.sent@ == old(self).sent@,
  {
    if self.buffered + self.reserved < self.capacity {
      self.reserved = self.reserved + 1;
      true
    } else {
      false
    }
  }

  // Fill a previously reserved slot (Permit::send): no capacity re-check needed.
  pub fn fill(&mut self)
    requires
      ch_wf(*old(self)),
      old(self).reserved > 0,
    ensures
      ch_wf(*self),
      self.buffered == old(self).buffered + 1,
      self.reserved == old(self).reserved - 1,
      self.sent@ == old(self).sent@ + 1,
  {
    let ghost s = self.sent@;
    self.buffered = self.buffered + 1;
    self.reserved = self.reserved - 1;
    self.buf = Ghost(self.buf@.push(s));
    self.sent = Ghost(self.sent@ + 1);
    proof {
      assert forall |i: int| 0 <= i < self.buf@.len() implies self.buf@[i] == self.recvd@ + i by {}
    }
  }

  // Release a reserved slot without filling it (Permit dropped).
  pub fn unreserve(&mut self)
    requires
      ch_wf(*old(self)),
      old(self).reserved > 0,
    ensures
      ch_wf(*self),
      self.reserved == old(self).reserved - 1,
      self.buffered == old(self).buffered && self.sent@ == old(self).sent@,
  {
    self.reserved = self.reserved - 1;
  }
}

}
