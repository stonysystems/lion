use vstd::prelude::*;

verus! {

// ── Verified data state machine for broadcast (§1b) ──
// A ring of the most-recent `capacity` slots, each with a monotonic seq. The
// kernel owns next_seq (total ever sent) and buffered (current ring length); the
// oldest buffered seq is `next_seq - buffered`. recv_step, given a receiver's seq
// cursor, decides Lagged / Ready / Park purely from the ring window, proving the
// lag semantics exactly (Lagged iff the cursor fell behind the ring) and that
// delivery is in seq order. The glue holds the real T ring and moves in lockstep.

pub enum BRecv {
  Lagged { skipped: u64, new_cursor: u64 },
  Ready { seq: u64 },
  Park,
}

pub struct BroadcastKernel {
  pub next_seq: u64,
  pub buffered: u64,
  pub capacity: u64,
}

pub open spec fn b_wf(k: BroadcastKernel) -> bool {
  &&& k.buffered as nat <= k.capacity as nat
  &&& k.buffered as nat <= k.next_seq as nat
}

impl BroadcastKernel {
  pub fn new(capacity: u64) -> (k: BroadcastKernel)
    ensures
      b_wf(k),
      k.next_seq == 0,
      k.buffered == 0,
      k.capacity == capacity,
  {
    BroadcastKernel { next_seq: 0, buffered: 0, capacity }
  }

  // Publish: assign the next seq (returned), append to the ring, dropping the
  // oldest when full. next_seq strictly increases (monotonic).
  pub fn send_step(&mut self) -> (seq: u64)
    requires
      b_wf(*old(self)),
      old(self).next_seq < u64::MAX,
    ensures
      b_wf(*self),
      seq == old(self).next_seq,
      self.next_seq == old(self).next_seq + 1,
      self.next_seq > old(self).next_seq,
  {
    let seq = self.next_seq;
    self.next_seq = self.next_seq + 1;
    if self.buffered < self.capacity {
      self.buffered = self.buffered + 1;
    }
    seq
  }

  // Given a receiver's cursor, decide Lagged / Ready / Park from the ring window
  // [oldest, next_seq) where oldest = next_seq - buffered.
  pub fn recv_step(&self, cursor: u64) -> (d: BRecv)
    requires
      b_wf(*self),
      cursor <= self.next_seq,
    ensures
      (d is Lagged) == ((cursor as int) < (self.next_seq as int) - (self.buffered as int)),
      (d is Ready) == (((self.next_seq as int) - (self.buffered as int) <= (cursor as int))
        && cursor < self.next_seq),
      (d is Park) == (cursor == self.next_seq),
      d matches BRecv::Lagged { skipped, new_cursor } ==> (new_cursor as int
        == (self.next_seq as int) - (self.buffered as int) && skipped as int == new_cursor as int - cursor as int),
      d matches BRecv::Ready { seq } ==> seq == cursor,
  {
    let oldest = self.next_seq - self.buffered;
    if cursor < oldest {
      BRecv::Lagged { skipped: oldest - cursor, new_cursor: oldest }
    } else if cursor < self.next_seq {
      BRecv::Ready { seq: cursor }
    } else {
      BRecv::Park
    }
  }
}

// ── Headline guarantee ──
// Documentation theorem (intentionally uncalled): the ring never buffers more
// entries than have ever been published (send monotonicity itself is stated
// directly in send_step's ensures: next_seq strictly increases).
pub proof fn lemma_buffered_bounded_by_next_seq(k: BroadcastKernel)
  requires b_wf(k),
  ensures k.buffered as nat <= k.next_seq as nat,
{
}

}
