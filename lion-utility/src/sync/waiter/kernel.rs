use vstd::prelude::*;
use lion_utility_spec::generic::events::*;
use crate::sync::waiter::method::SyncMethod;
use crate::sync::waiter::proof::*;
use crate::sync::waiter::coupling::*;

verus! {

// Decisions the kernel returns to the (trusted) glue. The glue supplies a waker
// identity `id` (the external waker it holds) and, on Woke/Park, does the real
// effect (store the waker, or wake the one named by `id`). All control logic —
// consume-permit vs park, wake-a-waiter vs store-a-permit, and *which* waiter —
// lives here, in verified code; the glue only observes and executes.
pub enum WaitAction {
  Ready,
  Park(u64),
}

pub enum SignalAction {
  Woke(u64),
  Stored,
}

// Index of the first occurrence of `id` in `q`, if any.
fn find_first(q: &Vec<u64>, id: u64) -> (r: Option<usize>)
  ensures
    match r {
      Some(i) => i < q.len() && q@[i as int] == id
        && forall |j: int| 0 <= j < i ==> q@[j] != id,
      None => !q@.contains(id),
    },
{
  let mut i: usize = 0;
  while i < q.len()
    invariant
      i <= q.len(),
      forall |j: int| 0 <= j < i ==> q@[j] != id,
    decreases q.len() - i,
  {
    if q[i] == id {
      return Some(i);
    }
    i = i + 1;
  }
  assert(!q@.contains(id));
  None
}

// Permit count + FIFO waiter queue (of glue-supplied waker ids) + the logical
// event log. `well_formed` = the safety invariant on the log (Phase 2.0/2.1);
// the queue/permit are the decision state.
pub struct WaiterKernel {
  pub permit: u64,
  pub queue: Vec<u64>,
  pub log: Ghost<SyncLog>,
  // birth permit count (Semaphore::new(n) ⇒ n; Notify/new ⇒ 0); the permit
  // ledger is anchored against it.
  pub init: Ghost<int>,
}

// well_formed = the log safety invariant AND the full exec<->log coupling (§1a):
//   - the waiter queue is exactly the parked-waiter sequence the log implies
//     (no phantom/lost waiters; signal wakes a genuinely parked id), and
//   - the permit counter equals the ledger the log implies (init + the net of
//     stored/consumed permits) — no silent permit drift.
pub open spec fn well_formed(k: WaiterKernel) -> bool {
  &&& wf(k.log@)
  &&& queue_view(k.queue@) == waiters(k.log@)
  &&& k.permit as int == k.init@ + available_permits(k.log@)
}

impl WaiterKernel {
  pub fn new() -> (k: WaiterKernel)
    ensures
      well_formed(k),
      k.log@ == Seq::<UtilityEvent<SyncMethod, ()>>::empty(),
  {
    let k = WaiterKernel { permit: 0, queue: Vec::new(), log: Ghost(Seq::empty()), init: Ghost(0) };
    proof {
      lemma_waiters_empty();
      lemma_avail_empty();
      assert(queue_view(k.queue@) =~= waiters(k.log@));
    }
    k
  }

  pub fn with_permits(p: u64) -> (k: WaiterKernel)
    ensures
      well_formed(k),
      k.log@ == Seq::<UtilityEvent<SyncMethod, ()>>::empty(),
  {
    let k = WaiterKernel { permit: p, queue: Vec::new(), log: Ghost(Seq::empty()), init: Ghost(p as int) };
    proof {
      lemma_waiters_empty();
      lemma_avail_empty();
      assert(queue_view(k.queue@) =~= waiters(k.log@));
    }
    k
  }

  // Non-blocking attempt: consume a permit iff one is available; never parks.
  // On success it records a Ready wait (waker 0, a placeholder — a consume with
  // no parking, hence no PassWaker), so the permit ledger stays exact.
  pub fn try_acquire_step(&mut self) -> (ok: bool)
    requires
      well_formed(*old(self)),
    ensures
      well_formed(*self),
      ok == (old(self).permit > 0),
      self.log@ == if ok {
        old(self).log@ + wait_segment(0, WaitOutcome::Ready)
      } else {
        old(self).log@
      },
  {
    let ghost old_log = self.log@;
    if self.permit > 0 {
      self.permit = self.permit - 1;
      proof {
        lemma_wait_preserves(old_log, 0, WaitOutcome::Ready);
        lemma_waiters_wait(old_log, 0, WaitOutcome::Ready);
        lemma_avail_wait(old_log, 0, WaitOutcome::Ready);
      }
      self.log = Ghost(old_log + wait_segment(0, WaitOutcome::Ready));
      true
    } else {
      false
    }
  }

  // The awaiting side. Consumes a stored permit (Ready) or parks `id` (Park).
  pub fn wait_step(&mut self, id: u64) -> (a: WaitAction)
    requires
      well_formed(*old(self)),
    ensures
      well_formed(*self),
      (a is Ready) <==> (old(self).permit > 0),
      self.log@ == old(self).log@ + wait_segment(id as int,
        if a is Ready { WaitOutcome::Ready } else { WaitOutcome::Park }),
  {
    let ghost old_log = self.log@;
    let ghost old_q = self.queue@;
    if self.permit > 0 {
      self.permit = self.permit - 1;
      proof {
        lemma_wait_preserves(old_log, id as int, WaitOutcome::Ready);
        lemma_waiters_wait(old_log, id as int, WaitOutcome::Ready);
        lemma_avail_wait(old_log, id as int, WaitOutcome::Ready);
      }
      self.log = Ghost(old_log + wait_segment(id as int, WaitOutcome::Ready));
      WaitAction::Ready
    } else {
      self.queue.push(id);
      proof {
        lemma_wait_preserves(old_log, id as int, WaitOutcome::Park);
        lemma_waiters_wait(old_log, id as int, WaitOutcome::Park);
        lemma_avail_wait(old_log, id as int, WaitOutcome::Park);
        lemma_qv_push(old_q, id);
      }
      self.log = Ghost(old_log + wait_segment(id as int, WaitOutcome::Park));
      WaitAction::Park(id)
    }
  }

  // The releasing side. Wakes the head waiter (Woke) or stores a permit (Stored).
  pub fn signal_step(&mut self, notifier: u64) -> (a: SignalAction)
    requires
      well_formed(*old(self)),
      old(self).permit < u64::MAX,
    ensures
      well_formed(*self),
      self.log@ == old(self).log@ + signal_segment(notifier as int,
        match a { SignalAction::Woke(wid) => SignalOutcome::Woke(wid as int), SignalAction::Stored => SignalOutcome::Stored }),
  {
    let ghost old_log = self.log@;
    let ghost old_q = self.queue@;
    if self.queue.len() > 0 {
      let head = self.queue.remove(0);
      proof {
        lemma_signal_preserves(old_log, notifier as int, SignalOutcome::Woke(head as int));
        lemma_qv_index(old_q, 0);
        assert(head as int == waiters(old_log)[0]);
        lemma_waiters_signal(old_log, notifier as int, SignalOutcome::Woke(head as int));
        lemma_remove_first_head(waiters(old_log));
        lemma_qv_remove0(old_q);
        lemma_avail_signal(old_log, notifier as int, SignalOutcome::Woke(head as int));
      }
      self.log = Ghost(old_log + signal_segment(notifier as int, SignalOutcome::Woke(head as int)));
      SignalAction::Woke(head)
    } else {
      self.permit = self.permit + 1;
      proof {
        lemma_signal_preserves(old_log, notifier as int, SignalOutcome::Stored);
        lemma_waiters_signal(old_log, notifier as int, SignalOutcome::Stored);
        lemma_avail_signal(old_log, notifier as int, SignalOutcome::Stored);
      }
      self.log = Ghost(old_log + signal_segment(notifier as int, SignalOutcome::Stored));
      SignalAction::Stored
    }
  }

  // A parked waiter withdraws (its future was dropped before its wake): remove
  // the first occurrence of `id` from the queue and record a CancelWaker. No-op
  // (no log event) when `id` is not parked, so a double drop is trivially safe.
  // Permits are untouched — a cancelled waiter never held one.
  pub fn remove_step(&mut self, id: u64) -> (removed: bool)
    requires
      well_formed(*old(self)),
    ensures
      well_formed(*self),
      removed == old(self).queue@.contains(id),
      !removed ==> *self == *old(self),
      removed ==> self.log@ == old(self).log@.push(ev_cancel_waker(id as int)),
      removed ==> queue_view(self.queue@) == remove_first(queue_view(old(self).queue@), id as int),
      self.permit == old(self).permit,
      self.init == old(self).init,
  {
    let ghost old_log = self.log@;
    let ghost old_q = self.queue@;
    match find_first(&self.queue, id) {
      Some(i) => {
        self.queue.remove(i);
        proof {
          lemma_cancel_preserves(old_log, id as int);
          lemma_waiters_cancel(old_log, id as int);
          lemma_avail_cancel(old_log, id as int);
          lemma_qv_remove_at(old_q, i as int);
          lemma_qv_index(old_q, i as int);
          assert forall |j: int| 0 <= j < i implies queue_view(old_q)[j] != id as int by {
            lemma_qv_index(old_q, j);
          }
          lemma_remove_first_at(queue_view(old_q), id as int, i as int);
        }
        self.log = Ghost(old_log.push(ev_cancel_waker(id as int)));
        true
      }
      None => {
        false
      }
    }
  }
}

}
