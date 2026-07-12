use vstd::prelude::*;
use lion_utility_spec::view_types::*;
use crate::time::sleep::proof::*;

verus! {

// The verified kernel. Exec fields mirror the real Sleep (deadline + the
// currently-armed reactor timer token); `log` is the ghost logical event log
// the kernel maintains. All decision logic and invariant maintenance live here;
// the glue only realizes the reactor effects and feeds their results back.
pub struct SleepKernel {
  pub deadline: u64,
  pub rid: Option<u64>,
  pub log: Ghost<SleepLog>,
}

pub open spec fn opt_rid_view(rid: Option<u64>) -> Option<ResourceIdView> {
  match rid {
    Some(x) => Some(x as nat),
    None => None,
  }
}

// The kernel's standing invariant (delegates to the (log, armed-token) form).
pub open spec fn well_formed(k: SleepKernel) -> bool {
  wf(k.log@, opt_rid_view(k.rid))
}

// The kernel's decision for one poll, returned to the glue: Suspend means
// "return Pending" (an armed timer was recorded); Complete means "return Ready"
// (the deadline has passed); Fail means the deadline has NOT passed but the
// reactor refused the timer registration — no wake source exists, so the glue
// must not suspend (it panics; Tokio's time-driver failure semantics). The
// Fail tick is logged as Finished (the future never returns Pending), keeping
// wakeup_guarantee vacuous for that tick.
pub enum SleepAction {
  Complete,
  Suspend,
  Fail,
}

impl SleepKernel {
  // A fresh sleep with empty history is well-formed.
  pub fn new(deadline: u64) -> (s: SleepKernel)
    ensures well_formed(s),
  {
    let s = SleepKernel { deadline, rid: None, log: Ghost(Seq::empty()) };
    proof {
      assert(lion_utility_spec::framework::action_safety::action_safety_satisfied(
        lion_utility_spec::generic::invariants::wakeup_guarantee::<crate::time::sleep::method::SleepMethod, ()>(), s.log@));
      assert(lion_utility_spec::framework::action_safety::action_safety_satisfied(
        lion_utility_spec::generic::invariants::resource_ownership::<crate::time::sleep::method::SleepMethod, ()>(), s.log@));
    }
    s
  }

  // Decide and record one poll cycle from the raw observations: `now` (the real
  // clock the glue read) and `reg` (the reactor's register result — Some(token)
  // on success, None on failure/not-attempted). The kernel itself DECIDES whether
  // the sleep is still pending: only when the deadline has not passed AND a timer
  // was successfully armed. A register failure before the deadline is Fail (the
  // glue panics — it must neither suspend without a wake source nor complete
  // early). The decision is returned so the glue cannot suspend without the
  // kernel having recorded the armed timer. (The waker token threaded through
  // the segment is an internal ghost; its identity with the real cx.waker()
  // remains a trusted glue detail.)
  pub fn poll_step(&mut self, now: u64, reg: Option<u64>) -> (a: SleepAction)
    requires well_formed(*old(self)),
    ensures
      well_formed(*self),
      (a is Complete) <==> (now >= old(self).deadline),
      (a is Suspend) <==> (now < old(self).deadline && reg is Some),
      (a is Fail) <==> (now < old(self).deadline && reg is None),
  {
    let ghost w: WakerView = arbitrary();
    let ghost old_log = self.log@;
    let ghost old_rid_view = opt_rid_view(self.rid);
    let ghost d = self.deadline as int;

    if now >= self.deadline {
      self.rid = None;
      proof {
        lemma_poll_preserves(old_log, w, d, old_rid_view, PollOutcome::Expired);
        self.log@ = old_log + step_segment(w, d, old_rid_view, PollOutcome::Expired);
      }
      SleepAction::Complete
    } else {
      match reg {
        Some(x) => {
          self.rid = Some(x);
          proof {
            lemma_poll_preserves(old_log, w, d, old_rid_view, PollOutcome::ArmedOk(x as nat));
            self.log@ = old_log + step_segment(w, d, old_rid_view, PollOutcome::ArmedOk(x as nat));
          }
          SleepAction::Suspend
        }
        None => {
          self.rid = None;
          proof {
            lemma_poll_preserves(old_log, w, d, old_rid_view, PollOutcome::RegisterErr);
            self.log@ = old_log + step_segment(w, d, old_rid_view, PollOutcome::RegisterErr);
          }
          SleepAction::Fail
        }
      }
    }
  }

  // Record a reset to a new deadline: deregister the held token and re-arm later.
  // The log effect equals drop's (a DeregisterTimer); the new deadline is just an
  // exec field, not mentioned by the invariant.
  pub fn reset_step(&mut self, new_deadline: u64)
    requires well_formed(*old(self)),
    ensures well_formed(*self),
  {
    let ghost old_log = self.log@;
    let ghost old_rid_view = opt_rid_view(self.rid);
    self.rid = None;
    self.deadline = new_deadline;
    proof {
      lemma_drop_preserves(old_log, old_rid_view);
      self.log@ = old_log + drop_segment(old_rid_view);
    }
  }

  // Record dropping the sleep (deregister the held token), preserving invariant.
  pub fn drop_step(&mut self)
    requires well_formed(*old(self)),
    ensures well_formed(*self),
  {
    let ghost old_log = self.log@;
    let ghost old_rid_view = opt_rid_view(self.rid);
    self.rid = None;
    proof {
      lemma_drop_preserves(old_log, old_rid_view);
      self.log@ = old_log + drop_segment(old_rid_view);
    }
  }
}

}
