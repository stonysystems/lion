use vstd::prelude::*;
use lion_utility_spec::view_types::*;
use crate::net::tcp::method::IoMethod;
use crate::net::tcp::proof::*;

verus! {

// The verified io kernel. `rid` is the reactor io-resource token (registered at
// construction, cleared on drop); `log` is the ghost logical event log. The glue
// performs the real reactor effects (register/set_waker/deregister) and the real
// socket syscalls; the kernel records them and maintains the universal invariant.
pub struct IoKernel {
  pub rid: Option<u64>,
  pub log: Ghost<IoLog>,
}

pub open spec fn opt_rid_view(rid: Option<u64>) -> Option<ResourceIdView> {
  match rid {
    Some(x) => Some(x as nat),
    None => None,
  }
}

pub open spec fn well_formed(k: IoKernel) -> bool {
  wf(k.log@, opt_rid_view(k.rid))
}

// The kernel's decision for one io poll, returned to the glue: Arm means "this
// poll suspends — return Pending and set the waker"; Complete means "return
// Ready". The glue must follow this decision (it no longer decides on its own).
pub enum IoAction {
  Complete,
  Arm,
}

impl IoKernel {
  // Construct from a freshly-registered reactor token.
  pub fn new(reg_rid: u64) -> (s: IoKernel)
    ensures well_formed(s),
  {
    let s = IoKernel { rid: Some(reg_rid), log: Ghost(new_segment(reg_rid as nat)) };
    proof { lemma_io_new_preserves(reg_rid as nat); }
    s
  }

  // Decide and record one io poll cycle from the raw observations the glue made:
  // `was_ready` (reactor said the resource was ready) and `would_block` (the real
  // syscall returned WouldBlock). The kernel DECIDES to suspend exactly when the
  // resource was not ready or the op would block — and in that (and only that)
  // case the recorded segment arms a waker. The decision is returned so the glue
  // cannot suspend without the kernel having recorded the arm. (The waker token
  // is still an internal ghost; its identity with the real cx.waker() remains a
  // trusted glue detail.)
  pub fn poll_step(&mut self, m: IoMethod, was_ready: bool, would_block: bool) -> (a: IoAction)
    requires well_formed(*old(self)), old(self).rid is Some,
    ensures
      well_formed(*self),
      (a is Arm) <==> (!was_ready || would_block),
  {
    let arm = !was_ready || would_block;
    let ghost w: WakerView = arbitrary();
    let ghost old_log = self.log@;
    let r = self.rid.unwrap();
    let ghost rid_v = r as nat;
    let ghost out = if arm { IoOutcome::WouldBlock } else { IoOutcome::Ready };
    proof {
      lemma_io_poll_preserves(old_log, rid_v, w, m, out);
      self.log@ = old_log + io_step_segment(rid_v, w, m, out);
    }
    if arm { IoAction::Arm } else { IoAction::Complete }
  }

  // Record dropping the resource (deregister), preserving the invariant.
  pub fn drop_step(&mut self)
    requires well_formed(*old(self)),
    ensures well_formed(*self),
  {
    if let Some(r) = self.rid {
      let ghost old_log = self.log@;
      let ghost rid_v = r as nat;
      self.rid = None;
      proof {
        lemma_io_drop_preserves(old_log, rid_v);
        self.log@ = old_log + drop_segment(rid_v);
      }
    }
  }
}

}
