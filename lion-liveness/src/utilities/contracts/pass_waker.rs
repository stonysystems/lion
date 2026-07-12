use vstd::prelude::*;
use crate::utilities::spec::events::*;
use crate::utilities::spec::log::*;
#[cfg(verus_keep_ghost)]
use crate::utilities::invariants::wakeup_guarantee::utilities_inv;
use crate::framework::async_contract::*;
use crate::framework::module_spec::ModuleSpec;

verus! {

// ============================================================================
// Pass-Waker Async Contract (per-utility verification template)
//
// This is the utility-module async contract from the paper (§5.1): for each
// cross-task utility instance `uid` (channel, semaphore, …), once a task
// registers its waker on the utility (acceptance: PassWaker{uid}), driving the
// utility sufficiently many times guarantees the waker is invoked
// (fulfillment: Woken{uid}).
//
// Here we DEFINE the template (ModuleSpec + AsyncContract). STATUS: this
// contract is currently a TEMPLATE ONLY — it is neither proven nor assumed
// anywhere. (The old composed env clause `pass_waker_contract_holds` asserted
// its bounded_liveness_without_arrival form, which was semantically false —
// with assumption_fn ≡ true nothing forces a Woken event — and was removed;
// cross-task wake delivery is assumed per-state in the composed
// `wake_delivers_here` instead.) Before re-asserting this contract as a
// theorem or assumption, `assumption_fn` MUST first be given a genuine,
// satisfiable wake-forcing precondition (e.g. "a matching send / permit
// release occurs"), and the response must be proven from the kernel.
//
// Anchored at `l_start` in the Option B style: trigger/response observe only the
// new segment [l_start.len(), l.len()).
// ============================================================================

// --- Utility step: one driving (poll) cycle of the utility kernel ---

pub open spec fn is_utility_prefix(l: Log, l_prime: Log) -> bool {
  l.len() <= l_prime.len() &&
  l =~= l_prime.subrange(0, l.len() as int)
}

pub open spec fn count_poll_ends_in(l: Log, start: int, end: int) -> nat
  decreases (if end > start { end - start } else { 0 }) as nat
{
  if start >= end || start < 0 || end > l.len() {
    0
  } else if is_poll_end(l[start]) {
    1 + count_poll_ends_in(l, start + 1, end)
  } else {
    count_poll_ends_in(l, start + 1, end)
  }
}

// One utility step = the kernel is driven through exactly one poll cycle AND
// the invariant holds on the reached state (mirroring executor_progress, which
// embeds executor_inv(l'); without this, progress_preserves_wf(utility_module_spec())
// was falsifiable by a bare Pending poll-end with no wakeup source).
pub open spec fn utility_step(l: Log, l_prime: Log) -> bool {
  is_utility_prefix(l, l_prime) &&
  count_poll_ends_in(l_prime, l.len() as int, l_prime.len() as int) == 1 &&
  utilities_inv(l_prime)
}

pub open spec fn utility_module_spec() -> ModuleSpec<Log> {
  ModuleSpec {
    well_formed: |l: Log| utilities_inv(l),
    progress: |l: Log, l_prime: Log| utility_step(l, l_prime),
  }
}

// --- Contract predicates (uid = which utility instance) ---

pub open spec fn has_pass_waker_with_uid_after(l: Log, uid: UID, start: int) -> bool {
  exists |i: int| #![trigger l[i]]
    start <= i < l.len() &&
    is_pass_waker(l[i]) &&
    get_pass_waker_uid(l[i]) == uid
}

pub open spec fn has_woken_with_uid_after(l: Log, uid: UID, start: int) -> bool {
  exists |i: int| #![trigger l[i]]
    start <= i < l.len() &&
    is_woken(l[i]) &&
    get_woken_uid(l[i]) == uid
}

// Acceptance (trigger, used positively via bounded_liveness_without_arrival):
// the task has registered its waker on utility `uid`. This is a past event
// (already in the log), so it is NOT anchored at l_start — it must hold at the
// anchor state itself.
pub open spec fn trigger_fn(l: Log, uid: UID) -> bool {
  has_pass_waker_with_uid_after(l, uid, 0)
}

// Fulfillment: the waker for utility `uid` was invoked, in the new segment
// [l_start.len(), l.len()).
pub open spec fn response_fn(l_start: Log, l: Log, uid: UID) -> bool {
  has_woken_with_uid_after(l, uid, l_start.len() as int)
}

// Assumption: utility-specific preconditions (channel needs a matching send,
// semaphore needs a permit release, …). PLACEHOLDER — `true` claims
// unconditional wakeup, which no concrete utility can discharge; see the
// STATUS note in the header before consuming this contract anywhere.
pub open spec fn assumption_fn(l: Log, uid: UID) -> bool {
  true
}

// Uses bounded_liveness_without_arrival: once the waker is registered (trigger)
// and the utility-specific assumption holds, driving the utility eventually
// invokes the waker (response = Woken).
pub open spec fn pass_waker_contract(l_start: Log) -> AsyncContract<Log, UID> {
  AsyncContract {
    acceptance: |l: Log, uid: UID| trigger_fn(l, uid),
    fulfillment: |l: Log, uid: UID| response_fn(l_start, l, uid),
    assumption: |l: Log, uid: UID| assumption_fn(l, uid),
  }
}

}
