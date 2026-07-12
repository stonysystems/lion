use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::module_spec::{ModuleSpec, progress_n, env_progress_n, progress_preserves_wf};

verus! {

#[verifier::reject_recursive_types(L)]
#[verifier::reject_recursive_types(T)]
pub struct AsyncContract<L, T> {
  pub acceptance: spec_fn(L, T) -> bool,
  pub fulfillment: spec_fn(L, T) -> bool,
  pub assumption: spec_fn(L, T) -> bool,
}
pub open spec fn ensures_response_within<L, T>(
  l: L,
  t: T,
  ms: ModuleSpec<L>,
  ac: AsyncContract<L, T>,
  n: nat
) -> bool {
  forall |l_prime: L|
    #[trigger] progress_n(ms.progress, l, l_prime, n)
    ==> (ac.fulfillment)(l_prime, t)
}

pub open spec fn ensures_response<L, T>(
  l: L,
  t: T,
  ms: ModuleSpec<L>,
  ac: AsyncContract<L, T>
) -> bool {
  exists |n: nat| ensures_response_within(l, t, ms, ac, n)
}

// Contract liveness: once the trigger event (acceptance) has occurred and the
// assumption holds, the response is guaranteed within bounded progress. (There is
// no separate `arrival` gate — the trigger event IS the arrival, so acceptance is
// used positively rather than as a `!trigger && arrival` pair.)
pub open spec fn bounded_liveness_without_arrival<L, T>(
  ms: ModuleSpec<L>,
  ac: AsyncContract<L, T>
) -> bool {
  progress_preserves_wf(ms) &&
  forall |t: T, l: L|
    (ms.well_formed)(l) &&
    (ac.acceptance)(l, t) &&
    (ac.assumption)(l, t) ==>
    ensures_response(l, t, ms, ac)
}

pub open spec fn env_response_within_trace<L, T>(
  l: L,
  t: T,
  ms: ModuleSpec<L>,
  ac: AsyncContract<L, T>,
  env: spec_fn(L, T) -> bool,
  n: nat,
) -> bool {
  // Response-filter form only (no filter non-emptiness — soft-vacuity closure is
  // out of scope for this work).
  forall |l_prime: L|
    #[trigger] env_progress_n(ms.progress, l, l_prime, n, env, t)
      ==> (ac.fulfillment)(l_prime, t)
}

pub open spec fn bounded_liveness_env_without_arrival<L, T>(
  ms: ModuleSpec<L>,
  ac: AsyncContract<L, T>,
  env: spec_fn(L, T) -> bool,
) -> bool {
  progress_preserves_wf(ms) &&
  forall |t: T, l: L|
    #![trigger env(l, t)]
    (ms.well_formed)(l) &&
    (ac.acceptance)(l, t) &&
    env(l, t) ==>
    exists |n: nat| #[trigger] env_response_within_trace(l, t, ms, ac, env, n)
}

}
