use vstd::prelude::*;

verus! {

// Paper reference: Listing 4 (Invariant templates over event logs)
// specification.tex lines 237-248
//
// struct LocalLiveness<L> {
//   acceptance: spec fn(L, nat) -> bool,
//   fulfillment: spec fn(L, nat, nat) -> bool,
//   timely: spec fn(L, nat, nat) -> bool,
// }
// spec fn local_liveness_satisfied<L>(p: LocalLiveness<L>, l: L) -> bool {
//   forall |i: nat| (p.acceptance)(l, i) ==> exists |j: nat|
//     j > i && (p.fulfillment)(l, i, j) && (p.timely)(l, i, j)
// }
//
// Note: We use `int` instead of `nat` for flexibility with log indices.
#[verifier::reject_recursive_types(L)]
pub struct LocalLiveness<L> {
  pub acceptance: spec_fn(L, int) -> bool,
  pub fulfillment: spec_fn(L, int, int) -> bool,
  pub timely: spec_fn(L, int, int) -> bool,
}

pub open spec fn local_liveness_satisfied<L>(p: LocalLiveness<L>, l: L) -> bool {
  forall |i: int|
    #[trigger] (p.acceptance)(l, i) ==>
    exists |j: int|
      #![trigger (p.fulfillment)(l, i, j)]
      j > i &&
      (p.fulfillment)(l, i, j) &&
      (p.timely)(l, i, j)
}

}
