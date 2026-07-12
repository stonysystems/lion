use vstd::prelude::*;

verus! {

// Sleep's method tag (the `M` of the generic UtilityEvent<M, R>). Sleep exposes
// a single async method — Future::poll — so there is one variant. (A future
// `Reset` variant, a synchronous state-mutating call, would surface as a
// TickResult::Ongoing tick.)
#[derive(PartialEq, Eq)]
pub enum SleepMethod {
  Poll,
}

// Sleep's return type (the `R`) is the unit `()`: a finished sleep yields `()`.

}
