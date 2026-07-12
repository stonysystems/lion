use vstd::prelude::*;
use crate::executor::spec::log::*;
#[cfg(verus_keep_ghost)]
use crate::executor::invariants::fifo_task_selection::fifo_queue_at;

verus! {

// ============================================================================
// Stage 3 foundation (executor layer): a SATISFIABLE single-state replacement
// for the unsatisfiable persistent queue bound.
//
//   queue_length_bounded_persistent(l) = exists b. queue_bound_holds(l, b)   [UNSAT — see
//     the deleted queue_bound_holds: forall-extension uniform bound was constant false]
//
// The corrected form asserts the queue is bounded WITHIN l itself (over l's own
// positions), not over all syntactic prefix-extensions:
//
//   queue_bound_at(l, b)          = forall i in [0, l.len()]. |fifo_queue_at(l,i)| <= b
//   queue_length_bounded_single(l) = exists b. queue_bound_at(l, b)
//
// This is inhabited (proved below at the empty log with b = 0), in contrast to
// the persistent form which is false for every l. It is the executor-side
// analogue of composed/proof/assumption_satisfiable.rs::env_holds_at_state.
// ============================================================================

pub open spec fn queue_bound_at(l: Log, b: nat) -> bool {
  forall |i: int|
    #![trigger fifo_queue_at(l, i)]
    0 <= i <= l.len() ==> fifo_queue_at(l, i).len() <= b
}

pub open spec fn queue_length_bounded_single(l: Log) -> bool {
  exists |b: nat| #[trigger] queue_bound_at(l, b)
}

proof fn fifo_prefix_agree(a: Log, b: Log, i: int)
  requires
    0 <= i <= a.len(),
    is_prefix_of(a, b),
  ensures
    fifo_queue_at(a, i) == fifo_queue_at(b, i),
  decreases i
{
  if i <= 0 {
  } else {
    fifo_prefix_agree(a, b, i - 1);
    assert(a[i - 1] == b[i - 1]);
  }
}

// STRONGER than satisfiable: the single-state queue bound holds for EVERY log —
// a finite log has finitely many positions, so a max queue length exists. This
// makes a uniform queue bound universally available (unlike the persistent form,
// which is false for every log), a foundation for well-defined concrete bounds.
#[verifier::rlimit(50)]
pub proof fn queue_length_bounded_single_always(l: Log)
  ensures
    queue_length_bounded_single(l),
  decreases l.len()
{
  if l.len() == 0 {
    assert(queue_bound_at(l, 0nat)) by {
      assert forall |i: int| 0 <= i <= l.len() implies fifo_queue_at(l, i).len() <= 0nat by {
        assert(fifo_queue_at(l, 0).len() == 0);
      };
    };
  } else {
    let l_pre = l.subrange(0, l.len() - 1);
    assert(is_prefix_of(l_pre, l)) by {
      assert(l_pre =~= l.subrange(0, l_pre.len() as int));
    };
    queue_length_bounded_single_always(l_pre);
    let b_pre: nat = choose |b: nat| queue_bound_at(l_pre, b);
    let v: nat = fifo_queue_at(l, l.len() as int).len();
    let b: nat = if b_pre >= v { b_pre } else { v };
    assert(queue_bound_at(l, b)) by {
      assert forall |i: int| 0 <= i <= l.len() implies fifo_queue_at(l, i).len() <= b by {
        if i <= l.len() - 1 {
          fifo_prefix_agree(l_pre, l, i);
          assert(fifo_queue_at(l_pre, i).len() <= b_pre);
        } else {
          assert(i == l.len());
        }
      };
    };
    assert(queue_length_bounded_single(l));
  }
}

}
