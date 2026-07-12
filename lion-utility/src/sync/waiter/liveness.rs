use vstd::prelude::*;
use lion_utility_spec::view_types::*;
use lion_utility_spec::generic::events::*;
use lion_utility_spec::generic::log::*;
use lion_utility_spec::generic::contract::*;
use lion_utility_spec::framework::module_spec::*;
use lion_utility_spec::framework::async_contract::*;
use crate::sync::waiter::method::SyncMethod;
use crate::sync::waiter::proof::*;

verus! {

// ── The WaiterKernel as a module: well_formed = wf, progress = one kernel step ──
// A step either stutters, runs a Wait poll, runs a Signal call, or cancels a
// parked waiter (remove_step: the waiter's future was dropped).
pub open spec fn waiter_progress(l: SyncLog, l2: SyncLog) -> bool {
  ||| l2 == l
  ||| (exists |w: WakerView, out: WaitOutcome| l2 == l + #[trigger] wait_segment(w, out))
  ||| (exists |w: WakerView, out: SignalOutcome| l2 == l + #[trigger] signal_segment(w, out))
  ||| (exists |w: WakerView| l2 == l.push(#[trigger] ev_cancel_waker(w)))
}

pub open spec fn waiter_module_spec() -> ModuleSpec<SyncLog> {
  ModuleSpec { well_formed: |l: SyncLog| wf(l), progress: |l: SyncLog, l2: SyncLog| waiter_progress(l, l2) }
}

// ── The environmental fairness assumption, in ENV form (satisfiable) ──
//
// WHY ENV FORM: the waiter's WakeWaker IS the peer's atomic Signal(Woke) action — the kernel
// has no non-trivial liveness content of its own to prove (unlike the reactor timer/IO, whose
// wake is downstream of a proven cause). So the pass-waker contract is genuinely an
// ENVIRONMENTAL assumption: "a passed waker is delivered a WakeWaker". We state it, mirroring
// lion-liveness's `wake_delivers_here`, as a SATISFIABLE single-state implication.
//
// This REPLACES the old `bounded_wake_assumption`/`wakes_within`, which was 恒假
// (unsatisfiable): `wakes_within(l,w,n) = forall l2. progress_n(l,l2,n) ==> new_wake_waker_since(l,l2,w)`
// is falsified for EVERY n by the stutter/zero-step self-trace `l2 == l` (a `progress` disjunct),
// whose empty new-segment `[l.len, l.len)` contains no wake — so `∃n. wakes_within` is false and
// the whole liveness half discharged over an empty set.
pub open spec fn waiter_wake_env(l_start: SyncLog, l: SyncLog, w: WakerView) -> bool {
  &&& l_start.len() <= l.len()
  &&& (acceptance_fn(l, w) ==> new_wake_waker_since(l_start, l, w))
}

// Env-form contract (assumption folded into `env`; the env-form ignores `ac.assumption`).
pub open spec fn waiter_contract(l_start: SyncLog) -> AsyncContract<SyncLog, WakerView> {
  passwaker_to_wakewaker_contract::<SyncMethod, ()>(l_start, |_l: SyncLog, _w: WakerView| true)
}

// ── The PassWaker Contract (env-form bounded liveness) for the WaiterKernel ──
// Documentation theorem (intentionally uncalled): under the delivered-wake env
// assumption, every accepted PassWaker is answered within a bounded (n = 0)
// env-filtered continuation — the kernel's headline liveness result.
#[verifier::rlimit(50)]
pub proof fn lemma_waiter_bounded_liveness_env(l_start: SyncLog)
  ensures
    bounded_liveness_env_without_arrival(
      waiter_module_spec(), waiter_contract(l_start),
      |l: SyncLog, w: WakerView| waiter_wake_env(l_start, l, w)),
{
  let ms = waiter_module_spec();
  let ac = waiter_contract(l_start);
  let env = |l: SyncLog, w: WakerView| waiter_wake_env(l_start, l, w);

  // Part 1: progress preserves well-formedness (reuses the 2.1 safety lemmas).
  assert(progress_preserves_wf(ms)) by {
    assert forall |a: SyncLog, b: SyncLog|
      (ms.well_formed)(a) && #[trigger] (ms.progress)(a, b) implies (ms.well_formed)(b) by {
      assert(wf(a));
      assert(waiter_progress(a, b));
      if b == a {
      } else if exists |ww: WakerView, oo: WaitOutcome| b == a + #[trigger] wait_segment(ww, oo) {
        let (ww, oo): (WakerView, WaitOutcome) =
          choose |ww: WakerView, oo: WaitOutcome| b == a + #[trigger] wait_segment(ww, oo);
        lemma_wait_preserves(a, ww, oo);
      } else if exists |ww: WakerView, oo: SignalOutcome| b == a + #[trigger] signal_segment(ww, oo) {
        let (ww, oo): (WakerView, SignalOutcome) =
          choose |ww: WakerView, oo: SignalOutcome| b == a + #[trigger] signal_segment(ww, oo);
        lemma_signal_preserves(a, ww, oo);
      } else {
        let ww: WakerView = choose |ww: WakerView| b == a.push(#[trigger] ev_cancel_waker(ww));
        lemma_cancel_preserves(a, ww);
      }
    }
  }

  // Part 2: acceptance + env ==> bounded env-filtered response (at n = 0).
  // env + acceptance give the WakeWaker already delivered since l_start; the only env-good
  // 0-step continuation of `l` is `l` itself, which fulfils.
  assert forall |w: WakerView, l: SyncLog|
    #![trigger env(l, w)]
    (ms.well_formed)(l) && (ac.acceptance)(l, w) && env(l, w)
      implies exists |n: nat| #[trigger] env_response_within_trace(l, w, ms, ac, env, n) by {
    assert(waiter_wake_env(l_start, l, w));
    assert((ac.acceptance)(l, w));
    assert(acceptance_fn(l, w));
    assert(new_wake_waker_since(l_start, l, w));

    assert(env_response_within_trace(l, w, ms, ac, env, 0)) by {
      assert forall |l2: SyncLog|
        #[trigger] env_progress_n((ms.progress), l, l2, 0, env, w)
          implies (ac.fulfillment)(l2, w) by {
        let tr: Seq<SyncLog> = choose |tr: Seq<SyncLog>|
          #![trigger tr.len()] #![trigger tr.first()] #![trigger tr.last()]
          tr.len() == 1 && tr.first() == l && tr.last() == l2
          && is_valid_trace((ms.progress), tr) && env_holds_along((ms.progress), tr, env, w);
        assert(tr[0] == l && tr[tr.len() - 1] == l2);
        assert(l2 == l);
      }
    }
    assert(env_response_within_trace(l, w, ms, ac, env, 0));
  }
}

// ── Non-vacuity: the env-form precondition is satisfiable ──
// Witness: l_start = empty, l = [Wait/Park(w)] ++ [Signal/Woke(w)] — a well-formed log with a
// PassWaker(w) (acceptance) and a WakeWaker(w) (env's delivered fairness). So the theorem above
// is NOT hard-vacuous. (The soft vacuity — the env-good filter being non-empty — is deferred,
// same as the commented-out non-emptiness in `env_response_within_trace`.)
// Documentation theorem (intentionally uncalled): anti-vacuity witness for the
// bounded-liveness theorem above — its precondition set is inhabited.
pub proof fn lemma_waiter_env_satisfiable()
  ensures
    exists |l_start: SyncLog, l: SyncLog, w: WakerView|
      (waiter_module_spec().well_formed)(l)
      && acceptance_fn(l, w)
      && waiter_wake_env(l_start, l, w),
{
  let w: WakerView = arbitrary();
  let l_start: SyncLog = Seq::empty();
  let after_wait: SyncLog = l_start + wait_segment(w, WaitOutcome::Park);
  let l: SyncLog = after_wait + signal_segment(w, SignalOutcome::Woke(w));

  assert(wf(l_start));
  lemma_wait_preserves(l_start, w, WaitOutcome::Park);
  assert(wf(after_wait));
  lemma_signal_preserves(after_wait, w, SignalOutcome::Woke(w));
  assert(wf(l));

  // acceptance: the PassWaker(w) emitted by the Park segment.
  assert(is_pass_waker_at(l, (l_start.len() + 1) as int)) by {
    assert(l[(l_start.len() + 1) as int] == ev_pass_waker(w));
  }
  assert(acceptance_fn(l, w));

  // env: the WakeWaker(w) emitted by the Woke segment.
  assert(is_wake_waker_at(l, (after_wait.len() + 1) as int)) by {
    assert(l[(after_wait.len() + 1) as int] == ev_wake_waker(w));
  }
  assert(get_wake_waker_waker(l[(after_wait.len() + 1) as int]) == w);
  assert(new_wake_waker_since(l_start, l, w));
  assert(waiter_wake_env(l_start, l, w));
}

}
