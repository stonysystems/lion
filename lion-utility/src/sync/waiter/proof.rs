use vstd::prelude::*;
use lion_utility_spec::view_types::*;
use lion_utility_spec::generic::types::TickResult;
use lion_utility_spec::generic::events::*;
use lion_utility_spec::generic::log::*;
use lion_utility_spec::generic::invariants::*;
use lion_utility_spec::generic::extension::*;
use lion_utility_spec::framework::action_safety::*;
use crate::sync::waiter::method::SyncMethod;

verus! {

// The WaiterKernel's logical event log.
pub type SyncLog = Log<SyncMethod, ()>;

// ── Event constructors (the only shapes the WaiterKernel emits) ──
pub open spec fn ev_tick_begin(w: WakerView, m: SyncMethod) -> UtilityEvent<SyncMethod, ()> {
  UtilityEvent::Inbound(UtilityInbound::Tick { waker: w, method: m, result: None })
}
pub open spec fn ev_tick_end(w: WakerView, m: SyncMethod, r: TickResult<()>) -> UtilityEvent<SyncMethod, ()> {
  UtilityEvent::Inbound(UtilityInbound::Tick { waker: w, method: m, result: Some(r) })
}
pub open spec fn ev_pass_waker(w: WakerView) -> UtilityEvent<SyncMethod, ()> {
  UtilityEvent::Outbound(UtilityOutbound::PassWaker { waker: w })
}
pub open spec fn ev_wake_waker(w: WakerView) -> UtilityEvent<SyncMethod, ()> {
  UtilityEvent::Outbound(UtilityOutbound::WakeWaker { waker: w })
}
pub open spec fn ev_cancel_waker(w: WakerView) -> UtilityEvent<SyncMethod, ()> {
  UtilityEvent::Outbound(UtilityOutbound::CancelWaker { waker: w })
}

// ── Well-formedness ──
// Sync primitives hold no reactor token, so resource_ownership is vacuous; the
// content is wakeup_guarantee via the PassWaker disjunct. (Liveness — the
// PassWaker Contract — is a separate obligation, see proof of bounded-liveness.)
pub open spec fn wf(l: SyncLog) -> bool {
  utility_inv(l)
}

// ── Segments ──
// One `Wait` poll: permit available ⇒ complete; else park (emit PassWaker) ⇒ pending.
pub enum WaitOutcome { Ready, Park }

pub open spec fn wait_segment(w: WakerView, out: WaitOutcome) -> SyncLog {
  match out {
    WaitOutcome::Ready =>
      seq![ev_tick_begin(w, SyncMethod::Wait), ev_tick_end(w, SyncMethod::Wait, TickResult::Finished(()))],
    WaitOutcome::Park =>
      seq![ev_tick_begin(w, SyncMethod::Wait), ev_pass_waker(w),
        ev_tick_end(w, SyncMethod::Wait, TickResult::Pending)],
  }
}

// One `Signal` call (synchronous ⇒ Ongoing): wake a parked waiter, or store a permit.
pub enum SignalOutcome { Woke(WakerView), Stored }

pub open spec fn signal_segment(notifier: WakerView, out: SignalOutcome) -> SyncLog {
  match out {
    SignalOutcome::Woke(waiter) =>
      seq![ev_tick_begin(notifier, SyncMethod::Signal), ev_wake_waker(waiter),
        ev_tick_end(notifier, SyncMethod::Signal, TickResult::Ongoing(()))],
    SignalOutcome::Stored =>
      seq![ev_tick_begin(notifier, SyncMethod::Signal),
        ev_tick_end(notifier, SyncMethod::Signal, TickResult::Ongoing(()))],
  }
}

// ── structural facts: both segments are bracketed (tick_begin … tick_end) with
// no tick in the strict middle and no resource op anywhere ──
proof fn lemma_wait_facts(pre: SyncLog, w: WakerView, out: WaitOutcome)
  ensures
    ({
      let suf = wait_segment(w, out);
      let post = pre + suf;
      let n = pre.len() as int;
      let len = suf.len() as int;
      &&& post.len() == n + len
      &&& post[n] == ev_tick_begin(w, SyncMethod::Wait)
      &&& (forall |k: int| n < k < n + len - 1 ==> !is_tick_begin_at(post, k) && !is_tick_end_at(post, k))
      &&& (forall |k: int| n <= k < n + len ==>
            !is_deregister_timer_at(post, k) && !is_deregister_io_at(post, k) && !is_set_io_waker_at(post, k))
    }),
{
  let suf = wait_segment(w, out);
  let post = pre + suf;
  let n = pre.len() as int;
  let len = suf.len() as int;
  lemma_index_suffix(pre, suf, 0);
  assert forall |k: int| n < k < n + len - 1 implies
    (!is_tick_begin_at(post, k) && !is_tick_end_at(post, k)) by { lemma_index_suffix(pre, suf, k - n); }
  assert forall |k: int| n <= k < n + len implies
    (!is_deregister_timer_at(post, k) && !is_deregister_io_at(post, k) && !is_set_io_waker_at(post, k)) by {
    lemma_index_suffix(pre, suf, k - n);
  }
}

proof fn lemma_signal_facts(pre: SyncLog, notifier: WakerView, out: SignalOutcome)
  ensures
    ({
      let suf = signal_segment(notifier, out);
      let post = pre + suf;
      let n = pre.len() as int;
      let len = suf.len() as int;
      &&& post.len() == n + len
      &&& (forall |k: int| n <= k < n + len ==> !is_tick_end_pending_at(post, k))
      &&& (forall |k: int| n <= k < n + len ==>
            !is_deregister_timer_at(post, k) && !is_deregister_io_at(post, k) && !is_set_io_waker_at(post, k))
    }),
{
  let suf = signal_segment(notifier, out);
  let post = pre + suf;
  let n = pre.len() as int;
  let len = suf.len() as int;
  assert forall |k: int| n <= k < n + len implies !is_tick_end_pending_at(post, k) by {
    lemma_index_suffix(pre, suf, k - n);
  }
  assert forall |k: int| n <= k < n + len implies
    (!is_deregister_timer_at(post, k) && !is_deregister_io_at(post, k) && !is_set_io_waker_at(post, k)) by {
    lemma_index_suffix(pre, suf, k - n);
  }
}

// ── wakeup_guarantee preserved ──
#[verifier::rlimit(50)]
proof fn lemma_wait_wakeup(pre: SyncLog, w: WakerView, out: WaitOutcome)
  requires utility_inv(pre),
  ensures action_safety_satisfied(wakeup_guarantee::<SyncMethod, ()>(), pre + wait_segment(w, out)),
{
  let suf = wait_segment(w, out);
  let post = pre + suf;
  let p = wakeup_guarantee::<SyncMethod, ()>();
  let n = pre.len() as int;
  let len = suf.len() as int;
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by { lemma_index_prefix(pre, suf, i); }
  assert forall |i: int| 0 <= i < pre.len() && (p.validity)(pre, i) implies
    #[trigger] (p.validity)(post, i) by {
    if wakeup_validity(pre, i) { lemma_wakeup_validity_monotone(pre, suf, i); }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p.acceptance)(post, i)) implies
    (p.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_wait_facts(pre, w, out);
      match out {
        WaitOutcome::Ready => {
          lemma_index_suffix(pre, suf, i - n);
          assert(!is_tick_end_pending_at(post, i));
        }
        WaitOutcome::Park => {
          lemma_index_suffix(pre, suf, len - 1);
          lemma_index_suffix(pre, suf, len - 2);
          if is_tick_end_pending_at(post, i) {
            assert(i == n + len - 1);
            assert(post[i] == ev_tick_end(w, SyncMethod::Wait, TickResult::Pending));
            assert(post[n + 1] == ev_pass_waker(w));
            assert(complete_tick_cycle(post, n, i));
            assert(is_pass_waker_at(post, n + 1) && get_pass_waker_waker(post[n + 1]) == w);
            assert(passwaker_armed_in_cycle(post, w, n, i));
            assert(active_wakeup_source_for(post, w, n, i));
            assert(get_tick_waker(post[i]) == w);
            assert(wakeup_validity(post, i));
          }
        }
      }
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

#[verifier::rlimit(50)]
proof fn lemma_signal_wakeup(pre: SyncLog, notifier: WakerView, out: SignalOutcome)
  requires utility_inv(pre),
  ensures action_safety_satisfied(wakeup_guarantee::<SyncMethod, ()>(), pre + signal_segment(notifier, out)),
{
  let suf = signal_segment(notifier, out);
  let post = pre + suf;
  let p = wakeup_guarantee::<SyncMethod, ()>();
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by { lemma_index_prefix(pre, suf, i); }
  assert forall |i: int| 0 <= i < pre.len() && (p.validity)(pre, i) implies
    #[trigger] (p.validity)(post, i) by {
    if wakeup_validity(pre, i) { lemma_wakeup_validity_monotone(pre, suf, i); }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p.acceptance)(post, i)) implies
    (p.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_signal_facts(pre, notifier, out);
      assert(!is_tick_end_pending_at(post, i));
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

// ── resource_ownership preserved (vacuous: no resource ops in any segment) ──
#[verifier::rlimit(50)]
proof fn lemma_wait_resource(pre: SyncLog, w: WakerView, out: WaitOutcome)
  requires utility_inv(pre),
  ensures action_safety_satisfied(resource_ownership::<SyncMethod, ()>(), pre + wait_segment(w, out)),
{
  let suf = wait_segment(w, out);
  let post = pre + suf;
  let p = resource_ownership::<SyncMethod, ()>();
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by { lemma_index_prefix(pre, suf, i); }
  assert forall |i: int| 0 <= i < pre.len() && (p.validity)(pre, i) implies
    #[trigger] (p.validity)(post, i) by {
    lemma_index_prefix(pre, suf, i);
    if resource_validity(pre, i) {
      let rt = get_resource_token(pre[i]);
      lemma_token_active_before_monotone(pre, suf, rt, i);
    }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p.acceptance)(post, i)) implies
    (p.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_wait_facts(pre, w, out);
      assert(!resource_acceptance(post, i));
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

#[verifier::rlimit(50)]
proof fn lemma_signal_resource(pre: SyncLog, notifier: WakerView, out: SignalOutcome)
  requires utility_inv(pre),
  ensures action_safety_satisfied(resource_ownership::<SyncMethod, ()>(), pre + signal_segment(notifier, out)),
{
  let suf = signal_segment(notifier, out);
  let post = pre + suf;
  let p = resource_ownership::<SyncMethod, ()>();
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by { lemma_index_prefix(pre, suf, i); }
  assert forall |i: int| 0 <= i < pre.len() && (p.validity)(pre, i) implies
    #[trigger] (p.validity)(post, i) by {
    lemma_index_prefix(pre, suf, i);
    if resource_validity(pre, i) {
      let rt = get_resource_token(pre[i]);
      lemma_token_active_before_monotone(pre, suf, rt, i);
    }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p.acceptance)(post, i)) implies
    (p.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_signal_facts(pre, notifier, out);
      assert(!resource_acceptance(post, i));
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

// ── CancelWaker preserves both action-safety properties ──
// A bare CancelWaker is neither a tick end (wakeup_guarantee's acceptance) nor a
// resource op (resource_ownership's acceptance), so both are preserved vacuously
// on the new index; old indices transfer by monotonicity.
#[verifier::rlimit(50)]
proof fn lemma_cancel_wakeup(pre: SyncLog, w: WakerView)
  requires utility_inv(pre),
  ensures action_safety_satisfied(wakeup_guarantee::<SyncMethod, ()>(), pre + seq![ev_cancel_waker(w)]),
{
  let suf = seq![ev_cancel_waker(w)];
  let post = pre + suf;
  let p = wakeup_guarantee::<SyncMethod, ()>();
  let n = pre.len() as int;
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by { lemma_index_prefix(pre, suf, i); }
  assert forall |i: int| 0 <= i < pre.len() && (p.validity)(pre, i) implies
    #[trigger] (p.validity)(post, i) by {
    if wakeup_validity(pre, i) { lemma_wakeup_validity_monotone(pre, suf, i); }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p.acceptance)(post, i)) implies
    (p.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_index_suffix(pre, suf, i - n);
      assert(!is_tick_end_pending_at(post, i));
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

#[verifier::rlimit(50)]
proof fn lemma_cancel_resource(pre: SyncLog, w: WakerView)
  requires utility_inv(pre),
  ensures action_safety_satisfied(resource_ownership::<SyncMethod, ()>(), pre + seq![ev_cancel_waker(w)]),
{
  let suf = seq![ev_cancel_waker(w)];
  let post = pre + suf;
  let p = resource_ownership::<SyncMethod, ()>();
  let n = pre.len() as int;
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by { lemma_index_prefix(pre, suf, i); }
  assert forall |i: int| 0 <= i < pre.len() && (p.validity)(pre, i) implies
    #[trigger] (p.validity)(post, i) by {
    lemma_index_prefix(pre, suf, i);
    if resource_validity(pre, i) {
      let rt = get_resource_token(pre[i]);
      lemma_token_active_before_monotone(pre, suf, rt, i);
    }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p.acceptance)(post, i)) implies
    (p.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_index_suffix(pre, suf, i - n);
      assert(!resource_acceptance(post, i));
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

// ── A Wait poll / a Signal call preserves the safety invariant ──
#[verifier::rlimit(50)]
pub proof fn lemma_wait_preserves(pre: SyncLog, w: WakerView, out: WaitOutcome)
  requires wf(pre),
  ensures wf(pre + wait_segment(w, out)),
{
  lemma_wait_wakeup(pre, w, out);
  lemma_wait_resource(pre, w, out);
}

#[verifier::rlimit(50)]
pub proof fn lemma_signal_preserves(pre: SyncLog, notifier: WakerView, out: SignalOutcome)
  requires wf(pre),
  ensures wf(pre + signal_segment(notifier, out)),
{
  lemma_signal_wakeup(pre, notifier, out);
  lemma_signal_resource(pre, notifier, out);
}

#[verifier::rlimit(50)]
pub proof fn lemma_cancel_preserves(pre: SyncLog, w: WakerView)
  requires wf(pre),
  ensures wf(pre.push(ev_cancel_waker(w))),
{
  assert(pre.push(ev_cancel_waker(w)) =~= pre + seq![ev_cancel_waker(w)]);
  lemma_cancel_wakeup(pre, w);
  lemma_cancel_resource(pre, w);
}

}
