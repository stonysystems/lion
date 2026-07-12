use vstd::prelude::*;
use lion_utility_spec::view_types::*;
use lion_utility_spec::generic::types::TickResult;
use lion_utility_spec::generic::events::*;
use lion_utility_spec::generic::log::*;
use lion_utility_spec::generic::invariants::*;
use lion_utility_spec::generic::extension::*;
use lion_utility_spec::framework::action_safety::*;
use crate::time::sleep::method::SleepMethod;

verus! {

// The sleep utility's logical event log.
pub type SleepLog = Log<SleepMethod, ()>;

// ── Event constructors (the only event shapes the sleep kernel emits) ──
pub open spec fn ev_tick_begin(w: WakerView) -> UtilityEvent<SleepMethod, ()> {
  UtilityEvent::Inbound(UtilityInbound::Tick { waker: w, method: SleepMethod::Poll, result: None })
}
pub open spec fn ev_tick_end(w: WakerView, r: TickResult<()>) -> UtilityEvent<SleepMethod, ()> {
  UtilityEvent::Inbound(UtilityInbound::Tick { waker: w, method: SleepMethod::Poll, result: Some(r) })
}
pub open spec fn ev_register_timer(d: InstantView, w: WakerView, res: Option<ResourceIdView>) -> UtilityEvent<SleepMethod, ()> {
  UtilityEvent::Outbound(UtilityOutbound::RegisterTimer { deadline: d, waker: w, result: res })
}
pub open spec fn ev_deregister_timer(rid: ResourceIdView) -> UtilityEvent<SleepMethod, ()> {
  UtilityEvent::Outbound(UtilityOutbound::DeregisterTimer { resource_id: rid, result: true })
}

// ── Well-formedness on (log, currently-armed token) ──
// The kernel's standing invariant: the two universal utility invariants hold,
// and the armed token (if any) is still active.
pub open spec fn wf(l: SleepLog, rid: Option<ResourceIdView>) -> bool {
  &&& utility_inv(l)
  &&& (rid matches Some(t) ==> token_active_before(l, t, l.len() as int))
}

// ── One poll's outcome and the event segment it appends ──
pub enum PollOutcome {
  Expired,             // now >= deadline: complete with ()
  ArmedOk(ResourceIdView),  // not expired, reactor returned a fresh token: Pending
  RegisterErr,         // not expired, register failed: complete with ()
}

pub open spec fn dereg_prefix(old_rid: Option<ResourceIdView>) -> SleepLog {
  match old_rid {
    Some(old) => seq![ev_deregister_timer(old)],
    None => Seq::empty(),
  }
}

// The segment appended for one poll cycle (mirrors the real Sleep::poll).
pub open spec fn step_segment(w: WakerView, d: InstantView, old_rid: Option<ResourceIdView>, out: PollOutcome) -> SleepLog {
  match out {
    PollOutcome::Expired =>
      seq![ev_tick_begin(w), ev_tick_end(w, TickResult::Finished(()))],
    PollOutcome::ArmedOk(new) =>
      seq![ev_tick_begin(w)] + dereg_prefix(old_rid)
        + seq![ev_register_timer(d, w, Some(new)), ev_tick_end(w, TickResult::Pending)],
    PollOutcome::RegisterErr =>
      seq![ev_tick_begin(w)] + dereg_prefix(old_rid)
        + seq![ev_register_timer(d, w, None), ev_tick_end(w, TickResult::Finished(()))],
  }
}

pub open spec fn new_rid_of(out: PollOutcome) -> Option<ResourceIdView> {
  match out {
    PollOutcome::ArmedOk(new) => Some(new),
    _ => None,
  }
}

// ── Preservation lemma (proof skeleton) ──
// One poll preserves well-formedness: appending step_segment keeps utility_inv
// and the armed-token coupling.
// Structural index facts about a poll segment. `n = pre.len()`, `len = suf.len()`:
// suf[0] is the tick_begin; every strictly-middle index is an Outbound (non-tick).
proof fn lemma_seg_structure(pre: SleepLog, w: WakerView, d: InstantView, old_rid: Option<ResourceIdView>, out: PollOutcome)
  ensures
    ({
      let suf = step_segment(w, d, old_rid, out);
      let post = pre + suf;
      let n = pre.len() as int;
      let len = suf.len() as int;
      &&& post.len() == n + len
      &&& post[n] == ev_tick_begin(w)
      &&& (forall |k: int| n < k < n + len - 1 ==>
            !is_tick_begin_at(post, k) && !is_tick_end_at(post, k))
    }),
{
  let suf = step_segment(w, d, old_rid, out);
  let post = pre + suf;
  let n = pre.len() as int;
  let len = suf.len() as int;
  lemma_index_suffix(pre, suf, 0);
  assert forall |k: int| n < k < n + len - 1 implies
    (!is_tick_begin_at(post, k) && !is_tick_end_at(post, k)) by {
    lemma_index_suffix(pre, suf, k - n);
    match old_rid {
      Some(old) => match out {
        PollOutcome::Expired => { }
        PollOutcome::ArmedOk(new) => {
          assert(suf =~= seq![ev_tick_begin(w), ev_deregister_timer(old),
            ev_register_timer(d, w, Some(new)), ev_tick_end(w, TickResult::Pending)]);
        }
        PollOutcome::RegisterErr => {
          assert(suf =~= seq![ev_tick_begin(w), ev_deregister_timer(old),
            ev_register_timer(d, w, None), ev_tick_end(w, TickResult::Finished(()))]);
        }
      },
      None => match out {
        PollOutcome::Expired => { }
        PollOutcome::ArmedOk(new) => {
          assert(suf =~= seq![ev_tick_begin(w),
            ev_register_timer(d, w, Some(new)), ev_tick_end(w, TickResult::Pending)]);
        }
        PollOutcome::RegisterErr => {
          assert(suf =~= seq![ev_tick_begin(w),
            ev_register_timer(d, w, None), ev_tick_end(w, TickResult::Finished(()))]);
        }
      },
    }
  }
}

// wakeup_guarantee preserved by a poll segment.
#[verifier::rlimit(50)]
proof fn lemma_poll_wakeup(pre: SleepLog, w: WakerView, d: InstantView, old_rid: Option<ResourceIdView>, out: PollOutcome)
  requires utility_inv(pre),
  ensures action_safety_satisfied(wakeup_guarantee::<SleepMethod, ()>(), pre + step_segment(w, d, old_rid, out)),
{
  let suf = step_segment(w, d, old_rid, out);
  let post = pre + suf;
  let p = wakeup_guarantee::<SleepMethod, ()>();
  let n = pre.len() as int;
  let len = suf.len() as int;
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by {
    lemma_index_prefix(pre, suf, i);
  }
  assert forall |i: int| 0 <= i < pre.len() && (p.validity)(pre, i) implies
    #[trigger] (p.validity)(post, i) by {
    if wakeup_validity(pre, i) { lemma_wakeup_validity_monotone(pre, suf, i); }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p.acceptance)(post, i)) implies
    (p.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_seg_structure(pre, w, d, old_rid, out);
      if is_tick_end_pending_at(post, i) {
        let new = match out { PollOutcome::ArmedOk(x) => x, _ => arbitrary() };
        lemma_index_suffix(pre, suf, len - 1);
        lemma_index_suffix(pre, suf, len - 2);
        assert(i == n + len - 1);
        assert(post[i] == ev_tick_end(w, TickResult::Pending));
        assert(post[i - 1] == ev_register_timer(d, w, Some(new)));
        assert(complete_tick_cycle(post, n, i));
        assert(is_register_timer_succ_at(post, i - 1)
          && get_register_timer_waker(post[i - 1]) == w);
        assert(!timer_deregistered_after_in_cycle(post, get_register_timer_token(post[i - 1]), i - 1, i));
        assert(timer_armed_for_in_cycle(post, w, n, i));
        assert(active_wakeup_source_for(post, w, n, i));
        assert(get_tick_waker(post[i]) == w);
        assert(wakeup_validity(post, i));
      }
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

// resource_ownership preserved by a poll segment. The only resource op among new
// indices is the optional DeregisterTimer(old), present when old_rid = Some(old).
#[verifier::rlimit(50)]
proof fn lemma_poll_resource(pre: SleepLog, w: WakerView, d: InstantView, old_rid: Option<ResourceIdView>, out: PollOutcome)
  requires
    utility_inv(pre),
    old_rid matches Some(t) ==> token_active_before(pre, t, pre.len() as int),
  ensures action_safety_satisfied(resource_ownership::<SleepMethod, ()>(), pre + step_segment(w, d, old_rid, out)),
{
  let suf = step_segment(w, d, old_rid, out);
  let post = pre + suf;
  let p = resource_ownership::<SleepMethod, ()>();
  let n = pre.len() as int;
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by {
    lemma_index_prefix(pre, suf, i);
  }
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
      if resource_acceptance(post, i) {
        let old = match old_rid { Some(t) => t, None => arbitrary() };
        assert(old_rid matches Some(_) && i == n + 1) by {
          assert forall |m: int| 0 <= m < suf.len() implies
            (is_dereg_or_set_of_seg(w, d, old_rid, out, m) == resource_acceptance(post, n + m)) by {
            lemma_index_suffix(pre, suf, m);
          }
        }
        lemma_index_suffix(pre, suf, 1);
        assert(post[i] == ev_deregister_timer(old));
        assert(get_resource_token(post[i]) == old);
        lemma_token_active_before_monotone(pre, suf, old, n);
        assert(token_active_before(post, old, i));
      }
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

// Whether suffix element m is a resource op (used to locate the lone dereg).
pub open spec fn is_dereg_or_set_of_seg(w: WakerView, d: InstantView, old_rid: Option<ResourceIdView>, out: PollOutcome, m: int) -> bool {
  let suf = step_segment(w, d, old_rid, out);
  0 <= m < suf.len() && {
    let e = suf[m];
    is_deregister_timer(e) || is_deregister_io(e) || is_set_io_waker(e)
  }
}

// coupling: the armed token after the poll is active in the new log.
#[verifier::rlimit(50)]
proof fn lemma_poll_coupling(pre: SleepLog, w: WakerView, d: InstantView, old_rid: Option<ResourceIdView>, out: PollOutcome)
  ensures
    new_rid_of(out) matches Some(t) ==>
      token_active_before(pre + step_segment(w, d, old_rid, out), t,
        (pre + step_segment(w, d, old_rid, out)).len() as int),
{
  let suf = step_segment(w, d, old_rid, out);
  let post = pre + suf;
  let n = pre.len() as int;
  let len = suf.len() as int;
  if let PollOutcome::ArmedOk(new) = out {
    lemma_index_suffix(pre, suf, len - 2);
    assert(post[n + len - 2] == ev_register_timer(d, w, Some(new)));
    assert(is_register_succ_of_token_at(post, n + len - 2, new));
    assert forall |k: int| (n + len - 2) < k < post.len() implies
      !is_dereg_of_token_at(post, k, new) by {
      lemma_seg_structure(pre, w, d, old_rid, out);
      lemma_index_suffix(pre, suf, len - 1);
    }
    assert(token_active_before(post, new, post.len() as int));
  }
}

#[verifier::rlimit(50)]
pub proof fn lemma_poll_preserves(pre: SleepLog, w: WakerView, d: InstantView, old_rid: Option<ResourceIdView>, out: PollOutcome)
  requires wf(pre, old_rid)
  ensures wf(pre + step_segment(w, d, old_rid, out), new_rid_of(out))
{
  lemma_poll_wakeup(pre, w, d, old_rid, out);
  lemma_poll_resource(pre, w, d, old_rid, out);
  lemma_poll_coupling(pre, w, d, old_rid, out);
  assert(utility_inv(pre + step_segment(w, d, old_rid, out)));
}

// ── Drop transition ──
// drop deregisters the held token (if any): appends a single DeregisterTimer.
pub open spec fn drop_segment(old_rid: Option<ResourceIdView>) -> SleepLog {
  dereg_prefix(old_rid)
}

// wakeup_guarantee preserved by appending a single DeregisterTimer(old): no new
// Pending tick, so the only new index has false acceptance.
#[verifier::rlimit(50)]
proof fn lemma_drop_wakeup(pre: SleepLog, old: ResourceIdView)
  requires utility_inv(pre),
  ensures action_safety_satisfied(wakeup_guarantee::<SleepMethod, ()>(), pre + seq![ev_deregister_timer(old)]),
{
  let suf: SleepLog = seq![ev_deregister_timer(old)];
  let post = pre + suf;
  let p = wakeup_guarantee::<SleepMethod, ()>();
  assert(action_safety_satisfied(p, pre));
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by {
    lemma_index_prefix(pre, suf, i);
  }
  assert forall |i: int| 0 <= i < pre.len() && (p.validity)(pre, i) implies
    #[trigger] (p.validity)(post, i) by {
    if wakeup_validity(pre, i) {
      lemma_wakeup_validity_monotone(pre, suf, i);
    }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p.acceptance)(post, i)) implies
    (p.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_index_suffix(pre, suf, 0);
      assert(post[i] == ev_deregister_timer(old));
      assert(!is_tick_end_pending_at(post, i));
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

// resource_ownership preserved by appending DeregisterTimer(old) when old is
// active (the coupling precondition).
#[verifier::rlimit(50)]
proof fn lemma_drop_resource(pre: SleepLog, old: ResourceIdView)
  requires utility_inv(pre), token_active_before(pre, old, pre.len() as int),
  ensures action_safety_satisfied(resource_ownership::<SleepMethod, ()>(), pre + seq![ev_deregister_timer(old)]),
{
  let suf: SleepLog = seq![ev_deregister_timer(old)];
  let post = pre + suf;
  let p = resource_ownership::<SleepMethod, ()>();
  assert(action_safety_satisfied(p, pre));
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p.acceptance)(post, i)) == (p.acceptance)(pre, i)) by {
    lemma_index_prefix(pre, suf, i);
  }
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
      lemma_index_suffix(pre, suf, 0);
      assert(post[i] == ev_deregister_timer(old));
      assert(i == pre.len());
      assert(get_resource_token(post[i]) == old);
      lemma_token_active_before_monotone(pre, suf, old, pre.len() as int);
      assert(token_active_before(post, old, i));
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

#[verifier::rlimit(50)]
pub proof fn lemma_drop_preserves(pre: SleepLog, old_rid: Option<ResourceIdView>)
  requires wf(pre, old_rid)
  ensures wf(pre + drop_segment(old_rid), None::<ResourceIdView>)
{
  match old_rid {
    None => {
      assert(drop_segment(None) =~= Seq::<UtilityEvent<SleepMethod, ()>>::empty());
      assert(pre + drop_segment(None) =~= pre);
    }
    Some(old) => {
      let suf: SleepLog = seq![ev_deregister_timer(old)];
      assert(drop_segment(Some(old)) =~= suf);
      assert(token_active_before(pre, old, pre.len() as int));
      lemma_drop_wakeup(pre, old);
      lemma_drop_resource(pre, old);
      assert(utility_inv(pre + suf));
    }
  }
}

}
