use vstd::prelude::*;
use lion_utility_spec::view_types::*;
use lion_utility_spec::generic::types::TickResult;
use lion_utility_spec::generic::events::*;
use lion_utility_spec::generic::log::*;
use lion_utility_spec::generic::invariants::*;
use lion_utility_spec::generic::extension::*;
use lion_utility_spec::framework::action_safety::*;
use crate::net::tcp::method::IoMethod;

verus! {

// The io utility's logical event log.
pub type IoLog = Log<IoMethod, ()>;

// ── Event constructors (the only shapes the io kernel emits) ──
pub open spec fn ev_tick_begin(w: WakerView, m: IoMethod) -> UtilityEvent<IoMethod, ()> {
  UtilityEvent::Inbound(UtilityInbound::Tick { waker: w, method: m, result: None })
}
pub open spec fn ev_tick_end(w: WakerView, m: IoMethod, r: TickResult<()>) -> UtilityEvent<IoMethod, ()> {
  UtilityEvent::Inbound(UtilityInbound::Tick { waker: w, method: m, result: Some(r) })
}
pub open spec fn ev_register_io(rid: ResourceIdView) -> UtilityEvent<IoMethod, ()> {
  UtilityEvent::Outbound(UtilityOutbound::RegisterIoResource {
    source: 0, interest: (true, true), result: Some(IoResultView::Ok(rid)),
  })
}
pub open spec fn ev_set_io_waker(rid: ResourceIdView, w: WakerView) -> UtilityEvent<IoMethod, ()> {
  UtilityEvent::Outbound(UtilityOutbound::SetIoWaker {
    resource_id: rid, interest: (true, true), waker: w, result: IoResultView::Ok(()),
  })
}
pub open spec fn ev_deregister_io(rid: ResourceIdView) -> UtilityEvent<IoMethod, ()> {
  UtilityEvent::Outbound(UtilityOutbound::DeregisterIoResource {
    resource_id: rid, result: IoResultView::Ok(()),
  })
}

// ── Well-formedness on (log, registered io token) ──
// The io resource is registered at construction and stays active until drop, so
// the coupling carries both forms used downstream (io_active_at for the wakeup
// source, token_active_before for resource-ownership).
pub open spec fn wf(l: IoLog, rid: Option<ResourceIdView>) -> bool {
  &&& utility_inv(l)
  &&& (rid matches Some(t) ==>
        io_active_at(l, t, l.len() as int) && token_active_before(l, t, l.len() as int))
}

// ── Segments ──
pub enum IoOutcome { Ready, WouldBlock }

pub open spec fn io_step_segment(rid: ResourceIdView, w: WakerView, m: IoMethod, out: IoOutcome) -> IoLog {
  match out {
    IoOutcome::Ready =>
      seq![ev_tick_begin(w, m), ev_tick_end(w, m, TickResult::Finished(()))],
    IoOutcome::WouldBlock =>
      seq![ev_tick_begin(w, m), ev_set_io_waker(rid, w), ev_tick_end(w, m, TickResult::Pending)],
  }
}
pub open spec fn new_segment(rid: ResourceIdView) -> IoLog { seq![ev_register_io(rid)] }
pub open spec fn drop_segment(rid: ResourceIdView) -> IoLog { seq![ev_deregister_io(rid)] }

// ── Structural facts about a poll segment (no tick in the middle; no dereg) ──
proof fn lemma_seg_facts(pre: IoLog, rid: ResourceIdView, w: WakerView, m: IoMethod, out: IoOutcome)
  ensures
    ({
      let suf = io_step_segment(rid, w, m, out);
      let post = pre + suf;
      let n = pre.len() as int;
      let len = suf.len() as int;
      &&& post.len() == n + len
      &&& post[n] == ev_tick_begin(w, m)
      &&& (forall |k: int| n < k < n + len - 1 ==>
            !is_tick_begin_at(post, k) && !is_tick_end_at(post, k))
      &&& (forall |k: int| n <= k < n + len ==>
            !is_deregister_timer_at(post, k) && !is_deregister_io_at(post, k))
    }),
{
  let suf = io_step_segment(rid, w, m, out);
  let post = pre + suf;
  let n = pre.len() as int;
  let len = suf.len() as int;
  lemma_index_suffix(pre, suf, 0);
  assert forall |k: int| n < k < n + len - 1 implies
    (!is_tick_begin_at(post, k) && !is_tick_end_at(post, k)) by {
    lemma_index_suffix(pre, suf, k - n);
  }
  assert forall |k: int| n <= k < n + len implies
    (!is_deregister_timer_at(post, k) && !is_deregister_io_at(post, k)) by {
    lemma_index_suffix(pre, suf, k - n);
  }
}

// ── wakeup_guarantee preserved by a poll segment ──
#[verifier::rlimit(50)]
proof fn lemma_io_poll_wakeup(pre: IoLog, rid: ResourceIdView, w: WakerView, m: IoMethod, out: IoOutcome)
  requires utility_inv(pre), io_active_at(pre, rid, pre.len() as int),
  ensures action_safety_satisfied(wakeup_guarantee::<IoMethod, ()>(), pre + io_step_segment(rid, w, m, out)),
{
  let suf = io_step_segment(rid, w, m, out);
  let post = pre + suf;
  let p = wakeup_guarantee::<IoMethod, ()>();
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
      lemma_seg_facts(pre, rid, w, m, out);
      if is_tick_end_pending_at(post, i) {
        // Only WouldBlock yields a Pending tick_end; it is the last event (n+2),
        // its cycle opens at the tick_begin (n) and SetIoWaker(rid,w) at n+1.
        lemma_index_suffix(pre, suf, len - 1);
        lemma_index_suffix(pre, suf, len - 2);
        assert(i == n + len - 1);
        assert(len == 3);
        assert(post[i] == ev_tick_end(w, m, TickResult::Pending));
        assert(post[n + 1] == ev_set_io_waker(rid, w));
        assert(complete_tick_cycle(post, n, i));
        // io_active_at(post, rid, i): from coupling + no dereg in the segment prefix.
        assert forall |j: int| n <= j < i implies
          !(#[trigger] is_deregister_io_at(post, j) && get_resource_token(post[j]) == rid) by {
        }
        lemma_io_active_at_extend(pre, suf, rid, i);
        assert(io_active_at(post, rid, i));
        assert(is_set_io_waker_at(post, n + 1));
        assert(get_resource_token(post[n + 1]) == rid);
        assert(get_set_io_waker_waker(post[n + 1]) == w);
        assert(io_armed_for_in_cycle(post, w, n, i));
        assert(active_wakeup_source_for(post, w, n, i));
        assert(get_tick_waker(post[i]) == w);
        assert(wakeup_validity(post, i));
      }
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

// ── resource_ownership preserved by a poll segment ──
#[verifier::rlimit(50)]
proof fn lemma_io_poll_resource(pre: IoLog, rid: ResourceIdView, w: WakerView, m: IoMethod, out: IoOutcome)
  requires utility_inv(pre), token_active_before(pre, rid, pre.len() as int),
  ensures action_safety_satisfied(resource_ownership::<IoMethod, ()>(), pre + io_step_segment(rid, w, m, out)),
{
  let suf = io_step_segment(rid, w, m, out);
  let post = pre + suf;
  let p = resource_ownership::<IoMethod, ()>();
  let n = pre.len() as int;
  let len = suf.len() as int;
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
      lemma_seg_facts(pre, rid, w, m, out);
      if resource_acceptance(post, i) {
        // The only resource op the segment emits is SetIoWaker(rid) at n+1 (WouldBlock).
        lemma_index_suffix(pre, suf, i - n);
        assert(i == n + 1 && len == 3);
        assert(post[i] == ev_set_io_waker(rid, w));
        assert(get_resource_token(post[i]) == rid);
        assert forall |j: int| n <= j < i implies !#[trigger] is_dereg_of_token_at(post, j, rid) by {
        }
        lemma_token_active_before_extend(pre, suf, rid, i);
        assert(token_active_before(post, rid, i));
      }
    }
  }
  lemma_action_safety_extend(p, pre, suf);
}

// ── A poll preserves wf (invariant + the registered token stays active) ──
#[verifier::rlimit(50)]
pub proof fn lemma_io_poll_preserves(pre: IoLog, rid: ResourceIdView, w: WakerView, m: IoMethod, out: IoOutcome)
  requires wf(pre, Some(rid)),
  ensures wf(pre + io_step_segment(rid, w, m, out), Some(rid)),
{
  let suf = io_step_segment(rid, w, m, out);
  let post = pre + suf;
  let n = pre.len() as int;
  lemma_io_poll_wakeup(pre, rid, w, m, out);
  lemma_io_poll_resource(pre, rid, w, m, out);
  assert(utility_inv(post));
  lemma_seg_facts(pre, rid, w, m, out);
  // coupling: rid still active at the new end (no dereg anywhere in the segment).
  assert forall |j: int| n <= j < post.len() implies
    !(#[trigger] is_deregister_io_at(post, j) && get_resource_token(post[j]) == rid) by {
  }
  assert forall |j: int| n <= j < post.len() implies !#[trigger] is_dereg_of_token_at(post, j, rid) by {
  }
  lemma_io_active_at_extend(pre, suf, rid, post.len() as int);
  lemma_token_active_before_extend(pre, suf, rid, post.len() as int);
}

// ── Construction (register the io resource) yields a well-formed kernel ──
#[verifier::rlimit(50)]
pub proof fn lemma_io_new_preserves(rid: ResourceIdView)
  ensures wf(new_segment(rid), Some(rid)),
{
  let l = new_segment(rid);
  assert(l.len() == 1);
  assert(l[0] == ev_register_io(rid));
  assert(action_safety_satisfied(wakeup_guarantee::<IoMethod, ()>(), l)) by {
    assert forall |i: int| #[trigger] (wakeup_guarantee::<IoMethod, ()>().acceptance)(l, i)
      implies (wakeup_guarantee::<IoMethod, ()>().validity)(l, i) by {
      assert(!is_tick_end_pending_at(l, i));
    }
  }
  assert(action_safety_satisfied(resource_ownership::<IoMethod, ()>(), l)) by {
    assert forall |i: int| #[trigger] (resource_ownership::<IoMethod, ()>().acceptance)(l, i)
      implies (resource_ownership::<IoMethod, ()>().validity)(l, i) by {
      assert(!resource_acceptance(l, i));
    }
  }
  assert(is_register_io_succ_at(l, 0) && get_register_io_token(l[0]) == rid);
  assert(is_register_succ_of_token_at(l, 0, rid));
  assert(io_active_at(l, rid, 1));
  assert(token_active_before(l, rid, 1));
}

// ── Drop (deregister the io resource) preserves the invariant ──
#[verifier::rlimit(50)]
pub proof fn lemma_io_drop_preserves(pre: IoLog, rid: ResourceIdView)
  requires wf(pre, Some(rid)),
  ensures wf(pre + drop_segment(rid), None::<ResourceIdView>),
{
  let suf: IoLog = drop_segment(rid);
  let post = pre + suf;
  let p_w = wakeup_guarantee::<IoMethod, ()>();
  let p_r = resource_ownership::<IoMethod, ()>();
  let n = pre.len() as int;
  // wakeup: the new event is a DeregisterIo, never a Pending tick_end.
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p_w.acceptance)(post, i)) == (p_w.acceptance)(pre, i)) by { lemma_index_prefix(pre, suf, i); }
  assert forall |i: int| 0 <= i < pre.len() && (p_w.validity)(pre, i) implies
    #[trigger] (p_w.validity)(post, i) by {
    if wakeup_validity(pre, i) { lemma_wakeup_validity_monotone(pre, suf, i); }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p_w.acceptance)(post, i)) implies
    (p_w.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_index_suffix(pre, suf, 0);
      assert(!is_tick_end_pending_at(post, i));
    }
  }
  lemma_action_safety_extend(p_w, pre, suf);
  // resource: the DeregisterIo(rid) targets the active rid.
  assert forall |i: int| 0 <= i < pre.len() implies
    ((#[trigger] (p_r.acceptance)(post, i)) == (p_r.acceptance)(pre, i)) by { lemma_index_prefix(pre, suf, i); }
  assert forall |i: int| 0 <= i < pre.len() && (p_r.validity)(pre, i) implies
    #[trigger] (p_r.validity)(post, i) by {
    lemma_index_prefix(pre, suf, i);
    if resource_validity(pre, i) {
      let rt = get_resource_token(pre[i]);
      lemma_token_active_before_monotone(pre, suf, rt, i);
    }
  }
  assert forall |i: int| !(0 <= i < pre.len()) && (#[trigger] (p_r.acceptance)(post, i)) implies
    (p_r.validity)(post, i) by {
    if 0 <= i < post.len() {
      lemma_index_suffix(pre, suf, 0);
      assert(i == n);
      assert(post[i] == ev_deregister_io(rid));
      assert(get_resource_token(post[i]) == rid);
      lemma_token_active_before_monotone(pre, suf, rid, n);
      assert(token_active_before(post, rid, i));
    }
  }
  lemma_action_safety_extend(p_r, pre, suf);
  assert(utility_inv(post));
}

}
