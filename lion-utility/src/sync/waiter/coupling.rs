use vstd::prelude::*;
use lion_utility_spec::view_types::*;
use lion_utility_spec::generic::types::TickResult;
use lion_utility_spec::generic::events::*;
use lion_utility_spec::generic::log::*;
use crate::sync::waiter::method::SyncMethod;
use crate::sync::waiter::proof::*;

verus! {

// ── Abstract state implied by the log (for the exec<->log coupling, §1a) ──
//
// `waiters(log)` = the sequence of parked waker ids the log implies: a PassWaker
// enqueues, a WakeWaker dequeues (removes the first matching id), a CancelWaker
// withdraws (also removes the first matching id — the parked future was dropped
// before its wake). The exec kernel's `queue` must equal this; that is what
// proves "no phantom/lost waiter, and a woken id was genuinely parked".

// Remove the first occurrence of `x` from `s`.
pub closed spec fn remove_first(s: Seq<int>, x: int) -> Seq<int>
  decreases s.len(),
{
  if s.len() == 0 {
    s
  } else if s[0] == x {
    s.subrange(1, s.len() as int)
  } else {
    seq![s[0]] + remove_first(s.subrange(1, s.len() as int), x)
  }
}

pub closed spec fn waiters(log: SyncLog) -> Seq<int>
  decreases log.len(),
{
  if log.len() == 0 {
    Seq::<int>::empty()
  } else {
    let i = (log.len() - 1) as int;
    let prev = waiters(log.subrange(0, i));
    if is_pass_waker_at(log, i) {
      prev.push(get_pass_waker_waker(log[i]))
    } else if is_wake_waker_at(log, i) {
      remove_first(prev, get_wake_waker_waker(log[i]))
    } else if is_cancel_waker_at(log, i) {
      remove_first(prev, get_cancel_waker_waker(log[i]))
    } else {
      prev
    }
  }
}

// ── Single-event append lemmas: how each event the kernel emits moves `waiters` ──
// (A tick — begin or end — is none of PassWaker / WakeWaker / CancelWaker, so it
// leaves `waiters` unchanged; a PassWaker pushes; a WakeWaker or a CancelWaker
// removes-first.)

proof fn lemma_waiters_push_tick_begin(log: SyncLog, w: WakerView, m: SyncMethod)
  ensures
    waiters(log.push(ev_tick_begin(w, m))) == waiters(log),
{
  let e = ev_tick_begin(w, m);
  let post = log.push(e);
  reveal_with_fuel(waiters, 2);
  assert(post.subrange(0, (post.len() - 1) as int) =~= log);
  assert(!is_pass_waker_at(post, (post.len() - 1) as int));
  assert(!is_wake_waker_at(post, (post.len() - 1) as int));
  assert(!is_cancel_waker_at(post, (post.len() - 1) as int));
}

proof fn lemma_waiters_push_tick_end(log: SyncLog, w: WakerView, m: SyncMethod, r: lion_utility_spec::generic::types::TickResult<()>)
  ensures
    waiters(log.push(ev_tick_end(w, m, r))) == waiters(log),
{
  let e = ev_tick_end(w, m, r);
  let post = log.push(e);
  reveal_with_fuel(waiters, 2);
  assert(post.subrange(0, (post.len() - 1) as int) =~= log);
  assert(!is_pass_waker_at(post, (post.len() - 1) as int));
  assert(!is_wake_waker_at(post, (post.len() - 1) as int));
  assert(!is_cancel_waker_at(post, (post.len() - 1) as int));
}

proof fn lemma_waiters_push_pass_waker(log: SyncLog, w: WakerView)
  ensures
    waiters(log.push(ev_pass_waker(w))) == waiters(log).push(w),
{
  let e = ev_pass_waker(w);
  let post = log.push(e);
  reveal_with_fuel(waiters, 2);
  assert(post.subrange(0, (post.len() - 1) as int) =~= log);
  assert(is_pass_waker_at(post, (post.len() - 1) as int));
  assert(get_pass_waker_waker(post[(post.len() - 1) as int]) == w);
}

proof fn lemma_waiters_push_wake_waker(log: SyncLog, w: WakerView)
  ensures
    waiters(log.push(ev_wake_waker(w))) == remove_first(waiters(log), w),
{
  let e = ev_wake_waker(w);
  let post = log.push(e);
  reveal_with_fuel(waiters, 2);
  assert(post.subrange(0, (post.len() - 1) as int) =~= log);
  assert(!is_pass_waker_at(post, (post.len() - 1) as int));
  assert(is_wake_waker_at(post, (post.len() - 1) as int));
  assert(get_wake_waker_waker(post[(post.len() - 1) as int]) == w);
}

// A CancelWaker withdraws the parked waiter: remove-first, like WakeWaker.
pub proof fn lemma_waiters_cancel(log: SyncLog, w: WakerView)
  ensures
    waiters(log.push(ev_cancel_waker(w))) == remove_first(waiters(log), w),
{
  let e = ev_cancel_waker(w);
  let post = log.push(e);
  reveal_with_fuel(waiters, 2);
  assert(post.subrange(0, (post.len() - 1) as int) =~= log);
  assert(!is_pass_waker_at(post, (post.len() - 1) as int));
  assert(!is_wake_waker_at(post, (post.len() - 1) as int));
  assert(is_cancel_waker_at(post, (post.len() - 1) as int));
  assert(get_cancel_waker_waker(post[(post.len() - 1) as int]) == w);
}

// ── permit ledger implied by the log (§1a requirement 3) ──
// Each event contributes independently: a Signal tick (Ongoing) stores a permit
// (+1), a WakeWaker hands one straight to a woken waiter (-1, cancelling the
// Signal tick of a Woke segment), a Wait that completed (Finished) consumed one
// (-1). `permit == init + available_permits(log)`.

pub open spec fn perm_delta(e: UtilityEvent<SyncMethod, ()>) -> int {
  if is_tick_end_ongoing(e) {
    1
  } else if is_wake_waker(e) {
    -1
  } else if is_tick_end_finished(e) {
    -1
  } else {
    0
  }
}

pub closed spec fn available_permits(log: SyncLog) -> int
  decreases log.len(),
{
  if log.len() == 0 {
    0
  } else {
    available_permits(log.drop_last()) + perm_delta(log.last())
  }
}

pub proof fn lemma_avail_push(log: SyncLog, e: UtilityEvent<SyncMethod, ()>)
  ensures
    available_permits(log.push(e)) == available_permits(log) + perm_delta(e),
{
  reveal_with_fuel(available_permits, 2);
  assert(log.push(e).drop_last() =~= log);
  assert(log.push(e).last() == e);
}

pub proof fn lemma_avail_empty()
  ensures
    available_permits(Seq::<UtilityEvent<SyncMethod, ()>>::empty()) == 0,
{
  reveal_with_fuel(available_permits, 1);
}

pub proof fn lemma_avail_wait(log: SyncLog, w: WakerView, out: WaitOutcome)
  ensures
    available_permits(log + wait_segment(w, out)) == available_permits(log) + match out {
      WaitOutcome::Ready => -1int,
      WaitOutcome::Park => 0int,
    },
{
  let tb = ev_tick_begin(w, SyncMethod::Wait);
  match out {
    WaitOutcome::Ready => {
      let te = ev_tick_end(w, SyncMethod::Wait, TickResult::Finished(()));
      assert(log + wait_segment(w, out) =~= log.push(tb).push(te));
      lemma_avail_push(log, tb);
      lemma_avail_push(log.push(tb), te);
    }
    WaitOutcome::Park => {
      let pw = ev_pass_waker(w);
      let te = ev_tick_end(w, SyncMethod::Wait, TickResult::Pending);
      assert(log + wait_segment(w, out) =~= log.push(tb).push(pw).push(te));
      lemma_avail_push(log, tb);
      lemma_avail_push(log.push(tb), pw);
      lemma_avail_push(log.push(tb).push(pw), te);
    }
  }
}

pub proof fn lemma_avail_signal(log: SyncLog, notifier: WakerView, out: SignalOutcome)
  ensures
    available_permits(log + signal_segment(notifier, out)) == available_permits(log) + match out {
      SignalOutcome::Woke(_) => 0int,
      SignalOutcome::Stored => 1int,
    },
{
  let tb = ev_tick_begin(notifier, SyncMethod::Signal);
  let te = ev_tick_end(notifier, SyncMethod::Signal, TickResult::Ongoing(()));
  match out {
    SignalOutcome::Woke(wid) => {
      let ww = ev_wake_waker(wid);
      assert(log + signal_segment(notifier, out) =~= log.push(tb).push(ww).push(te));
      lemma_avail_push(log, tb);
      lemma_avail_push(log.push(tb), ww);
      lemma_avail_push(log.push(tb).push(ww), te);
    }
    SignalOutcome::Stored => {
      assert(log + signal_segment(notifier, out) =~= log.push(tb).push(te));
      lemma_avail_push(log, tb);
      lemma_avail_push(log.push(tb), te);
    }
  }
}

// A CancelWaker is permit-neutral (the withdrawn waiter never held a permit).
pub proof fn lemma_avail_cancel(log: SyncLog, w: WakerView)
  ensures
    available_permits(log.push(ev_cancel_waker(w))) == available_permits(log),
{
  lemma_avail_push(log, ev_cancel_waker(w));
  assert(perm_delta(ev_cancel_waker(w)) == 0);
}

// ── exec queue (Seq<u64>) viewed as Seq<int>, + small algebraic lemmas ──

pub open spec fn queue_view(q: Seq<u64>) -> Seq<int> {
  q.map_values(|x: u64| x as int)
}

pub proof fn lemma_qv_push(q: Seq<u64>, x: u64)
  ensures
    queue_view(q.push(x)) == queue_view(q).push(x as int),
{
  assert(queue_view(q.push(x)) =~= queue_view(q).push(x as int));
}

pub proof fn lemma_qv_remove0(q: Seq<u64>)
  requires
    q.len() > 0,
  ensures
    queue_view(q.remove(0)) == queue_view(q).subrange(1, q.len() as int),
{
  assert(queue_view(q.remove(0)) =~= queue_view(q).subrange(1, q.len() as int));
}

pub proof fn lemma_qv_remove_at(q: Seq<u64>, i: int)
  requires
    0 <= i < q.len(),
  ensures
    queue_view(q.remove(i)) == queue_view(q).remove(i),
{
  assert(queue_view(q.remove(i)) =~= queue_view(q).remove(i));
}

pub proof fn lemma_qv_index(q: Seq<u64>, i: int)
  requires
    0 <= i < q.len(),
  ensures
    queue_view(q)[i] == q[i] as int,
{
}

pub proof fn lemma_remove_first_head(s: Seq<int>)
  requires
    s.len() > 0,
  ensures
    remove_first(s, s[0]) == s.subrange(1, s.len() as int),
{
  reveal_with_fuel(remove_first, 2);
}

// remove_first == remove-at-index, when `i` is the first occurrence of `x`.
pub proof fn lemma_remove_first_at(s: Seq<int>, x: int, i: int)
  requires
    0 <= i < s.len(),
    s[i] == x,
    forall |j: int| 0 <= j < i ==> s[j] != x,
  ensures
    remove_first(s, x) == s.remove(i),
  decreases i,
{
  reveal_with_fuel(remove_first, 2);
  if i == 0 {
    assert(s.subrange(1, s.len() as int) =~= s.remove(0));
  } else {
    let t = s.subrange(1, s.len() as int);
    assert(s[0] != x);
    assert(remove_first(s, x) == seq![s[0]] + remove_first(t, x));
    assert(t[i - 1] == x);
    assert forall |j: int| 0 <= j < i - 1 implies t[j] != x by {
      assert(t[j] == s[j + 1]);
    }
    lemma_remove_first_at(t, x, i - 1);
    assert(seq![s[0]] + t.remove(i - 1) =~= s.remove(i));
  }
}

pub proof fn lemma_waiters_empty()
  ensures
    waiters(Seq::<UtilityEvent<SyncMethod, ()>>::empty()) == Seq::<int>::empty(),
{
  reveal_with_fuel(waiters, 1);
}

// ── Segment-level: net effect of a whole wait/signal segment on `waiters` ──

pub proof fn lemma_waiters_wait(log: SyncLog, w: WakerView, out: WaitOutcome)
  ensures
    waiters(log + wait_segment(w, out)) == match out {
      WaitOutcome::Ready => waiters(log),
      WaitOutcome::Park => waiters(log).push(w),
    },
{
  let tb = ev_tick_begin(w, SyncMethod::Wait);
  match out {
    WaitOutcome::Ready => {
      let te = ev_tick_end(w, SyncMethod::Wait, TickResult::Finished(()));
      assert(log + wait_segment(w, out) =~= log.push(tb).push(te));
      lemma_waiters_push_tick_begin(log, w, SyncMethod::Wait);
      lemma_waiters_push_tick_end(log.push(tb), w, SyncMethod::Wait, TickResult::Finished(()));
    }
    WaitOutcome::Park => {
      let pw = ev_pass_waker(w);
      let te = ev_tick_end(w, SyncMethod::Wait, TickResult::Pending);
      assert(log + wait_segment(w, out) =~= log.push(tb).push(pw).push(te));
      lemma_waiters_push_tick_begin(log, w, SyncMethod::Wait);
      lemma_waiters_push_pass_waker(log.push(tb), w);
      lemma_waiters_push_tick_end(log.push(tb).push(pw), w, SyncMethod::Wait, TickResult::Pending);
    }
  }
}

pub proof fn lemma_waiters_signal(log: SyncLog, notifier: WakerView, out: SignalOutcome)
  ensures
    waiters(log + signal_segment(notifier, out)) == match out {
      SignalOutcome::Woke(wid) => remove_first(waiters(log), wid),
      SignalOutcome::Stored => waiters(log),
    },
{
  let tb = ev_tick_begin(notifier, SyncMethod::Signal);
  let te = ev_tick_end(notifier, SyncMethod::Signal, TickResult::Ongoing(()));
  match out {
    SignalOutcome::Woke(wid) => {
      let ww = ev_wake_waker(wid);
      assert(log + signal_segment(notifier, out) =~= log.push(tb).push(ww).push(te));
      lemma_waiters_push_tick_begin(log, notifier, SyncMethod::Signal);
      lemma_waiters_push_wake_waker(log.push(tb), wid);
      lemma_waiters_push_tick_end(log.push(tb).push(ww), notifier, SyncMethod::Signal, TickResult::Ongoing(()));
    }
    SignalOutcome::Stored => {
      assert(log + signal_segment(notifier, out) =~= log.push(tb).push(te));
      lemma_waiters_push_tick_begin(log, notifier, SyncMethod::Signal);
      lemma_waiters_push_tick_end(log.push(tb), notifier, SyncMethod::Signal, TickResult::Ongoing(()));
    }
  }
}

}
