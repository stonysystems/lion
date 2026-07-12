use vstd::prelude::*;
use crate::composed::spec::state::*;
use crate::composed::spec::types::*;
use crate::composed::spec::assumptions::*;
#[cfg(verus_keep_ghost)]
use crate::reactor::spec::events::get_set_waker_interest;
use crate::reactor::spec::log as reactor_log;
use crate::reactor::spec::types::ResourceIdView;
use crate::executor::spec::log as executor_log;

verus! {

// ============================================================================
// The SINGLE-STATE, satisfiable environment predicate.
//
// (History: the original `external_assumptions` had the shape
//   forall s_ext. is_extension_of(s, s_ext) ==> Clauses(s_ext)
// over a pure prefix relation with NO well-formedness constraint, which made
// it UNSATISFIABLE for every (s, tid) — an adversarial extension can, e.g.,
// append GetCurrentTime{timestamp:0} to break timestamps_positive. It has been
// deleted.) This module holds the corrected single-state predicate
// `env_holds_at_state_core` and proves it is inhabited.
// ============================================================================

// ----------------------------------------------------------------------------
// Single-state analogues of the clauses whose original form quantifies over
// extensions internally.
// ----------------------------------------------------------------------------

// The content-bearing FIXED-cap single-state poll-count clause, carried by
// env_N along a whole trace.
pub open spec fn bounded_poll_count_here_with_bound(s: ComposedState, tid: TaskId, n: nat) -> bool {
  count_polls_for_tid(s.executor_log, tid) >= n ==>
  task_polled_to_ready(s.executor_log, tid)
}

// Forward io-readiness (counts poll-events since the SetWaker sw_idx, so n>=1 is
// meaningful). Carries the io-ready bound n: if since the last
// SetWaker at least n poll-events occurred, a matching-interest IoEventReady exists
// — the single-state, per-trace-state form of io_ready_after_n_poll_events.
// A cancelled wait (rid deregistered after the waker was set) owes no readiness —
// mio never delivers for a deregistered fd; without this guard, cancellation
// traces were pruned from the env domain.
pub open spec fn io_ready_forward_here(l: reactor_log::Log, rid: ResourceIdView, n: nat) -> bool {
  let sw_idx = crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(l, rid, l.len() as int);
  (sw_idx >= 0 &&
   crate::reactor::contracts::bounded_io_wakeup::count_poll_events_in_range(l, sw_idx, l.len() as int) >= n &&
   !(exists |j: int|
       sw_idx < j < l.len() &&
       #[trigger] reactor_log::io_syscall_deregistered_at(l, j) &&
       crate::reactor::spec::events::get_io_syscall_deregister_rid(l[j]) == rid))
  ==> crate::reactor::contracts::bounded_io_wakeup::has_io_event_ready_matching_interest_after(
        l, rid, get_set_waker_interest(l[sw_idx]), sw_idx)
}

pub open spec fn io_assumption_here(l: reactor_log::Log, rid: ResourceIdView) -> bool {
  crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(l, rid)
}

// t5c: GUARDED by the io currency guard — the resource-hold obliges only rids
// some task is CURRENTLY awaiting (io analog of t4b's timer guard). Unguarded,
// it excluded normal wake→poll(Ready)→drop cleanup traces from the domain.
pub open spec fn contract_io_assumption_here(s: ComposedState) -> bool {
  forall |rid: ResourceIdView|
    #![trigger io_assumption_here(s.reactor_log, rid)]
    crate::composed::spec::assumptions::io_rid_current_poll_awaited(s, rid) ==>
    io_assumption_here(s.reactor_log, rid)
}

// (The old `env_holds_at_state` — the core plus the never-provable
// bound_dominance clause — was dead by construction and has been removed
// together with bound_dominance_holds; `env_holds_at_state_core` below is the
// live, satisfiable environment predicate.)

// The satisfiable core: every clause is a genuine single-state fact; on the
// empty state they are jointly satisfiable (proved below).
// The top theorem's precondition is satisfiable — witness {empty logs, schedule=[tid]}.
// Three of the four conjuncts (composed_well_formed, !end_to_end_trigger, end_to_end_env)
// are GENUINE, non-vacuous facts about the concrete witness. The fourth, end_to_end_arrival,
// holds via witness_arrival_holds, a ∀ whose successor domain is not shown non-empty (SOFT
// vacuity — see that lemma). So this establishes HARD non-vacuity (domain inhabited); the
// soft-vacuity of the arrival/goal ∀-filters is out of scope.
pub proof fn env_precondition_satisfiable()
  ensures
    exists |s: ComposedState, tid: TaskId|
      crate::composed::spec::progress::composed_well_formed(s) &&
      !crate::composed::spec::contract::end_to_end_trigger(s, tid) &&
      #[trigger] end_to_end_env(s, tid) &&
      crate::composed::spec::contract::end_to_end_arrival(s, tid),
{
  let tid: TaskId = 0;
  let w = arrival_witness(tid);
  witness_arrival_holds(tid);
  assert(!crate::composed::spec::contract::end_to_end_trigger(w, tid));
  assert(crate::composed::spec::progress::composed_well_formed(w)) by {
    assert(crate::executor::invariants::executor_inv(w.executor_log));
    assert(crate::reactor::invariants::reactor_inv(w.reactor_log));
    assert(crate::composed::spec::alignment::action_mediation_state(w)) by {
      assert(crate::composed::spec::alignment::operation_to_reactor_exists(w));
      assert(crate::composed::spec::alignment::reactor_to_operation_unique(w));
      assert(crate::composed::spec::alignment::reactor_outbound_to_task_exists(w));
      assert(crate::composed::spec::alignment::reactor_registration_to_task_exists(w));
      crate::composed::spec::alignment::monotonic_alignment_holds_empty(w);
      assert(crate::composed::spec::alignment::succ_deregister_by_owner(w)) by {
        reveal(crate::composed::spec::alignment::succ_deregister_by_owner);
      }
      assert(crate::composed::spec::alignment::deregister_matches_own_registration(w)) by {
        reveal(crate::composed::spec::alignment::deregister_matches_own_registration);
      }
      assert(crate::composed::spec::alignment::deregister_io_matches_own_registration(w)) by {
        reveal(crate::composed::spec::alignment::deregister_io_matches_own_registration);
      }
      assert(crate::composed::spec::alignment::succ_deregister_io_by_owner(w)) by {
        reveal(crate::composed::spec::alignment::succ_deregister_io_by_owner);
      }
    }
    assert(crate::composed::spec::alignment::observation_consistency_state(w));
  }
  env_core_holds_empty_logs(w, tid);
  assert(end_to_end_env(w, tid));
  assert(
    crate::composed::spec::progress::composed_well_formed(w) &&
    !crate::composed::spec::contract::end_to_end_trigger(w, tid) &&
    end_to_end_env(w, tid) &&
    crate::composed::spec::contract::end_to_end_arrival(w, tid));
}

// HARD non-vacuity: the top theorem holds AND its precondition is satisfiable (there is a
// real state meeting all four antecedent clauses), so the theorem is not a ∀ over an empty
// domain / contradictory precondition.
//
// SCOPE (honest): this closes HARD vacuity only. SOFT vacuity is partially closed by the
// four wake-path witnesses: the arrival ∀'s successor set IS exhibited (bs1_composed_progress
// proves composed_progress(arrival_witness(tid), bs1(tid))), and each witness shows a real
// env_N-good trace reaching Ready at n=2 (ete_reachable_N(arrival_witness, ·, 2, 2, tid)).
// BUDGET GAP CLOSED (F-A): b_domain_inhabited_at_any_n (inhabitation_budget.rs) extends the
// wake witness with idle stuttering ticks, so the response-filter domain is inhabited at
// EVERY budget n >= 2 — in particular at the proof-instantiated n* = chunk + cap·chunk
// (chunk >= cap + 2 >= 3, so n* >= 2 always). What remains open: □env ⇒ ◇goal realizability
// from ARBITRARY qualifying states (not just the constructed witnesses) — deliberately out
// of scope (same as the paper's Scope-of-Trust section).
pub proof fn top_theorem_precondition_satisfiable()
  ensures
    end_to_end_liveness_env_N_trace(),
    exists |s: ComposedState, tid: TaskId|
      crate::composed::spec::progress::composed_well_formed(s) &&
      !crate::composed::spec::contract::end_to_end_trigger(s, tid) &&
      #[trigger] end_to_end_env(s, tid) &&
      crate::composed::spec::contract::end_to_end_arrival(s, tid),
{
  end_to_end_liveness_env_N_trace_holds();
  env_precondition_satisfiable();
}

// Non-vacuity witness: empty logs + committed schedule [tid]. Delivers tid to every
// successor's first pop, so end_to_end_arrival holds WITH !trigger (tid not popped yet).
pub open spec fn arrival_witness(tid: TaskId) -> ComposedState {
  ComposedState {
    executor_log: Seq::empty(),
    reactor_log: Seq::empty(),
    task_logs: Map::empty(),
    injection_schedule: seq![crate::executor::spec::types::TaskView { id: tid }],
  }
}

// Every progress successor of the witness delivers tid (its first pop), so
// task_delivered_next_tick holds even though tid is not yet popped in the witness.
// NON-VACUITY: this ∀ over composed_progress successors is NOT vacuous — the successor set
// is exhibited by bs1_composed_progress (inhabitation_goal_wake.rs), which proves
// composed_progress(arrival_witness(tid), bs1(tid)) for a real pop+poll tick delivering tid.
pub proof fn witness_arrival_holds(tid: TaskId)
  ensures
    crate::composed::spec::contract::end_to_end_arrival(arrival_witness(tid), tid),
{
  let w = arrival_witness(tid);
  assert forall |s2: ComposedState|
    #[trigger] crate::composed::spec::progress::composed_progress(w, s2)
    implies crate::composed::spec::contract::task_spawned_in(s2.executor_log, tid) by {
    reveal(crate::composed::spec::progress::composed_progress);
    // 1 pop happened
    crate::executor::proof::bounded_injection_poll::single_progress_has_pop(
      w.executor_log, s2.executor_log);
    // schedule fixed = [tid]
    assert(s2.injection_schedule == w.injection_schedule);
    let inj = crate::executor::spec::injection_schedule::injected_tasks(s2.executor_log);
    // pops_deliver_schedule (schedule len 1 > 0) gives prefix + (pops>=1 => injected>=1)
    assert(inj.len() >= 1);
    assert(crate::executor::spec::injection_schedule::is_task_prefix(inj, w.injection_schedule));
    assert(inj[0] == w.injection_schedule[0]);
    assert(inj[0].id == tid);
    injected_is_spawned(s2.executor_log, 0);
  }
}

// Any task the schedule-model reports as delivered (in injected_tasks) was in fact
// produced by a Some-yielding PopInjection event, i.e. it is `task_spawned_in`.
pub proof fn injected_is_spawned(l: executor_log::Log, i: int)
  requires
    0 <= i < crate::executor::spec::injection_schedule::injected_tasks(l).len(),
  ensures
    crate::composed::spec::contract::task_spawned_in(
      l, crate::executor::spec::injection_schedule::injected_tasks(l)[i].id),
  decreases l.len(),
{
  let inj = crate::executor::spec::injection_schedule::injected_tasks(l);
  let sub = l.subrange(0, (l.len() - 1) as int);
  let last = l[(l.len() - 1) as int];
  let subinj = crate::executor::spec::injection_schedule::injected_tasks(sub);
  if crate::executor::spec::events::is_pop_injection(last)
    && crate::executor::spec::events::get_pop_injection_task(last).is_some() {
    if i < subinj.len() {
      injected_is_spawned(sub, i);
      // task_spawned_in(sub, ..) => task_spawned_in(l, ..): sub is a prefix of l
      let j: int = choose |j: int| 0 <= j < sub.len()
        && crate::executor::spec::log::is_pop_injection_at(sub, j)
        && crate::executor::spec::events::get_pop_injection_task(sub[j]).is_some()
        && crate::executor::spec::events::get_pop_injection_task(sub[j]).unwrap().id == inj[i].id;
      assert(l[j] == sub[j]);
    } else {
      // i is the last delivered task = `last`, at position l.len()-1
      assert(crate::executor::spec::log::is_pop_injection_at(l, (l.len() - 1) as int));
      assert(crate::executor::spec::events::get_pop_injection_task(
        l[(l.len() - 1) as int]).unwrap().id == inj[i].id);
    }
  } else {
    injected_is_spawned(sub, i);
    let j: int = choose |j: int| 0 <= j < sub.len()
      && crate::executor::spec::log::is_pop_injection_at(sub, j)
      && crate::executor::spec::events::get_pop_injection_task(sub[j]).is_some()
      && crate::executor::spec::events::get_pop_injection_task(sub[j]).unwrap().id == inj[i].id;
    assert(l[j] == sub[j]);
  }
}

pub open spec fn env_holds_at_state_core(s: ComposedState, tid: TaskId) -> bool {
  timestamps_strictly_increasing(s.reactor_log) &&
  crate::reactor::timestamps_positive(s.reactor_log) &&
  timer_deadline_gap_bounded(s, tid) &&
  timer_resources_remain_active(s) &&
  queue_length_bounded(s) &&
  // DOCUMENTATION CONJUNCT (audit): tid_unique is consumed by no
  // derivation lemma — it mirrors the ledger-enforced pop-uniqueness the impl
  // proves, keeps the executor contracts' assumption_fn meaningful, and excludes
  // no real trace. Retained deliberately; every witness discharges it.
  executor_log::tid_unique(s.executor_log, tid) &&
  // t4b: contract_timer_assumption_here (leftmost find_register, reuse-EXCLUDING) removed
  // from env core — it was consumed only by now-deleted rid-keyed helpers, and the
  // timer resource-hold is carried by the reuse-tolerant timer_resources_remain_active.
  // (audit: pop_follows_schedule removed too — discharged everywhere,
  // consumed nowhere; delivery derivations use composed_progress's
  // pops_deliver_schedule instead. Removal strictly enlarges the theorem domain.)
  contract_io_assumption_here(s)
}

// ----------------------------------------------------------------------------
// The satisfiable core holds on the empty state.
// ----------------------------------------------------------------------------
#[verifier::rlimit(50)]
pub proof fn env_core_holds_empty_logs(s: ComposedState, tid: TaskId)
  requires
    s.executor_log =~= Seq::empty(),
    s.reactor_log =~= Seq::empty(),
    s.task_logs =~= Map::empty(),
  ensures
    env_holds_at_state_core(s, tid),
{
  assert(timestamps_strictly_increasing(s.reactor_log));
  assert(crate::reactor::timestamps_positive(s.reactor_log));
  assert(timer_deadline_gap_bounded(s, tid)) by { reveal(timer_deadline_gap_bounded); }

  assert(timer_resources_remain_active(s));

  assert(queue_length_bounded(s)) by {
    assert(crate::executor::invariants::fifo_task_selection::fifo_queue_at(s.executor_log, 0)
      =~= Seq::empty());
  }

  assert(executor_log::tid_unique(s.executor_log, tid));

  assert(contract_io_assumption_here(s)) by {
    assert forall |rid: ResourceIdView| io_assumption_here(s.reactor_log, rid) by {
      assert(crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(
        s.reactor_log, rid));
    }
  }
}

pub open spec fn end_to_end_env(s: ComposedState, tid: TaskId) -> bool {
  env_holds_at_state_core(s, tid)
}

// Parameterized filter carrying a UNIFORM poll bound `cap`. The uniform-bound
// obstacle (TODO): a not-yet-ready task needs a fixed bound N chosen before the
// reached state; a per-state ∃n poll-bound clause (since deleted) is
// retrospective (count(s) < N ⇒ vacuous), so it loses the forward-looking-ness.
// env_N fixes `cap`; requiring env_N at EVERY trace state (an env_N-good trace)
// recovers "count(l') ≥ cap ⇒ ready(l')" uniformly along the trace — exactly
// what the deleted forall-extension form provided, but over a satisfiable
// (per-trace) domain. Only the two genuinely bound-carrying clauses need `cap`
// (poll count here; queue bound to be added); clock/resource clauses are
// prefix-closed and stay in end_to_end_env.
// WAKE-DELIVERY assumption, window-scoped (P4b option (a)).
//
// A task blocked on a FIRED-and-not-yet-consumed wakeup source is in the
// runnable queue. Compared to the previous form this antecedent is scoped:
//   - "unconsumed": the task's LAST executor poll is Pending (a re-poll closes
//     the window, so post-consumption states are no longer constrained — this
//     kills the monotone-antecedent disease);
//   - timer/io "fired": a WakeTask for rid with NO later same-rid
//     re-registration (timer) / re-SetWaker (io) — i.e. the wake belongs to
//     the CURRENT registration window, and an armed-but-unfired source imposes
//     nothing (this kills the instantaneous-delivery disease: waiting states
//     are env-legal);
//   - defer: the Defer op itself is the fire (delivery within the same tick —
//     matches the executor's drain-in-tick behavior);
//   - pass-waker: the fire is the PassWaker registration itself. Gating on the
//     kernel's Woken event would additionally require a (currently absent)
//     kernel-liveness assumption — see the pass_waker TEMPLATE-ONLY note.
// Delivery itself (fired ⇒ queued) remains the environment's obligation, per
// the paper's compositional design; for timer/io it is realizable from the
// modeled reactor (wake fires in park, DrainReactorWake follows in-tick).
// Window anchoring mirrors the module machinery: timer at the canonical
// (leftmost) registration find_register_timer_idx — under rid reuse this is the
// same scope limitation as the reactor's leftmost-anchored timer proofs (the
// documented io_syscall_active_at_set_waker/F3 item); io at the LAST SuccSetWaker,
// which is genuinely re-arm safe (a re-SetWaker moves the anchor forward and
// closes the old window).
// io_wake_in_current_window moved to composed::spec::wake_queues (Phase B, io
// increment): it is the io disjunct of the reactor-wake queue's arrival predicate,
// and lives in the spec module to avoid a spec→proof module cycle.
pub use crate::composed::spec::wake_queues::io_wake_in_current_window;

// timer_wake_owned moved to composed::spec::wake_queues (Phase B): it is the timer
// disjunct of the reactor-wake queue's arrival predicate, and lives in the spec
// module to avoid a spec→proof module cycle (wake_queues references it).
pub use crate::composed::spec::wake_queues::timer_wake_owned;

// Phase B discharge helper: if s's reactor log has no WakeTask event, then no task
// is in the (derived) reactor-wake queue at s (the arrival predicate needs a fired
// WakeTask via response_at). Used to prove reactor_wake_drain_step vacuously in the
// concrete-trace inhabitation witnesses (whose step-start reactor logs contain no
// fired WakeTask — the wake witness's WakeTask fires WITHIN the step, so at its start
// state the queue is empty and the same-tick drain is unconstrained by the step).
pub proof fn no_reactor_wake_pending_no_waketask(s: ComposedState)
  requires
    forall |w: int| 0 <= w < s.reactor_log.len() ==> !reactor_log::is_wake_task_at(s.reactor_log, w),
  ensures
    forall |tid2: TaskId| !crate::composed::spec::wake_queues::reactor_wake_pending(s, tid2),
{
  reveal(crate::composed::spec::wake_queues::reactor_wake_pending);
  reveal(crate::composed::spec::wake_queues::reactor_wake_arrival);
  // timer disjunct false: response_at needs a WakeTask, none exists
  assert forall |i: int|
    #![trigger crate::reactor::contracts::bounded_timer_wakeup::response_at(s.reactor_log, i)]
    !crate::reactor::contracts::bounded_timer_wakeup::response_at(s.reactor_log, i) by {
  }
  // io disjunct false: io_wake_in_current_window needs a WakeTask, none exists
  assert forall |rid: ResourceIdView|
    #![trigger crate::composed::spec::wake_queues::io_wake_in_current_window(s.reactor_log, rid)]
    !crate::composed::spec::wake_queues::io_wake_in_current_window(s.reactor_log, rid) by {
  }
  assert forall |tid2: TaskId| !crate::composed::spec::wake_queues::reactor_wake_pending(s, tid2) by {
    assert(!timer_wake_owned(s, tid2));
  }
}

// Phase C discharge helper (task-wake analog): if no task log in s has a Woken event,
// then no task is in the (derived) task-wake queue at s. Used to prove taskwake_drain_step
// vacuously in the inhabitation witnesses (whose task logs contain no Woken op).
pub proof fn no_taskwake_pending_no_woken(s: ComposedState)
  requires
    forall |tid2: TaskId| #[trigger] s.task_logs.contains_key(tid2) ==>
      (forall |j: int| 0 <= j < s.task_logs[tid2].len() ==>
        !crate::utilities::spec::events::is_woken(s.task_logs[tid2][j])),
  ensures
    forall |tid2: TaskId| !crate::composed::spec::wake_queues::taskwake_pending(s, tid2),
{
  reveal(crate::composed::spec::wake_queues::taskwake_pending);
  reveal(crate::composed::spec::wake_queues::taskwake_arrival);
  assert forall |tid2: TaskId| !crate::composed::spec::wake_queues::taskwake_pending(s, tid2) by {
    if s.task_logs.contains_key(tid2) {
      let last2 = (s.task_logs[tid2].len() - 1) as int;
      assert(!crate::utilities::spec::log::has_woken_in_current_poll(s.task_logs[tid2], last2)) by {
        assert forall |j: int| #![trigger s.task_logs[tid2][j]]
          0 <= j < s.task_logs[tid2].len() implies
          !crate::utilities::spec::events::is_woken(s.task_logs[tid2][j]) by {
        }
      }
    }
  }
}

// RETIRED (Phase D): wake_fired_unconsumed / wake_delivers_here were the free per-state
// delivery assumption for the four wake queues. All four are now MODELED / DERIVED —
// timer + io via the reactor-wake queue (Phase B), deferred via the deferred queue
// (Phase A), and pass_waker via the BOUNDED external-arrival clause taskwake_arrival_within
// (Phase C) — so wake_fired_unconsumed ≡ false and wake_delivers_here ≡ true. Both are
// deleted; the only surviving delivery-side assumptions are the genuinely external
// arrivals (injection's ghost schedule, TaskWake's bounded clause below).

// Bounded external-arrival clause for the TaskWake queue (wake-routing Phase C),
// drain-membership form . Unlike timer/io — whose fire event is DERIVABLE
// from the reactor kernel — a TaskWake is caused by an EXTERNAL entity (another
// task/utility), and lion-liveness has no utility kernel to derive the fire from. So
// the ARRIVAL is legitimately ASSUMED (same KIND as injection's "task is spawned"),
// but BOUNDED and HONEST — and structured like the other queues: the cross-task wake
// is assumed to LAND (arrival fused with drain MEMBERSHIP — a parked arrival has no
// observable of its own, see wake_queues.rs taskwake_pending note); the drain's
// EXISTENCE is proven (single_progress_has_drain_task_wake) and Drain→FIFO→poll is
// derived. Concretely: a task that (a) registered a PassWaker in its current poll,
// (b) whose last poll is still Pending, is CONTAINED in any Drain{TaskWake} that
// occurs after >= n scheduler ticks of waiting — but only until delivered: the
// !taskwake_drained_in guard (open interval (last_poll, d), EXCLUDING d) keeps this
// satisfiable on real traces, since once the first post-window drain carries tid,
// every later d is exempt. A never-woken task makes the antecedent hold (at the first
// post-window drain) WITHOUT the consequent ⟹ that trace is pruned from env_N's
// domain — exactly as io_ready_forward_here prunes never-ready resources. Opaque to
// bound SMT (reveal at the use sites).
#[verifier::opaque]
pub open spec fn taskwake_arrival_within(s: ComposedState, tid: TaskId, n: nat) -> bool {
  forall |d: int|
    #![trigger s.executor_log[d]]
    {
      let last_poll = executor_log::last_poll_idx_for_id(s.executor_log, tid);
      (s.task_logs.contains_key(tid) &&
       crate::utilities::spec::log::has_pass_waker_in_current_poll(
         s.task_logs[tid], (s.task_logs[tid].len() - 1) as int) &&
       executor_log::last_poll_is_pending(s.executor_log, tid) &&
       last_poll < d < s.executor_log.len() &&
       executor_log::is_drain_task_wake_at(s.executor_log, d) &&
       !crate::composed::spec::wake_queues::taskwake_drained_in(
         s.executor_log, tid, last_poll, d) &&
       executor_log::count_tick_ends_between(s.executor_log, last_poll, d) >= n)
      ==> executor_log::task_id_in_drain_at(s.executor_log, d, tid)
    }
}

// The TaskWake arrival clause is VACUOUSLY true when tid has no PassWaker in its current
// poll (or is absent) — the antecedent's has_pass_waker conjunct fails. Every env_N
// witness (b*/g*/spawn) is in this case, so it discharges the clause via this helper.
pub proof fn taskwake_arrival_within_vacuous(s: ComposedState, tid: TaskId, n: nat)
  requires
    !s.task_logs.contains_key(tid) ||
    !crate::utilities::spec::log::has_pass_waker_in_current_poll(
      s.task_logs[tid], (s.task_logs[tid].len() - 1) as int) ||
    !executor_log::last_poll_is_pending(s.executor_log, tid),
  ensures
    taskwake_arrival_within(s, tid, n),
{
  reveal(taskwake_arrival_within);
}


pub open spec fn env_N(s: ComposedState, tid: TaskId, cap: nat) -> bool {
  end_to_end_env(s, tid) &&
  bounded_poll_count_here_with_bound(s, tid, cap) &&
  // io readiness carries its OWN environment bound (get_io_ready_bound), decoupled
  // from the task-completion bound cap.
  (forall |rid: ResourceIdView|
    #[trigger] io_ready_forward_here(s.reactor_log, rid, get_io_ready_bound(s, tid))) &&
  taskwake_arrival_within(s, tid, cap)
}

// env_N is strictly stronger than end_to_end_env, so an env_N-good trace is in
// particular an env-good trace — env_N reuses all existing end_to_end_env
// machinery, only adding the uniform poll bound. (Queue needs no cap: its bound
// get_max_queue_length is arbitrary() — a state-independent constant — so
// queue_length_bounded already gives a uniform bound; only the poll-count
// bound was a per-state existential, hence the single `cap`.)
pub proof fn env_N_implies_env(s: ComposedState, tid: TaskId, cap: nat)
  requires
    env_N(s, tid, cap),
  ensures
    end_to_end_env(s, tid),
{
}

// env_N is satisfiable: reuse the end_to_end_env witness and pick cap above its
// current poll count, so the poll-bound implication is vacuously true.
pub proof fn env_N_satisfiable()
  ensures
    exists |s: ComposedState, tid: TaskId, cap: nat| #[trigger] env_N(s, tid, cap),
{
  let tid: TaskId = arbitrary();
  env_core_holds_empty_logs(empty_composed_state(), tid);
  let s = crate::composed::spec::state::empty_composed_state();
  assert(end_to_end_env(s, tid));
  let cap: nat = 1nat;
  assert(count_polls_for_tid(s.executor_log, tid) == 0);
  assert(bounded_poll_count_here_with_bound(s, tid, cap));
  assert forall |rid: ResourceIdView|
    #[trigger] io_ready_forward_here(s.reactor_log, rid, get_io_ready_bound(s, tid)) by {
    assert(s.reactor_log.len() == 0);
    assert(crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      s.reactor_log, rid, s.reactor_log.len() as int) == -1);
  };
  assert(!s.task_logs.contains_key(tid));
  taskwake_arrival_within_vacuous(s, tid, cap);
  assert(env_N(s, tid, cap));
}

pub open spec fn ete_trace_reachable(s: ComposedState, l2: ComposedState, n: nat, tid: TaskId) -> bool {
  crate::framework::module_spec::env_progress_n(
    crate::composed::spec::progress::composed_module_spec().progress,
    s, l2, n,
    |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2),
    tid,
  )
}

// env_N-good trace (fixed uniform bound cap). An env_N-good trace is in
// particular an env-good ete_trace_reachable, so all env machinery applies AND
// the uniform poll bound cap holds at every state (via env_N).
pub open spec fn ete_reachable_N(s: ComposedState, l2: ComposedState, n: nat, cap: nat, tid: TaskId) -> bool {
  crate::framework::module_spec::env_progress_n(
    crate::composed::spec::progress::composed_module_spec().progress,
    s, l2, n,
    |s2: ComposedState, tid2: TaskId| env_N(s2, tid2, cap),
    tid,
  )
}

// At the endpoint of an env_N-good trace, env_N holds with the SAME fixed cap —
// so the scheduling proof has BOTH uniform bounds at the reached state:
// bounded_poll_count_here_with_bound(l', tid, cap) (poll, uniform via cap) and,
// via env_N ⟹ end_to_end_env, queue_length_bounded(l') (queue, uniform via the
// state-independent get_max_queue_length constant). This is the clean uniform-
// bound interface the re-plumbed scheduling consumes at the endpoint.
// Composed split: an env_N-good (n1+n2)-trace to l' passes through some l_mid at
// n1 steps, with env_N-good sub-traces s→l_mid (n1) and l_mid→l' (n2). This is
// how the wake loop reaches the wake point l_mid then drains to l'.
pub proof fn ete_reachable_N_split(s: ComposedState, l_prime: ComposedState, n1: nat, n2: nat, cap: nat, tid: TaskId)
  requires
    ete_reachable_N(s, l_prime, (n1 + n2) as nat, cap, tid),
  ensures
    exists |l_mid: ComposedState|
      #[trigger] ete_reachable_N(s, l_mid, n1, cap, tid)
      && ete_reachable_N(l_mid, l_prime, n2, cap, tid),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| env_N(s2, tid2, cap);
  assert(ete_reachable_N(s, l_prime, (n1 + n2) as nat, cap, tid));
  assert(crate::framework::module_spec::env_progress_n(progress, s, l_prime, (n1 + n2) as nat, env, tid));
  crate::framework::module_spec::env_progress_n_split(progress, s, l_prime, n1, n2, env, tid);
  let l_mid: ComposedState = choose |l_mid: ComposedState|
    crate::framework::module_spec::env_progress_n(progress, s, l_mid, n1, env, tid)
    && crate::framework::module_spec::env_progress_n(progress, l_mid, l_prime, n2, env, tid);
  assert(ete_reachable_N(s, l_mid, n1, cap, tid));
  assert(ete_reachable_N(l_mid, l_prime, n2, cap, tid));
}

#[verifier::rlimit(50)]
pub proof fn ete_reachable_one_step(s: ComposedState, s1: ComposedState, cap: nat, tid: TaskId)
  requires
    ete_reachable_N(s, s1, 1, cap, tid),
  ensures
    crate::framework::module_spec::progress_n(
      crate::composed::spec::progress::composed_module_spec().progress, s, s1, 1),
    crate::composed::spec::progress::composed_progress(s, s1),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| env_N(s2, tid2, cap);
  assert(crate::framework::module_spec::env_progress_n(progress, s, s1, 1, env, tid));
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, s1, 1, env, tid);
  let tr: Seq<ComposedState> = choose |tr: Seq<ComposedState>|
    #![trigger tr.len()]
    tr.len() == 2 && tr.first() == s && tr.last() == s1 &&
    crate::framework::module_spec::is_valid_trace(progress, tr);
  assert((progress)(tr[0], tr[1]));
  assert(tr[0] == s && tr[1] == s1);
}

// Tick-end growth at the ete_reachable_N level (wake-routing Phase C): after
// n env_N-good steps, at least n scheduler ticks have elapsed since any fixed earlier
// point K <= s.executor_log.len(). This is the arrival clock the bounded TaskWake
// clause taskwake_arrival_within reads — the honest "waited n ticks" measure.
pub proof fn ete_reachable_N_grows_tick_ends(
  s: ComposedState, l_wake: ComposedState, n: nat, cap: nat, tid: TaskId, k: int,
)
  requires
    ete_reachable_N(s, l_wake, n, cap, tid),
    0 <= k <= s.executor_log.len(),
  ensures
    executor_log::count_tick_ends_after(l_wake.executor_log, k) >= n,
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| env_N(s2, tid2, cap);
  assert(crate::framework::module_spec::env_progress_n(progress, s, l_wake, n, env, tid));
  let trace: Seq<ComposedState> = choose |trace: Seq<ComposedState>|
    trace.len() == n + 1 && trace.first() == s && trace.last() == l_wake
    && crate::framework::module_spec::is_valid_trace(progress, trace)
    && crate::framework::module_spec::env_holds_along(progress, trace, env, tid);
  assert(trace[0] == s);
  assert(trace[n as int] == l_wake);
  crate::composed::proof::end_to_end::progress_n_has_n_tick_ends(trace, n);
  let base = s.executor_log.len() as int;
  let end = l_wake.executor_log.len() as int;
  assert(executor_log::count_tick_ends_between(l_wake.executor_log, base, end) >= n);
  // prefix relation s ⊆ l_wake ⟹ base <= end, so additivity keeps the [k, base) prefix
  ete_reachable_N_implies_env(s, l_wake, n, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_wake, n, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_wake, n);
  assert(base <= end);
  crate::executor::proof::bounded_drain_poll::count_tick_ends_additivity_range(
    l_wake.executor_log, k, base, end);
}

pub proof fn ete_reachable_N_gives_env_N_at_end(s: ComposedState, l_prime: ComposedState, n: nat, cap: nat, tid: TaskId)
  requires
    ete_reachable_N(s, l_prime, n, cap, tid),
  ensures
    env_N(l_prime, tid, cap),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| env_N(s2, tid2, cap);
  crate::framework::module_spec::env_progress_n_gives_env_at_end(progress, s, l_prime, n, env, tid);
}

pub proof fn ete_reachable_N_implies_env(s: ComposedState, l2: ComposedState, n: nat, cap: nat, tid: TaskId)
  requires
    ete_reachable_N(s, l2, n, cap, tid),
  ensures
    ete_trace_reachable(s, l2, n, tid),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env_s = |s2: ComposedState, tid2: TaskId| env_N(s2, tid2, cap);
  let env_w = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  assert forall |x: ComposedState| #[trigger] env_s(x, tid) implies env_w(x, tid) by {
    env_N_implies_env(x, tid, cap);
  };
  crate::framework::module_spec::env_progress_n_weaken(progress, s, l2, n, env_s, env_w, tid);
}

pub proof fn trace_reachable_gives_env_at_end(s: ComposedState, l_prime: ComposedState, n: nat, tid: TaskId)
  requires
    ete_trace_reachable(s, l_prime, n, tid),
  ensures
    end_to_end_env(l_prime, tid),
{
  let ms = crate::composed::spec::progress::composed_module_spec();
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  crate::framework::module_spec::env_progress_n_gives_env_at_end(ms.progress, s, l_prime, n, env, tid);
}

// env_N at the trace start (mirrors ete_reachable_N_gives_env_N_at_end).
pub proof fn ete_reachable_N_gives_env_N_at_start(s: ComposedState, l_prime: ComposedState, n: nat, cap: nat, tid: TaskId)
  requires
    ete_reachable_N(s, l_prime, n, cap, tid),
  ensures
    env_N(s, tid, cap),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| env_N(s2, tid2, cap);
  crate::framework::module_spec::env_progress_n_gives_env_at_start(progress, s, l_prime, n, env, tid);
}

// If tid is Pending at s and is NOT polled over the s→l_x segment, then at l_x
// the task log is unchanged and tid's last poll is still Pending — i.e. the
// wakeup is still UNCONSUMED at l_x. This is the executor-side fact the
// window wake-delivery clause (wake_fired_unconsumed) needs at l_wake.
pub proof fn not_polled_preserves_pending(
  s: ComposedState, l_x: ComposedState, n: nat, cap: nat, tid: TaskId,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    ete_reachable_N(s, l_x, n, cap, tid),
    !executor_log::has_poll_task_for_id_after(l_x.executor_log, tid, s.executor_log.len() as int),
  ensures
    l_x.task_logs.contains_key(tid),
    s.task_logs[tid] =~= l_x.task_logs[tid],
    executor_log::last_poll_is_pending(l_x.executor_log, tid),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |c: ComposedState, tt: TaskId| env_N(c, tt, cap);
  ete_reachable_N_implies_env(s, l_x, n, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_x, n, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_x, n);
  assert(crate::executor::spec::log::is_prefix_of(s.executor_log, l_x.executor_log));
  assert(l_x.task_logs.contains_key(tid));
  // task log unchanged: else task_log_growth_implies_poll gives a poll in the
  // new segment, contradicting !has_poll.
  assert(s.task_logs[tid] =~= l_x.task_logs[tid]) by {
    assert(crate::composed::spec::state::is_task_log_prefix(s.task_logs[tid], l_x.task_logs[tid]));
    if s.task_logs[tid].len() < l_x.task_logs[tid].len() {
      let trace: Seq<ComposedState> = choose |trace: Seq<ComposedState>|
        trace.len() == n + 1 && trace.first() == s && trace.last() == l_x &&
        crate::framework::module_spec::is_valid_trace(progress, trace);
      assert(trace[n as int] == l_x);
      assert(n >= 1) by {
        if n == 0 { assert(trace.len() == 1); assert(trace.first() == trace.last()); }
      }
      crate::composed::proof::end_to_end::task_log_growth_implies_poll(trace, tid, n as int);
      let pidx = choose |pidx: int|
        s.executor_log.len() as int <= pidx < l_x.executor_log.len() &&
        crate::executor::spec::log::is_poll_task_for_id_at(l_x.executor_log, pidx, tid);
      assert(executor_log::has_poll_task_for_id_after(l_x.executor_log, tid, s.executor_log.len() as int));
    }
  }
  crate::composed::proof::end_to_end::last_poll_pending_prefix_stable(
    s.executor_log, l_x.executor_log, tid);
}

// DEFER: DERIVED from the modeled Deferred queue (wake-routing Phase A),
// replacing the free wake_delivers_here defer disjunct. A task whose current poll
// deferred (has_defer_in_current_poll) is in the Deferred queue; the modeled
// deferred_drain_step (in composed_progress) takes it in the next tick's
// Drain{Deferred} (which tick_has_drain_deferred / single_progress_has_drain_deferred
// guarantees exists); drain_adds_tid_to_queue puts it in the runnable FIFO;
// queue_member_eventually_polled_on_trace drains it to a poll. Two cases: the
// deferred task is either already drained into the FIFO (Case A) or still waiting
// in the deferred queue, delivered by the first step (Case B). Assumption-free.
pub proof fn composed_defer_pending_to_poll(
  s: ComposedState, l_prime: ComposedState, chunk: nat, cap: nat, tid: TaskId,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    crate::utilities::spec::log::has_defer_in_current_poll(
      s.task_logs[tid], (s.task_logs[tid].len() - 1) as int),
    forall |j: int|
      executor_log::last_poll_idx_for_id(s.executor_log, tid) < j < s.executor_log.len() ==>
      !crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, j, tid),
    ete_reachable_N(s, l_prime, chunk, cap, tid),
    chunk > get_max_queue_length(s) + 1,
    cap >= 1,
    0 < s.executor_log.len(),
  ensures
    executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int),
{
  let lpi = executor_log::last_poll_idx_for_id(s.executor_log, tid);
  if crate::composed::spec::wake_queues::deferred_drained_after(s.executor_log, tid, lpi) {
    // ---- Case A: already drained into the runnable FIFO before s ----
    let d: int = choose |d: int|
      lpi < d < s.executor_log.len() &&
      executor_log::is_drain_deferred_at(s.executor_log, d) &&
      executor_log::task_id_in_drain_at(s.executor_log, d, tid);
    assert(executor_log::is_drain_at(s.executor_log, d));
    crate::composed::proof::end_to_end::drain_adds_tid_to_queue(s.executor_log, tid, d);
    crate::composed::proof::end_to_end::tid_survives_or_polled_in_range(
      s.executor_log, tid, d + 1, s.executor_log.len() as int);
    if exists |pidx: int| d + 1 <= pidx < s.executor_log.len()
      && crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, pidx, tid) {
      let pidx: int = choose |pidx: int| d + 1 <= pidx < s.executor_log.len()
        && crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, pidx, tid);
      assert(lpi < pidx < s.executor_log.len());
      assert(false);
    }
    assert(crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
      s.executor_log, s.executor_log.len() as int, tid));
    queue_member_eventually_polled_on_trace(s, l_prime, chunk, cap, tid);
  } else {
    // ---- Case B: still in the deferred queue → first step's Drain{Deferred} ----
    assert(crate::composed::spec::wake_queues::in_deferred_queue(s, tid));
    let progress = crate::composed::spec::progress::composed_module_spec().progress;
    let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
    ete_reachable_N_split(s, l_prime, 1, (chunk - 1) as nat, cap, tid);
    let s1: ComposedState = choose |s1: ComposedState|
      ete_reachable_N(s, s1, 1, cap, tid) && ete_reachable_N(s1, l_prime, (chunk - 1) as nat, cap, tid);
    ete_reachable_one_step(s, s1, cap, tid);
    reveal(crate::composed::spec::progress::composed_progress);
    // s1's tick has a Drain{Deferred} at d in the new content
    crate::executor::proof::bounded_drain_poll::single_progress_has_drain_deferred(
      s.executor_log, s1.executor_log);
    let d: int = choose |d: int|
      s.executor_log.len() as int <= d < s1.executor_log.len()
      && executor_log::is_drain_deferred_at(s1.executor_log, d);
    // the modeled deferred routing takes tid in that drain
    assert(executor_log::task_id_in_drain_at(s1.executor_log, d, tid));
    assert(executor_log::is_drain_at(s1.executor_log, d));
    crate::composed::proof::end_to_end::drain_adds_tid_to_queue(s1.executor_log, tid, d);
    let enter_idx: int = d + 1;
    crate::composed::proof::end_to_end::progress_n_preserves_wf(s, s1, 1);
    crate::composed::proof::end_to_end::tid_survives_or_polled_in_range(
      s1.executor_log, tid, enter_idx, s1.executor_log.len() as int);
    if exists |pidx: int| enter_idx <= pidx < s1.executor_log.len()
      && crate::executor::spec::log::is_poll_task_for_id_at(s1.executor_log, pidx, tid) {
      let pidx: int = choose |pidx: int| enter_idx <= pidx < s1.executor_log.len()
        && crate::executor::spec::log::is_poll_task_for_id_at(s1.executor_log, pidx, tid);
      ete_reachable_N_implies_env(s1, l_prime, (chunk - 1) as nat, cap, tid);
      crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s1, l_prime, (chunk - 1) as nat, env, tid);
      crate::composed::proof::end_to_end::progress_n_implies_extension(s1, l_prime, (chunk - 1) as nat);
      assert(crate::executor::spec::log::is_prefix_of(s1.executor_log, l_prime.executor_log));
      assert(s1.executor_log[pidx] == l_prime.executor_log[pidx]);
    } else {
      assert(crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
        s1.executor_log, s1.executor_log.len() as int, tid));
      assert(0 < s1.executor_log.len());
      assert(get_max_queue_length(s1) == get_max_queue_length(s));
      queue_member_eventually_polled_on_trace(s1, l_prime, (chunk - 1) as nat, cap, tid);
    }
  }
}

// REACTOR-WAKE: DERIVED from the modeled ReactorWake queue (wake-routing
// Phase B), replacing the free wake_delivers_here timer/io disjuncts. A task whose
// owned WakeTask has fired (reactor_wake_arrival) is in the ReactorWake queue; the
// modeled reactor_wake_drain_step (in composed_progress) takes it in the next tick's
// Drain{ReactorWake} (which single_progress_has_drain_reactor_wake guarantees exists);
// drain_adds_tid_to_queue puts it in the runnable FIFO; queue_member_eventually_
// polled_on_trace drains it to a poll. Structurally identical to
// composed_defer_pending_to_poll (Case A already drained / Case B first step's drain),
// only the queue predicate and drain source differ. Assumption-free (the WakeTask
// itself is established upstream by the timer/io reactor contract).
pub proof fn composed_reactor_wake_pending_to_poll(
  s: ComposedState, l_prime: ComposedState, chunk: nat, cap: nat, tid: TaskId,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    crate::composed::spec::wake_queues::reactor_wake_arrival(s, tid),
    forall |j: int|
      executor_log::last_poll_idx_for_id(s.executor_log, tid) < j < s.executor_log.len() ==>
      !crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, j, tid),
    ete_reachable_N(s, l_prime, chunk, cap, tid),
    chunk > get_max_queue_length(s) + 1,
    cap >= 1,
    0 < s.executor_log.len(),
  ensures
    executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int),
{
  let lpi = executor_log::last_poll_idx_for_id(s.executor_log, tid);
  if crate::composed::spec::wake_queues::reactor_wake_drained_after(s.executor_log, tid, lpi) {
    // ---- Case A: already drained into the runnable FIFO before s ----
    let d: int = choose |d: int|
      lpi < d < s.executor_log.len() &&
      executor_log::is_drain_reactor_wake_at(s.executor_log, d) &&
      executor_log::task_id_in_drain_at(s.executor_log, d, tid);
    assert(executor_log::is_drain_at(s.executor_log, d));
    crate::composed::proof::end_to_end::drain_adds_tid_to_queue(s.executor_log, tid, d);
    crate::composed::proof::end_to_end::tid_survives_or_polled_in_range(
      s.executor_log, tid, d + 1, s.executor_log.len() as int);
    if exists |pidx: int| d + 1 <= pidx < s.executor_log.len()
      && crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, pidx, tid) {
      let pidx: int = choose |pidx: int| d + 1 <= pidx < s.executor_log.len()
        && crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, pidx, tid);
      assert(lpi < pidx < s.executor_log.len());
      assert(false);
    }
    assert(crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
      s.executor_log, s.executor_log.len() as int, tid));
    queue_member_eventually_polled_on_trace(s, l_prime, chunk, cap, tid);
  } else {
    // ---- Case B: still in the reactor-wake queue → first step's Drain{ReactorWake} ----
    assert(crate::composed::spec::wake_queues::reactor_wake_pending(s, tid)) by {
      reveal(crate::composed::spec::wake_queues::reactor_wake_pending);
    }
    let progress = crate::composed::spec::progress::composed_module_spec().progress;
    let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
    ete_reachable_N_split(s, l_prime, 1, (chunk - 1) as nat, cap, tid);
    let s1: ComposedState = choose |s1: ComposedState|
      ete_reachable_N(s, s1, 1, cap, tid) && ete_reachable_N(s1, l_prime, (chunk - 1) as nat, cap, tid);
    ete_reachable_one_step(s, s1, cap, tid);
    reveal(crate::composed::spec::progress::composed_progress);
    // s1's tick has a Drain{ReactorWake} at d in the new content
    crate::executor::proof::bounded_drain_poll::single_progress_has_drain_reactor_wake(
      s.executor_log, s1.executor_log);
    let d: int = choose |d: int|
      s.executor_log.len() as int <= d < s1.executor_log.len()
      && executor_log::is_drain_reactor_wake_at(s1.executor_log, d);
    // the modeled reactor-wake routing takes tid in that drain
    assert(executor_log::task_id_in_drain_at(s1.executor_log, d, tid)) by {
      reveal(crate::composed::spec::wake_queues::reactor_wake_drain_step);
    }
    assert(executor_log::is_drain_at(s1.executor_log, d));
    crate::composed::proof::end_to_end::drain_adds_tid_to_queue(s1.executor_log, tid, d);
    let enter_idx: int = d + 1;
    crate::composed::proof::end_to_end::progress_n_preserves_wf(s, s1, 1);
    crate::composed::proof::end_to_end::tid_survives_or_polled_in_range(
      s1.executor_log, tid, enter_idx, s1.executor_log.len() as int);
    if exists |pidx: int| enter_idx <= pidx < s1.executor_log.len()
      && crate::executor::spec::log::is_poll_task_for_id_at(s1.executor_log, pidx, tid) {
      let pidx: int = choose |pidx: int| enter_idx <= pidx < s1.executor_log.len()
        && crate::executor::spec::log::is_poll_task_for_id_at(s1.executor_log, pidx, tid);
      ete_reachable_N_implies_env(s1, l_prime, (chunk - 1) as nat, cap, tid);
      crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s1, l_prime, (chunk - 1) as nat, env, tid);
      crate::composed::proof::end_to_end::progress_n_implies_extension(s1, l_prime, (chunk - 1) as nat);
      assert(crate::executor::spec::log::is_prefix_of(s1.executor_log, l_prime.executor_log));
      assert(s1.executor_log[pidx] == l_prime.executor_log[pidx]);
    } else {
      assert(crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
        s1.executor_log, s1.executor_log.len() as int, tid));
      assert(0 < s1.executor_log.len());
      assert(get_max_queue_length(s1) == get_max_queue_length(s));
      queue_member_eventually_polled_on_trace(s1, l_prime, (chunk - 1) as nat, cap, tid);
    }
  }
}


// DISPATCHED pending → tid POLLED: the timer case is DERIVED from the modeled
// reactor (composed_timer_pending_to_poll, which consumes env_timer_wake_general_at
// ⊆ reactor timer liveness); io is likewise derived (io_ready_forward_here is the
// env readiness clause, delivery is fire→drain→FIFO→poll); defer/pass-waker rest
// on the taskwake arrival clause (the utility kernel is unmodeled).
// chunk > K + B + cap + C + 1 with K = get_max_timer_deadline_gap
// (uniform), B = get_io_ready_bound (uniform io readiness bound, decoupled from
// cap), C = get_max_queue_length (uniform) — a state-independent chunk size.
pub proof fn composed_pending_to_poll_derived(
  s: ComposedState, l_prime: ComposedState, chunk: nat, cap: nat, tid: TaskId, pending_idx: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    crate::composed::spec::assumptions::is_task_pending_at(s, tid, pending_idx),
    forall |j: int| pending_idx < j < s.executor_log.len() ==>
      !crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, j, tid),
    ete_reachable_N(s, l_prime, chunk, cap, tid),
    chunk > get_max_timer_deadline_gap(s, tid) + get_io_ready_bound(s, tid)
      + cap + get_max_queue_length(s) + 1,
    cap >= 1,
  ensures
    executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int),
{
  let last: int = (s.task_logs[tid].len() - 1) as int;
  crate::composed::proof::end_to_end::pending_has_wakeup_source(s, tid, pending_idx);
  ete_reachable_N_gives_env_N_at_start(s, l_prime, chunk, cap, tid);
  env_N_implies_env(s, tid, cap);
  env_gives_core_clauses(s, tid);
  // last poll of tid is Pending (pending_idx is the last poll, and it is Pending)
  assert(executor_log::last_poll_is_pending(s.executor_log, tid)) by {
    assert(executor_log::is_poll_pending_for_id_at(s.executor_log, pending_idx, tid));
    assert(executor_log::has_poll_for_id(s.executor_log, tid));
    crate::composed::proof::end_to_end::last_poll_idx_properties(s.executor_log, tid);
    let q = executor_log::last_poll_idx_for_id(s.executor_log, tid);
    assert(q == pending_idx) by {
      if q > pending_idx {
        assert(executor_log::is_poll_task_for_id_at(s.executor_log, q, tid));
      } else if q < pending_idx {
        assert(executor_log::is_poll_task_for_id_at(s.executor_log, pending_idx, tid));
      }
    }
  }
  if crate::utilities::spec::log::has_active_timer_with_waker(s.task_logs[tid], last) {
    // ---- TIMER: DERIVED by CONSUMING the reactor's env-form timer CONTRACT ----
    let rid: ResourceIdView = choose |rid: ResourceIdView|
      crate::utilities::spec::log::has_timer_registered_in_current_poll(s.task_logs[tid], rid, last);
    composed_timer_pending_to_poll_via_contract(s, l_prime, chunk, cap, tid, rid);
  } else if crate::utilities::spec::log::has_active_io_with_waker(s.task_logs[tid], last) {
    // ---- IO: DERIVED by CONSUMING the reactor's env-form io CONTRACT ----
    let rid: crate::reactor::spec::types::ResourceIdView = choose |rid: crate::reactor::spec::types::ResourceIdView|
      crate::utilities::spec::log::is_io_active(s.task_logs[tid], rid, last) &&
      crate::utilities::spec::log::has_waker_set_in_current_poll(s.task_logs[tid], rid, last);
    assert(chunk > get_io_ready_bound(s, tid) + get_max_queue_length(s) + 2);
    // tid genuinely holds rid: is_io_active gives no deregister before `last`, and the
    // task log ends with a pending Poll (pending_poll_inv), which is not a deregister —
    // so there is no deregister of rid in tid's whole log.
    assert(crate::composed::spec::alignment::pending_poll_inv(s));
    assert(crate::composed::spec::alignment::task_log_ends_with_pending(s.task_logs[tid]));
    assert(crate::utilities::spec::events::is_poll_end_pending(
      s.task_logs[tid][(s.task_logs[tid].len() - 1) as int]));
    assert(!crate::utilities::spec::log::is_io_deregistered_before(
      s.task_logs[tid], rid, s.task_logs[tid].len() as int));
    composed_io_pending_to_poll(s, l_prime, chunk, cap, tid, rid);
  } else if crate::utilities::spec::log::has_defer_in_current_poll(s.task_logs[tid], last) {
    // ---- DEFER: DERIVED via the modeled Deferred queue (no wake_delivers_here) ----
    assert(0 < s.executor_log.len());
    composed_defer_pending_to_poll(s, l_prime, chunk, cap, tid);
  } else {
    // ---- pass-waker: DERIVED via the drain-membership arrival clause (Phase C) ----
    // pending_has_wakeup_source + excluded timer/io/defer ⟹ pass_waker is the source.
    assert(crate::utilities::spec::log::has_pass_waker_in_current_poll(s.task_logs[tid], last));
    assert(executor_log::last_poll_idx_for_id(s.executor_log, tid) == pending_idx) by {
      crate::composed::proof::end_to_end::last_poll_idx_properties(s.executor_log, tid);
      let q = executor_log::last_poll_idx_for_id(s.executor_log, tid);
      if q > pending_idx {
        assert(executor_log::is_poll_task_for_id_at(s.executor_log, q, tid));
      } else if q < pending_idx {
        assert(executor_log::is_poll_task_for_id_at(s.executor_log, pending_idx, tid));
      }
    }
    composed_taskwake_pending_to_poll(s, l_prime, chunk, cap, tid, pending_idx);
  }
}

// Pass-waker pending facts survive to a reached state where tid was not re-polled:
// the task log (hence its PassWaker) is unchanged, the last poll is still Pending,
// and the last-poll index is still pending_idx.
#[verifier::rlimit(50)]
proof fn taskwake_pending_facts_at(
  s: ComposedState, s1: ComposedState, n: nat, cap: nat, tid: TaskId, pending_idx: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    executor_log::last_poll_idx_for_id(s.executor_log, tid) == pending_idx,
    0 <= pending_idx < s.executor_log.len(),
    ete_reachable_N(s, s1, n, cap, tid),
    !executor_log::has_poll_task_for_id_after(s1.executor_log, tid, s.executor_log.len() as int),
  ensures
    s1.task_logs.contains_key(tid),
    s1.task_logs[tid] == s.task_logs[tid],
    executor_log::last_poll_is_pending(s1.executor_log, tid),
    executor_log::last_poll_idx_for_id(s1.executor_log, tid) == pending_idx,
    crate::executor::spec::log::is_prefix_of(s.executor_log, s1.executor_log),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |c: ComposedState, tt: TaskId| env_N(c, tt, cap);
  not_polled_preserves_pending(s, s1, n, cap, tid);
  ete_reachable_N_implies_env(s, s1, n, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, s1, n, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, s1, n);
  assert(crate::executor::spec::log::is_prefix_of(s.executor_log, s1.executor_log));
  // last poll of tid in s1 is still pending_idx (no poll after s ⟹ no new poll)
  crate::composed::proof::end_to_end::last_poll_idx_properties(s.executor_log, tid);
  crate::composed::proof::end_to_end::last_poll_idx_properties(s1.executor_log, tid);
  assert(executor_log::is_poll_task_for_id_at(s1.executor_log, pending_idx, tid)) by {
    assert(s1.executor_log[pending_idx] == s.executor_log[pending_idx]);
  }
  let q = executor_log::last_poll_idx_for_id(s1.executor_log, tid);
  assert(q == pending_idx) by {
    if q > pending_idx {
      assert(executor_log::is_poll_task_for_id_at(s1.executor_log, q, tid));
      if q < s.executor_log.len() {
        assert(s1.executor_log[q] == s.executor_log[q]);
        assert(executor_log::is_poll_task_for_id_at(s.executor_log, q, tid));
      } else {
        assert(executor_log::has_poll_task_for_id_after(s1.executor_log, tid, s.executor_log.len() as int));
      }
    } else if q < pending_idx {
      assert(executor_log::is_poll_task_for_id_at(s1.executor_log, pending_idx, tid));
    }
  }
}

// The FIRST post-window Drain{TaskWake} carries tid: after cap ticks (s → l_wake) plus
// one more step (l_wake → s1), the step's PROVEN Drain{TaskWake} occurrence
// (single_progress_has_drain_task_wake) either has an earlier drain in (pending_idx, d)
// that already took tid (return that one), or is itself obliged by the drain-membership
// arrival clause taskwake_arrival_within (its !taskwake_drained_in guard holds, and
// >= cap tick-ends separate pending_idx from d).
#[verifier::rlimit(50)]
proof fn taskwake_first_drain_carries_tid(
  s: ComposedState, l_wake: ComposedState, s1: ComposedState,
  cap: nat, tid: TaskId, pending_idx: int,
) -> (e: int)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::has_pass_waker_in_current_poll(
      s.task_logs[tid], (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    executor_log::last_poll_idx_for_id(s.executor_log, tid) == pending_idx,
    0 <= pending_idx < s.executor_log.len(),
    ete_reachable_N(s, l_wake, cap, cap, tid),
    ete_reachable_N(l_wake, s1, 1, cap, tid),
    ete_reachable_N(s, s1, (cap + 1) as nat, cap, tid),
    !executor_log::has_poll_task_for_id_after(s1.executor_log, tid, s.executor_log.len() as int),
    cap >= 1,
  ensures
    pending_idx < e < s1.executor_log.len(),
    executor_log::is_drain_at(s1.executor_log, e),
    executor_log::task_id_in_drain_at(s1.executor_log, e, tid),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |c: ComposedState, tt: TaskId| end_to_end_env(c, tt);
  taskwake_pending_facts_at(s, s1, (cap + 1) as nat, cap, tid, pending_idx);
  // prefixes: s ⊆ l_wake ⊆ s1
  ete_reachable_N_implies_env(s, l_wake, cap, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_wake, cap, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_wake, cap);
  ete_reachable_one_step(l_wake, s1, cap, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(l_wake, s1, 1);
  reveal(crate::composed::spec::progress::composed_progress);
  // the step's tick has a Drain{TaskWake} at d in the new content (PROVEN occurrence)
  crate::executor::proof::bounded_drain_poll::single_progress_has_drain_task_wake(
    l_wake.executor_log, s1.executor_log);
  let d: int = choose |d: int|
    #![trigger executor_log::is_drain_task_wake_at(s1.executor_log, d)]
    l_wake.executor_log.len() as int <= d < s1.executor_log.len()
    && executor_log::is_drain_task_wake_at(s1.executor_log, d);
  assert(pending_idx < d);
  if crate::composed::spec::wake_queues::taskwake_drained_in(
    s1.executor_log, tid, pending_idx, d) {
    // an earlier drain already took tid
    let e: int = choose |e: int|
      #![trigger s1.executor_log[e]]
      pending_idx < e < d &&
      executor_log::is_drain_task_wake_at(s1.executor_log, e) &&
      executor_log::task_id_in_drain_at(s1.executor_log, e, tid);
    e
  } else {
    // arrival clock: >= cap tick-ends in (pending_idx, d) — l_wake's window is a prefix of it
    ete_reachable_N_grows_tick_ends(s, l_wake, cap, cap, tid, pending_idx);
    crate::executor::proof::bounded_drain_poll::count_tick_ends_prefix_equals(
      l_wake.executor_log, s1.executor_log, pending_idx, l_wake.executor_log.len() as int);
    crate::executor::proof::bounded_drain_poll::count_tick_ends_additivity_range(
      s1.executor_log, pending_idx, l_wake.executor_log.len() as int, d);
    assert(executor_log::count_tick_ends_between(s1.executor_log, pending_idx, d) >= cap);
    // fire the drain-membership arrival clause at s1
    ete_reachable_N_gives_env_N_at_end(s, s1, (cap + 1) as nat, cap, tid);
    reveal(taskwake_arrival_within);
    assert(executor_log::task_id_in_drain_at(s1.executor_log, d, tid));
    d
  }
}

// TASKWAKE: pass-waker pending → tid POLLED, via the drain-membership arrival clause
// (wake-routing Phase C, drain-membership form). Wait cap ticks (arrival window), take
// one more step whose Drain{TaskWake} is PROVEN to occur; the arrival clause (or an
// earlier drain) puts tid in that drain; drain_adds_tid_to_queue puts it in the
// runnable FIFO; queue_member_eventually_polled_on_trace drains it to a poll. Same
// Drain→FIFO→poll structure as composed_defer_pending_to_poll — only the arrival is
// assumed (the utility kernel is unmodeled), everything downstream is derived.
#[verifier::rlimit(50)]
pub proof fn composed_taskwake_pending_to_poll(
  s: ComposedState, l_prime: ComposedState, chunk: nat, cap: nat, tid: TaskId, pending_idx: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::has_pass_waker_in_current_poll(
      s.task_logs[tid], (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    executor_log::last_poll_idx_for_id(s.executor_log, tid) == pending_idx,
    0 <= pending_idx < s.executor_log.len(),
    forall |j: int| pending_idx < j < s.executor_log.len() ==>
      !executor_log::is_poll_task_for_id_at(s.executor_log, j, tid),
    ete_reachable_N(s, l_prime, chunk, cap, tid),
    chunk > cap + get_max_queue_length(s) + 1,
    cap >= 1,
  ensures
    executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int),
{
  if executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int) {
    return;
  }
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |c: ComposedState, tt: TaskId| end_to_end_env(c, tt);
  // split s → s1 (cap+1: arrival window + drain step) → l_prime, then s1's window
  ete_reachable_N_split(s, l_prime, (cap + 1) as nat, (chunk - cap - 1) as nat, cap, tid);
  let s1: ComposedState = choose |s1: ComposedState|
    #[trigger] ete_reachable_N(s, s1, (cap + 1) as nat, cap, tid)
    && ete_reachable_N(s1, l_prime, (chunk - cap - 1) as nat, cap, tid);
  ete_reachable_N_split(s, s1, cap, 1nat, cap, tid);
  let l_wake: ComposedState = choose |l_wake: ComposedState|
    #[trigger] ete_reachable_N(s, l_wake, cap, cap, tid)
    && ete_reachable_N(l_wake, s1, 1nat, cap, tid);
  // s1 ⊆ l_prime, so a poll of tid after s in s1 would persist to l_prime — none exists
  ete_reachable_N_implies_env(s1, l_prime, (chunk - cap - 1) as nat, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(
    progress, s1, l_prime, (chunk - cap - 1) as nat, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s1, l_prime, (chunk - cap - 1) as nat);
  assert(!executor_log::has_poll_task_for_id_after(s1.executor_log, tid, s.executor_log.len() as int)) by {
    if executor_log::has_poll_task_for_id_after(s1.executor_log, tid, s.executor_log.len() as int) {
      let pidx = choose |pidx: int|
        s.executor_log.len() as int <= pidx < s1.executor_log.len() &&
        executor_log::is_poll_task_for_id_at(s1.executor_log, pidx, tid);
      assert(s1.executor_log[pidx] == l_prime.executor_log[pidx]);
    }
  }
  let e = taskwake_first_drain_carries_tid(s, l_wake, s1, cap, tid, pending_idx);
  // Drain → FIFO → survives (tid is never polled in (e, s1.len()))
  crate::composed::proof::end_to_end::drain_adds_tid_to_queue(s1.executor_log, tid, e);
  crate::composed::proof::end_to_end::progress_n_preserves_wf(s, s1, (cap + 1) as nat);
  crate::composed::proof::end_to_end::tid_survives_or_polled_in_range(
    s1.executor_log, tid, e + 1, s1.executor_log.len() as int);
  if exists |pidx: int| e + 1 <= pidx < s1.executor_log.len()
    && executor_log::is_poll_task_for_id_at(s1.executor_log, pidx, tid) {
    let pidx: int = choose |pidx: int| e + 1 <= pidx < s1.executor_log.len()
      && executor_log::is_poll_task_for_id_at(s1.executor_log, pidx, tid);
    assert(pending_idx < pidx);
    if pidx < s.executor_log.len() {
      // contradicts "no poll of tid in (pending_idx, s.len())"
      taskwake_pending_facts_at(s, s1, (cap + 1) as nat, cap, tid, pending_idx);
      assert(s1.executor_log[pidx] == s.executor_log[pidx]);
      assert(executor_log::is_poll_task_for_id_at(s.executor_log, pidx, tid));
      assert(false);
    } else {
      // contradicts "no poll of tid after s in s1"
      assert(executor_log::has_poll_task_for_id_after(s1.executor_log, tid, s.executor_log.len() as int));
      assert(false);
    }
  } else {
    assert(crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
      s1.executor_log, s1.executor_log.len() as int, tid));
    taskwake_pending_facts_at(s, s1, (cap + 1) as nat, cap, tid, pending_idx);
    assert(0 < s1.executor_log.len());
    assert(get_max_queue_length(s1) == get_max_queue_length(s));
    queue_member_eventually_polled_on_trace(s1, l_prime, (chunk - cap - 1) as nat, cap, tid);
    assert(executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int)) by {
      let pj = choose |pj: int|
        s1.executor_log.len() as int <= pj < l_prime.executor_log.len() &&
        executor_log::is_poll_task_for_id_at(l_prime.executor_log, pj, tid);
      assert(s.executor_log.len() as int <= pj);
    }
  }
}


// ============================================================================
// t4 (Phase 0/A composed migration): thread the task's FIXED reactor
// registration index i and CONSUME the reactor's per-registration (i-keyed)
// timer contract bounded_timer_wakeup_at directly, instead of the rid-keyed
// (leftmost-recompute) bounded_timer_wakeup. The not-deregistered-at-i fact is
// sourced from timer_resources_remain_active — since t4b that clause is the
// WEAKENED, reuse-tolerant current-poll-owned form (it holds at registrations
// owned by the current poll, which covers i here).
// ============================================================================

// Establish current-poll-ownership of reactor register index i from an explicit
// task-op witness (tid, t): tid's current-poll RegisterTimer at t is matched by i.
pub proof fn timer_reg_current_poll_owned_from_witness(
  s: ComposedState, tid: TaskId, t: int, i: int,
)
  requires
    s.task_logs.contains_key(tid),
    0 <= t < s.task_logs[tid].len(),
    crate::utilities::spec::events::is_register_timer(s.task_logs[tid][t]),
    crate::utilities::spec::log::in_current_poll_cycle(
      s.task_logs[tid], t, (s.task_logs[tid].len() - 1) as int),
    0 <= i < s.reactor_log.len(),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[i], s.task_logs[tid][t]),
  ensures
    timer_reg_current_poll_owned(s, i),
{
  reveal(timer_reg_current_poll_owned);
}

// Extract the task's fixed reactor register-timer index i for rid AND the matching
// task-op index t (composed action-mediation). t is threaded so current-poll-ownership
// of i can be re-established at reached states (tid's task log unchanged when not polled).
#[verifier::rlimit(50)]
pub proof fn composed_timer_reg_reactor_idx(
  s: ComposedState, tid: TaskId, rid: ResourceIdView,
) -> (r: (int, int))
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::has_timer_registered_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
  ensures
    ({ let (i, t) = r;
    0 <= i < s.reactor_log.len() &&
    reactor_log::is_succ_register_timer_at(s.reactor_log, i) &&
    crate::reactor::spec::events::get_register_timer_rid(s.reactor_log[i]) == rid &&
    0 <= t < s.task_logs[tid].len() &&
    crate::utilities::spec::events::is_register_timer(s.task_logs[tid][t]) &&
    crate::utilities::spec::log::in_current_poll_cycle(
      s.task_logs[tid], t, (s.task_logs[tid].len() - 1) as int) &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[i], s.task_logs[tid][t]) &&
    timer_reg_current_poll_owned(s, i) }),
{
  let task_log = s.task_logs[tid];
  let last_idx = (task_log.len() - 1) as int;
  let j: int = choose |j: int|
    crate::utilities::spec::log::in_current_poll_cycle(task_log, j, last_idx) &&
    crate::utilities::spec::events::is_register_timer(task_log[j]) &&
    crate::utilities::spec::events::get_resource_id(task_log[j]) == Some(rid) &&
    !crate::utilities::spec::log::timer_deregistered_after_in_poll(task_log, rid, j, last_idx);
  assert(0 <= j < task_log.len());
  assert(crate::composed::spec::alignment::is_reactor_operation(task_log[j]));
  let k: int = choose |k: int|
    0 <= k < s.reactor_log.len() &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[k], task_log[j]);
  assert(reactor_log::is_succ_register_timer_at(s.reactor_log, k));
  assert(crate::reactor::spec::events::get_register_timer_rid(s.reactor_log[k]) == rid);
  timer_reg_current_poll_owned_from_witness(s, tid, j, k);
  (k, j)
}

// i-keyed deadline bound: the per-registration bound at i is <= env's uniform
// deadline gap (mirror of timer_concrete_bound_le_gap with reg = i).
pub proof fn timer_concrete_bound_at_le_gap(s: ComposedState, tid: TaskId, i: int)
  requires
    timer_deadline_gap_bounded(s, tid),
    0 <= i < s.reactor_log.len(),
    reactor_log::is_succ_register_timer_at(s.reactor_log, i),
    crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(
      s.reactor_log, i, s.reactor_log.len() as int),
  ensures
    crate::reactor::proof::timer_liveness::timer_concrete_bound_at(s.reactor_log, i)
      <= get_max_timer_deadline_gap(s, tid),
{
  reveal(timer_deadline_gap_bounded);
  assert(crate::reactor::proof::round_extension::compute_bound(
      crate::reactor::spec::events::get_register_timer_deadline(s.reactor_log[i]),
      reactor_log::max_timestamp_up_to(s.reactor_log, (i + 1) as int))
    <= get_max_timer_deadline_gap(s, tid));
  crate::reactor::proof::timer_liveness::max_ts_monotone(
    s.reactor_log, (i + 1) as int, s.reactor_log.len() as int);
  crate::reactor::proof::round_extension::compute_bound_monotone(
    crate::reactor::spec::events::get_register_timer_deadline(s.reactor_log[i]),
    reactor_log::max_timestamp_up_to(s.reactor_log, s.reactor_log.len() as int),
    reactor_log::max_timestamp_up_to(s.reactor_log, (i + 1) as int));
}

// i-keyed not-dereg between (t4b, reuse-tolerant): at a reached l_x where tid is NOT
// polled, the timer at the fixed index i is not deregistered through l_x. Sourced from
// the WEAKENED A4' timer_resources_remain_active(l_x): i stays current-poll-owned because
// tid's task log is unchanged (not polled) and i's reactor event persists (prefix), so
// the witness (tid, t) still matches — no find_last stability needed.
pub proof fn env_reactor_timer_active_between_at(
  s: ComposedState, l_x: ComposedState, m: nat, cap: nat, tid: TaskId, i: int, t: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    0 <= i < s.reactor_log.len(),
    reactor_log::is_succ_register_timer_at(s.reactor_log, i),
    0 <= t < s.task_logs[tid].len(),
    crate::utilities::spec::events::is_register_timer(s.task_logs[tid][t]),
    crate::utilities::spec::log::in_current_poll_cycle(
      s.task_logs[tid], t, (s.task_logs[tid].len() - 1) as int),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[i], s.task_logs[tid][t]),
    ete_reachable_N(s, l_x, m, cap, tid),
    !executor_log::has_poll_task_for_id_after(l_x.executor_log, tid, s.executor_log.len() as int),
  ensures
    crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(
      l_x.reactor_log, i, l_x.reactor_log.len() as int),
{
  ete_reachable_N_gives_env_N_at_end(s, l_x, m, cap, tid);
  env_N_implies_env(l_x, tid, cap);
  env_gives_core_clauses(l_x, tid);
  ete_reachable_N_implies_env(s, l_x, m, cap, tid);
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_x, m, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_x, m);
  assert(l_x.reactor_log[i] == s.reactor_log[i]);
  assert(reactor_log::is_succ_register_timer_at(l_x.reactor_log, i));
  // tid not polled ⇒ task log unchanged ⇒ (tid, t) still witnesses current-poll-ownership.
  not_polled_preserves_pending(s, l_x, m, cap, tid);
  assert(l_x.task_logs[tid] =~= s.task_logs[tid]);
  assert(l_x.task_logs[tid][t] == s.task_logs[tid][t]);
  timer_reg_current_poll_owned_from_witness(l_x, tid, t, i);
  assert(timer_resources_remain_active(l_x));
}

// Pending timer poll → tid POLLED, CONSUMING the module env-form timer contract:
// composed_timer_contract_gives_response (via bounded_liveness_env interface) yields
// fulfillment at l_wake (n_c steps, n_c bounded); env's wake_routing routes tid into
// the queue; queue_member drains to a poll. The timer wake is DERIVED through the
// module CONTRACT — no reach-in to env_timer_wake_general_at.
#[verifier::rlimit(100)]
pub proof fn composed_timer_pending_to_poll_via_contract(
  s: ComposedState, l_prime: ComposedState, chunk: nat, cap: nat, tid: TaskId, rid: ResourceIdView,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::has_timer_registered_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    ete_reachable_N(s, l_prime, chunk, cap, tid),
    // Phase B: +2 (was +1) — after the wake fires at l_wake, delivery costs one drain
    // tick MORE than the old same-tick wake_delivers_here form (the modeled queue
    // decouples push from drain). The caller's +cap (cap>=1) slack covers this.
    chunk > get_max_timer_deadline_gap(s, tid) + get_max_queue_length(s) + 2,
    cap >= 1,
  ensures
    executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int),
{
  if executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int) {
    return;
  }
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  ete_reachable_N_gives_env_N_at_start(s, l_prime, chunk, cap, tid);
  // FIXED task registration index i + matching task-op t (t4): thread them through
  // the i-keyed derivation; t re-establishes current-poll-ownership at l_wake.
  let (i, t): (int, int) = composed_timer_reg_reactor_idx(s, tid, rid);
  // bounded split point n_c (the timer wake bound); l_wake is where the wake fires
  let n_c: nat = composed_timer_contract_gives_response(s, tid, cap, rid, i, t);
  assert((chunk - n_c) as nat > get_max_queue_length(s) + 1);
  ete_reachable_N_split(s, l_prime, n_c, (chunk - n_c) as nat, cap, tid);
  let l_wake: ComposedState = choose |l_wake: ComposedState|
    ete_reachable_N(s, l_wake, n_c, cap, tid) && ete_reachable_N(l_wake, l_prime, (chunk - n_c) as nat, cap, tid);
  // l_wake ⊆ l_prime (poll persistence + length)
  ete_reachable_N_implies_env(l_wake, l_prime, (chunk - n_c) as nat, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(
    progress, l_wake, l_prime, (chunk - n_c) as nat, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(l_wake, l_prime, (chunk - n_c) as nat);
  // not polled over [s, l_wake] — else it persists to l_prime and we returned above
  assert(!executor_log::has_poll_task_for_id_after(l_wake.executor_log, tid, s.executor_log.len() as int)) by {
    if executor_log::has_poll_task_for_id_after(l_wake.executor_log, tid, s.executor_log.len() as int) {
      let pidx = choose |pidx: int|
        s.executor_log.len() as int <= pidx < l_wake.executor_log.len() &&
        executor_log::is_poll_task_for_id_at(l_wake.executor_log, pidx, tid);
      assert(l_wake.executor_log[pidx] == l_prime.executor_log[pidx]);
    }
  }
  // wake FIRED at l_wake, in the current registration window
  composed_env_timer_fulfillment(s, l_wake, l_prime, n_c, (chunk - n_c) as nat, cap, tid, rid, i, t);
  // tid's owned WakeTask has fired at l_wake ⟹ tid is in the MODELED reactor-wake queue
  timer_window_delivers_queued(s, l_wake, n_c, cap, tid, rid, i, t);
  // s ⊆ l_wake (executor length) + wf for the drain-based delivery
  ete_reachable_N_implies_env(s, l_wake, n_c, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_wake, n_c, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_wake, n_c);
  crate::composed::proof::end_to_end::progress_n_preserves_wf(s, l_wake, n_c);
  assert(0 < l_wake.executor_log.len());
  assert(get_max_queue_length(l_wake) == get_max_queue_length(s));
  // not-polled-since forall at l_wake (tautological: no poll after the last poll)
  crate::composed::proof::end_to_end::last_poll_idx_properties(l_wake.executor_log, tid);
  // DERIVE delivery via the modeled reactor-wake queue + drain step (no wake_delivers_here)
  composed_reactor_wake_pending_to_poll(l_wake, l_prime, (chunk - n_c) as nat, cap, tid);
}

// The window wake-delivery step (timer): at l_wake the timer wake has FIRED in the
// current window and tid has NOT been polled since s (so still Pending, task log
// unchanged) — hence wake_fired_unconsumed holds, and env_N's wake_delivers_here
// routes tid into the runnable FIFO at l_wake. Split out to bound the SMT context.
#[verifier::rlimit(50)]
proof fn timer_window_delivers_queued(
  s: ComposedState, l_wake: ComposedState, n_c: nat, cap: nat, tid: TaskId, rid: ResourceIdView, i: int, t: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::has_timer_registered_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    0 <= i < s.reactor_log.len(),
    reactor_log::is_succ_register_timer_at(s.reactor_log, i),
    crate::reactor::spec::events::get_register_timer_rid(s.reactor_log[i]) == rid,
    0 <= t < s.task_logs[tid].len(),
    crate::utilities::spec::events::is_register_timer(s.task_logs[tid][t]),
    crate::utilities::spec::log::in_current_poll_cycle(
      s.task_logs[tid], t, (s.task_logs[tid].len() - 1) as int),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[i], s.task_logs[tid][t]),
    ete_reachable_N(s, l_wake, n_c, cap, tid),
    !executor_log::has_poll_task_for_id_after(l_wake.executor_log, tid, s.executor_log.len() as int),
    crate::reactor::contracts::bounded_timer_wakeup::response_at(l_wake.reactor_log, i),
  ensures
    // Phase B: instead of routing tid into the FIFO via the free wake_delivers_here,
    // establish that tid's owned WakeTask has FIRED at l_wake (reactor_wake_arrival) —
    // the arrival into the MODELED reactor-wake queue. Delivery is then DERIVED by the
    // caller via composed_reactor_wake_pending_to_poll (reactor_wake_drain_step).
    crate::composed::spec::wake_queues::reactor_wake_arrival(l_wake, tid),
    l_wake.task_logs.contains_key(tid),
    executor_log::last_poll_is_pending(l_wake.executor_log, tid),
{
  not_polled_preserves_pending(s, l_wake, n_c, cap, tid);
  let last = (s.task_logs[tid].len() - 1) as int;
  let lastw = (l_wake.task_logs[tid].len() - 1) as int;
  assert(l_wake.task_logs[tid] =~= s.task_logs[tid]);
  assert(lastw == last);
  ete_reachable_N_gives_env_N_at_end(s, l_wake, n_c, cap, tid);
  // i persists as its registration in l_wake (reactor prefix); (tid, t) re-witnesses
  // current-poll-ownership of i (tid not polled ⇒ task log unchanged).
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  ete_reachable_N_implies_env(s, l_wake, n_c, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_wake, n_c, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_wake, n_c);
  assert(l_wake.reactor_log[i] == s.reactor_log[i]);
  assert(reactor_log::is_succ_register_timer_at(l_wake.reactor_log, i));
  assert(crate::reactor::spec::events::get_register_timer_rid(l_wake.reactor_log[i]) == rid);
  assert(l_wake.task_logs[tid][t] == s.task_logs[tid][t]);
  timer_reg_current_poll_owned_from_witness(l_wake, tid, t, i);
  // i-keyed timer_wake_owned(l_wake, tid) (witness index i) — the timer disjunct of
  // reactor_wake_arrival: tid's current registration i had its OWN waker fire.
  assert(timer_wake_owned(l_wake, tid)) by {
    assert(crate::utilities::spec::log::has_timer_registered_in_current_poll(
      l_wake.task_logs[tid], rid, lastw)) by {
      assert(l_wake.task_logs[tid] == s.task_logs[tid]);
    }
    assert(0 <= i < l_wake.reactor_log.len() &&
      reactor_log::is_succ_register_timer_at(l_wake.reactor_log, i) &&
      timer_reg_current_poll_owned(l_wake, i) &&
      crate::utilities::spec::log::has_timer_registered_in_current_poll(
        l_wake.task_logs[tid],
        crate::reactor::spec::events::get_register_timer_rid(l_wake.reactor_log[i]), lastw) &&
      crate::reactor::contracts::bounded_timer_wakeup::response_at(l_wake.reactor_log, i));
  }
  assert(crate::composed::spec::wake_queues::reactor_wake_arrival(l_wake, tid)) by {
    reveal(crate::composed::spec::wake_queues::reactor_wake_arrival);
  }
}



// The i-keyed timer response bound n_c = timer_concrete_bound_at(s.reactor, i) + 1,
// bounded uniformly by env's deadline gap. not-dereg-at-i (needed to fire the gap
// clause) is sourced from the WEAKENED A4' via the current-poll-owned witness (tid, t).
// (t4b: the forall-l_prime contract-response ensures was dropped — under reuse-tolerance
// the wake is established only at the not-polled l_wake, via composed_env_timer_fulfillment
// consuming env_timer_wake_general_at directly; the response bound needs no contract.)
pub proof fn composed_timer_contract_gives_response(
  s: ComposedState, tid: TaskId, cap: nat, rid: ResourceIdView, i: int, t: int,
) -> (n_c: nat)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    env_N(s, tid, cap),
    0 <= i < s.reactor_log.len(),
    reactor_log::is_succ_register_timer_at(s.reactor_log, i),
    0 <= t < s.task_logs[tid].len(),
    crate::utilities::spec::events::is_register_timer(s.task_logs[tid][t]),
    crate::utilities::spec::log::in_current_poll_cycle(
      s.task_logs[tid], t, (s.task_logs[tid].len() - 1) as int),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[i], s.task_logs[tid][t]),
  ensures
    n_c >= 1,
    n_c >= crate::reactor::proof::timer_liveness::timer_concrete_bound_at(s.reactor_log, i),
    n_c <= get_max_timer_deadline_gap(s, tid) + 1,
{
  env_N_implies_env(s, tid, cap);
  env_gives_core_clauses(s, tid);
  // not-dereg at i from the weakened A4' via current-poll-owned witness (tid, t)
  timer_reg_current_poll_owned_from_witness(s, tid, t, i);
  assert(timer_resources_remain_active(s));
  assert(crate::reactor::invariants::wake_on_expired::timer_not_deregistered_through(
    s.reactor_log, i, s.reactor_log.len() as int));
  timer_concrete_bound_at_le_gap(s, tid, i);
  (crate::reactor::proof::timer_liveness::timer_concrete_bound_at(s.reactor_log, i) + 1) as nat
}

// io find_last link (trace induction): a new SetWaker for rid appearing in the
// reactor window ⟹ the rid-owner tid's task_log grew. At the step the SetWaker
// appears, new_reactor_event_has_new_op gives a NEW source op; setwaker_op_owner_is_tid
// pins it to tid; so tid's task_log grew that step. Otherwise recurse on the prefix.
// Isolated unfolds of composed_progress (keep the expensive reveal out of the heavy
// step lemma).
pub proof fn progress_gives_cma(s: ComposedState, s_prime: ComposedState)
  requires crate::composed::spec::progress::composed_progress(s, s_prime),
  ensures crate::composed::spec::alignment::cross_module_alignment(s, s_prime),
{ reveal(crate::composed::spec::progress::composed_progress); }

pub proof fn cma_gives_new_reactor_event_has_new_op(s: ComposedState, s_prime: ComposedState)
  requires crate::composed::spec::alignment::cross_module_alignment(s, s_prime),
  ensures crate::composed::spec::alignment::new_reactor_event_has_new_op(s, s_prime),
{
  reveal(crate::composed::spec::alignment::cross_module_alignment);
  assert(crate::composed::spec::alignment::action_mediation_step(s, s_prime));
}

pub proof fn progress_gives_new_reactor_event_has_new_op(s: ComposedState, s_prime: ComposedState)
  requires crate::composed::spec::progress::composed_progress(s, s_prime),
  ensures crate::composed::spec::alignment::new_reactor_event_has_new_op(s, s_prime),
{
  progress_gives_cma(s, s_prime);
  cma_gives_new_reactor_event_has_new_op(s, s_prime);
}

pub proof fn progress_gives_extension(s: ComposedState, s_prime: ComposedState)
  requires crate::composed::spec::progress::composed_progress(s, s_prime),
  ensures crate::composed::spec::state::is_extension_of(s, s_prime),
{ reveal(crate::composed::spec::progress::composed_progress); }

// Per-step: a SetWaker for rid new in THIS step ⟹ the rid owner tid's task_log grew.
#[verifier::rlimit(60)]
pub proof fn setwaker_step_grows_task_log(
  s: ComposedState, s_prime: ComposedState, tid: TaskId, rid: ResourceIdView, j: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s_prime),
    crate::composed::spec::progress::composed_progress(s, s_prime),
    crate::composed::spec::alignment::composed_active_rid(s_prime, tid, rid),
    crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(s_prime.reactor_log, rid),
    s.task_logs.contains_key(tid),
    s.reactor_log.len() <= j < s_prime.reactor_log.len(),
    reactor_log::is_succ_set_waker_at(s_prime.reactor_log, j),
    crate::reactor::spec::events::get_set_waker_rid(s_prime.reactor_log[j]) == rid,
    // j is the LAST SetWaker for rid at s_prime (so it == find_last, the anchor
    // the reuse-tolerant keystone requires).
    forall |q: int| j < q < s_prime.reactor_log.len() ==>
      !(reactor_log::is_succ_set_waker_at(s_prime.reactor_log, q) &&
        crate::reactor::spec::events::get_set_waker_rid(s_prime.reactor_log[q]) == rid),
  ensures
    s_prime.task_logs.contains_key(tid),
    s_prime.task_logs[tid].len() > s.task_logs[tid].len(),
{
  progress_gives_extension(s, s_prime);
  progress_gives_new_reactor_event_has_new_op(s, s_prime);
  assert(crate::composed::spec::alignment::is_task_initiated_reactor_event(s_prime.reactor_log[j]));
  let (tp, ti): (TaskId, int) = choose |tp: TaskId, ti: int|
    #![trigger s_prime.task_logs[tp][ti]]
    s_prime.task_logs.contains_key(tp) &&
    (if s.task_logs.contains_key(tp) { s.task_logs[tp].len() as int } else { 0int })
      <= ti < s_prime.task_logs[tp].len() &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s_prime.reactor_log[j], s_prime.task_logs[tp][ti]);
  assert(crate::utilities::spec::events::is_set_waker(s_prime.task_logs[tp][ti]));
  assert(crate::utilities::spec::events::get_resource_id(s_prime.task_logs[tp][ti]) == Some(rid));
  // j == find_last(s_prime), so the keystone's last-set-waker anchor is j.
  crate::reactor::proof::io_liveness::find_last_eq_if_last(
    s_prime.reactor_log, rid, s_prime.reactor_log.len() as int, j);
  setwaker_op_owner_is_tid(s_prime, tid, tp, ti, rid);
  assert(tp == tid);
  // tid exists at s (precondition), so the guarded lower bound is s's log length.
  assert(s.task_logs[tid].len() <= ti < s_prime.task_logs[tid].len());
}

// task_log length is monotone along a valid trace.
pub proof fn task_log_len_monotone_from_start(trace: Seq<ComposedState>, tid: TaskId, m: int)
  requires
    crate::framework::module_spec::is_valid_trace(
      crate::composed::spec::progress::composed_module_spec().progress, trace),
    0 <= m < trace.len(),
    forall |k: int| 0 <= k <= m ==> (#[trigger] trace[k].task_logs).contains_key(tid),
  ensures
    trace[m].task_logs[tid].len() >= trace[0].task_logs[tid].len(),
  decreases m
{
  if m > 0 {
    task_log_len_monotone_from_start(trace, tid, m - 1);
    assert(crate::composed::spec::progress::composed_progress(trace[m - 1], trace[m]));
    progress_gives_extension(trace[m - 1], trace[m]);
  }
}

// task_log length is monotone between any two trace indices i <= j.
pub proof fn task_log_len_monotone_between(trace: Seq<ComposedState>, tid: TaskId, i: int, j: int)
  requires
    crate::framework::module_spec::is_valid_trace(
      crate::composed::spec::progress::composed_module_spec().progress, trace),
    0 <= i <= j < trace.len(),
    forall |k: int| i <= k <= j ==> (#[trigger] trace[k].task_logs).contains_key(tid),
  ensures
    trace[j].task_logs[tid].len() >= trace[i].task_logs[tid].len(),
  decreases j - i
{
  if j > i {
    task_log_len_monotone_between(trace, tid, i, j - 1);
    assert(crate::composed::spec::progress::composed_progress(trace[j - 1], trace[j]));
    progress_gives_extension(trace[j - 1], trace[j]);
  }
}

// io find_last link (trace induction over n): dispatches each step to
// setwaker_step_grows_task_log or recurses on the prefix.
pub proof fn new_setwaker_implies_task_log_growth(
  trace: Seq<ComposedState>, tid: TaskId, rid: ResourceIdView, n: int, j: int,
)
  requires
    trace.len() > n, n >= 1,
    crate::framework::module_spec::is_valid_trace(
      crate::composed::spec::progress::composed_module_spec().progress, trace),
    forall |k: int| 0 <= k <= n ==> #[trigger] crate::composed::spec::progress::composed_well_formed(trace[k]),
    forall |k: int| 0 <= k <= n ==>
      crate::composed::spec::alignment::composed_active_rid(#[trigger] trace[k], tid, rid),
    forall |k: int| 0 <= k <= n ==>
      crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(
        (#[trigger] trace[k]).reactor_log, rid),
    forall |k: int| 0 <= k <= n ==> (#[trigger] trace[k].task_logs).contains_key(tid),
    trace[0].reactor_log.len() <= j < trace[n].reactor_log.len(),
    reactor_log::is_succ_set_waker_at(trace[n].reactor_log, j),
    crate::reactor::spec::events::get_set_waker_rid(trace[n].reactor_log[j]) == rid,
    // j is the LAST SetWaker for rid at trace[n] (prefix-stable, so carried down).
    forall |q: int| j < q < trace[n].reactor_log.len() ==>
      !(reactor_log::is_succ_set_waker_at(trace[n].reactor_log, q) &&
        crate::reactor::spec::events::get_set_waker_rid(trace[n].reactor_log[q]) == rid),
    trace[0].task_logs.contains_key(tid),
  ensures
    trace[n].task_logs[tid].len() > trace[0].task_logs[tid].len(),
  decreases n
{
  assert(crate::composed::spec::progress::composed_progress(trace[n - 1], trace[n]));
  progress_gives_extension(trace[n - 1], trace[n]);
  if j >= trace[n - 1].reactor_log.len() {
    setwaker_step_grows_task_log(trace[n - 1], trace[n], tid, rid, j);
    task_log_len_monotone_from_start(trace, tid, n - 1);
  } else {
    assert(trace[n - 1].reactor_log[j] == trace[n].reactor_log[j]);
    // no-later carries to trace[n-1] (prefix of trace[n])
    assert forall |q: int| j < q < trace[n - 1].reactor_log.len() implies
      !(reactor_log::is_succ_set_waker_at(trace[n - 1].reactor_log, q) &&
        crate::reactor::spec::events::get_set_waker_rid(#[trigger] trace[n - 1].reactor_log[q]) == rid) by {
      assert(trace[n - 1].reactor_log[q] == trace[n].reactor_log[q]);
      assert(!(reactor_log::is_succ_set_waker_at(trace[n].reactor_log, q) &&
        crate::reactor::spec::events::get_set_waker_rid(trace[n].reactor_log[q]) == rid));
    }
    new_setwaker_implies_task_log_growth(trace, tid, rid, n - 1, j);
  }
}

// io find_last case-split (contrapositive): a new SetWaker for rid in the reactor
// window ⟹ the owner tid was polled. Combines the task_log-growth link with
// task_log_growth_implies_poll.
pub proof fn new_setwaker_implies_poll(
  trace: Seq<ComposedState>, tid: TaskId, rid: ResourceIdView, n: int, j: int,
)
  requires
    trace.len() > n, n >= 1,
    crate::framework::module_spec::is_valid_trace(
      crate::composed::spec::progress::composed_module_spec().progress, trace),
    forall |k: int| 0 <= k <= n ==> #[trigger] crate::composed::spec::progress::composed_well_formed(trace[k]),
    forall |k: int| 0 <= k <= n ==>
      crate::composed::spec::alignment::composed_active_rid(#[trigger] trace[k], tid, rid),
    forall |k: int| 0 <= k <= n ==>
      crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(
        (#[trigger] trace[k]).reactor_log, rid),
    forall |k: int| 0 <= k <= n ==> (#[trigger] trace[k].task_logs).contains_key(tid),
    trace[0].reactor_log.len() <= j < trace[n].reactor_log.len(),
    reactor_log::is_succ_set_waker_at(trace[n].reactor_log, j),
    crate::reactor::spec::events::get_set_waker_rid(trace[n].reactor_log[j]) == rid,
    forall |q: int| j < q < trace[n].reactor_log.len() ==>
      !(reactor_log::is_succ_set_waker_at(trace[n].reactor_log, q) &&
        crate::reactor::spec::events::get_set_waker_rid(trace[n].reactor_log[q]) == rid),
  ensures
    exists |poll_idx: int|
      #![trigger trace[n].executor_log[poll_idx]]
      trace[0].executor_log.len() as int <= poll_idx < trace[n].executor_log.len() &&
      crate::executor::spec::log::is_poll_task_for_id_at(trace[n].executor_log, poll_idx, tid),
{
  new_setwaker_implies_task_log_growth(trace, tid, rid, n, j);
  crate::composed::proof::end_to_end::task_log_growth_implies_poll(trace, tid, n);
}

// A prefix of an env_N-good trace is itself env_N-reachable, and its endpoint is env_N.
pub proof fn ete_reachable_N_from_trace_prefix(
  trace: Seq<ComposedState>, s: ComposedState, cap: nat, tid: TaskId, n: int, k: int,
)
  requires
    0 <= k <= n,
    trace.len() == n + 1,
    trace[0] == s,
    crate::framework::module_spec::is_valid_trace(
      crate::composed::spec::progress::composed_module_spec().progress, trace),
    crate::framework::module_spec::env_holds_along(
      crate::composed::spec::progress::composed_module_spec().progress, trace,
      |c: ComposedState, tt: TaskId| env_N(c, tt, cap), tid),
  ensures
    ete_reachable_N(s, trace[k], k as nat, cap, tid),
    env_N(trace[k], tid, cap),
{
  let cprog = crate::composed::spec::progress::composed_module_spec().progress;
  let cenv = |c: ComposedState, tt: TaskId| env_N(c, tt, cap);
  assert(cenv(trace[k], tid));
  let sub: Seq<ComposedState> = trace.subrange(0, (k + 1) as int);
  assert(crate::framework::module_spec::env_progress_n(cprog, s, trace[k], k as nat, cenv, tid)) by {
    assert(sub.len() == k + 1);
    assert(sub[0] == s);
    assert(sub[k] == trace[k]);
    assert(crate::framework::module_spec::is_valid_trace(cprog, sub)) by {
      assert forall |i: int| #![trigger sub[i]] 0 <= i < sub.len() - 1 implies cprog(sub[i], sub[i + 1]) by {
        assert(sub[i] == trace[i] && sub[i + 1] == trace[i + 1]);
      };
    };
    assert(crate::framework::module_spec::env_holds_along(cprog, sub, cenv, tid)) by {
      assert forall |i: int| #![trigger sub[i]] 0 <= i < sub.len() implies cenv(sub[i], tid) by {
        assert(sub[i] == trace[i]);
      };
    };
  };
}

// A suffix of an env_N-good trace: its endpoint is env_N-reachable from trace[k]
// (t5c — lets io_trace_facts_at carry !polled down to trace[k]).
#[verifier::rlimit(50)]
proof fn ete_reachable_N_from_trace_suffix(
  trace: Seq<ComposedState>, cap: nat, tid: TaskId, n: int, k: int,
)
  requires
    0 <= k <= n,
    trace.len() == n + 1,
    crate::framework::module_spec::is_valid_trace(
      crate::composed::spec::progress::composed_module_spec().progress, trace),
    crate::framework::module_spec::env_holds_along(
      crate::composed::spec::progress::composed_module_spec().progress, trace,
      |c: ComposedState, tt: TaskId| env_N(c, tt, cap), tid),
  ensures
    ete_reachable_N(trace[k], trace[n], (n - k) as nat, cap, tid),
{
  let cprog = crate::composed::spec::progress::composed_module_spec().progress;
  let cenv = |c: ComposedState, tt: TaskId| env_N(c, tt, cap);
  let sub: Seq<ComposedState> = trace.subrange(k, n + 1);
  assert(crate::framework::module_spec::env_progress_n(
    cprog, trace[k], trace[n], (n - k) as nat, cenv, tid)) by {
    assert(sub.len() == n - k + 1);
    assert(sub[0] == trace[k]);
    assert(sub[n - k] == trace[n]);
    assert(crate::framework::module_spec::is_valid_trace(cprog, sub)) by {
      assert forall |i: int| #![trigger sub[i]] 0 <= i < sub.len() - 1 implies cprog(sub[i], sub[i + 1]) by {
        assert(sub[i] == trace[k + i] && sub[i + 1] == trace[k + i + 1]);
      };
    };
    assert(crate::framework::module_spec::env_holds_along(cprog, sub, cenv, tid)) by {
      assert forall |i: int| #![trigger sub[i]] 0 <= i < sub.len() implies cenv(sub[i], tid) by {
        assert(sub[i] == trace[k + i]);
      };
    };
  };
}

// The per-state facts new_setwaker_implies_poll consumes along the io trace.
pub open spec fn io_trace_state_facts(
  trace: Seq<ComposedState>, tid: TaskId, rid: ResourceIdView, k: int,
) -> bool {
  crate::composed::spec::progress::composed_well_formed(trace[k]) &&
  crate::composed::spec::alignment::composed_active_rid(trace[k], tid, rid) &&
  trace[k].task_logs.contains_key(tid) &&
  crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(trace[k].reactor_log, rid)
}

// Establish io_trace_state_facts at one trace index k. composed_active_rid(trace[k])
// is derived via the reuse-tolerant no-own-deregister bootstrap: since tid is not
// polled over the window (s→l_x), its task log is UNCHANGED at trace[k] (== s), so
// tid still holds rid (no own-deregister), and composed_active_rid_from_no_dereg
// applies at trace[k]. io_remains_active + wf come from env / trace.
// spinoff_prover: this heavy io proof sits at the SMT ceiling and is perturbed into
// rlimit-timeout by UNRELATED additions elsewhere in the module (function reordering
// shifts Z3's query and tips quantifier instantiation). Running it in its own solver
// instance isolates it from that cross-function nondeterminism (Phase B).
#[verifier::spinoff_prover]
#[verifier::rlimit(120)]
pub proof fn io_trace_facts_at(
  trace: Seq<ComposedState>, s: ComposedState, l_x: ComposedState, tid: TaskId, rid: ResourceIdView,
  t: int, r: int, cap: nat, n: int, k: int,
)
  requires
    0 <= k <= n,
    trace.len() == n + 1,
    trace[0] == s,
    trace[n] == l_x,
    crate::framework::module_spec::is_valid_trace(
      crate::composed::spec::progress::composed_module_spec().progress, trace),
    crate::framework::module_spec::env_holds_along(
      crate::composed::spec::progress::composed_module_spec().progress, trace,
      |c: ComposedState, tt: TaskId| env_N(c, tt, cap), tid),
    crate::composed::spec::progress::composed_well_formed(s),
    env_N(s, tid, cap),
    s.task_logs.contains_key(tid),
    0 <= t < s.task_logs[tid].len(),
    crate::utilities::spec::events::is_register_io(s.task_logs[tid][t]),
    crate::utilities::spec::events::get_resource_id(s.task_logs[tid][t]) == Some(rid),
    0 <= r < s.reactor_log.len(),
    reactor_log::io_syscall_registered_at(s.reactor_log, r),
    crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[r]) == rid,
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[r], s.task_logs[tid][t]),
    !crate::utilities::spec::log::is_io_deregistered_before(
      s.task_logs[tid], rid, s.task_logs[tid].len() as int),
    // t5c: the waiter facts (with last_poll_is_pending below, the io currency
    // guard's witness) — carried to trace[k] to instantiate the GUARDED env clause.
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    ete_reachable_N(s, l_x, n as nat, cap, tid),
    !executor_log::has_poll_task_for_id_after(l_x.executor_log, tid, s.executor_log.len() as int),
  ensures
    io_trace_state_facts(trace, tid, rid, k),
{
  let cprog = crate::composed::spec::progress::composed_module_spec().progress;
  let cenv = |c: ComposedState, tt: TaskId| env_N(c, tt, cap);
  // progress_n(s, trace[k], k) + env_N(trace[k]) from the trace prefix
  ete_reachable_N_from_trace_prefix(trace, s, cap, tid, n, k);
  assert(env_N(trace[k], tid, cap));
  assert(ete_reachable_N(s, trace[k], k as nat, cap, tid));
  crate::composed::proof::end_to_end::progress_n_preserves_wf(s, trace[k], k as nat);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, trace[k], k as nat);
  assert(crate::composed::spec::state::is_extension_of(s, trace[k]));
  assert(trace[k].task_logs.contains_key(tid));
  // t5c: !polled carries down to trace[k] (its executor log is a prefix of l_x's),
  // so tid's task log is UNCHANGED and its last poll is still Pending at trace[k].
  ete_reachable_N_from_trace_suffix(trace, cap, tid, n, k);
  crate::framework::module_spec::env_progress_n_implies_progress_n(
    cprog, trace[k], l_x, (n - k) as nat, cenv, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(trace[k], l_x, (n - k) as nat);
  assert(!executor_log::has_poll_task_for_id_after(
    trace[k].executor_log, tid, s.executor_log.len() as int)) by {
    if executor_log::has_poll_task_for_id_after(
      trace[k].executor_log, tid, s.executor_log.len() as int) {
      let pidx = choose |pidx: int|
        s.executor_log.len() as int <= pidx < trace[k].executor_log.len() &&
        executor_log::is_poll_task_for_id_at(trace[k].executor_log, pidx, tid);
      assert(trace[k].executor_log[pidx] == l_x.executor_log[pidx]);
    }
  };
  not_polled_preserves_pending(s, trace[k], k as nat, cap, tid);
  assert(trace[k].task_logs[tid] =~= s.task_logs[tid]);
  assert(trace[k].task_logs[tid] == s.task_logs[tid]);
  // io_remains_active at trace[k]: instantiate the GUARDED env clause (t5c) with
  // witness tid — currently awaiting rid (io-active + current-poll waker + Pending).
  env_N_implies_env(trace[k], tid, cap);
  env_gives_core_clauses(trace[k], tid);
  io_assumption_here_gives_active(trace[k], tid, rid);
  // register witness (t, r) stable in trace[k]; tid still holds rid ⟹ composed_active_rid
  assert(trace[k].reactor_log[r] == s.reactor_log[r]);
  assert(trace[k].task_logs[tid][t] == s.task_logs[tid][t]);
  composed_active_rid_from_no_dereg(trace[k], tid, rid, t, r);
}

// io bootstrap (t5): a task tid that registered rid and NEVER deregisters it in
// its OWN log owns rid at the reactor level. Any reactor DeregisterIo(rid) after
// tid's registration r would (io dereg-by-owner, on its FIRST occurrence, which is
// io_syscall_active_at(r,·)) be attributable to tid's own task log — contradicting the
// no-own-deregister hypothesis. Replaces the old leftmost-io_remains_active route
// (which silently excluded reuse); reuse-tolerant (constrains only tid's own rid).
#[verifier::rlimit(80)]
proof fn composed_active_rid_from_no_dereg(
  s: ComposedState, tid: TaskId, rid: ResourceIdView, t: int, r: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    0 <= t < s.task_logs[tid].len(),
    crate::utilities::spec::events::is_register_io(s.task_logs[tid][t]),
    crate::utilities::spec::events::get_resource_id(s.task_logs[tid][t]) == Some(rid),
    0 <= r < s.reactor_log.len(),
    reactor_log::io_syscall_registered_at(s.reactor_log, r),
    crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[r]) == rid,
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[r], s.task_logs[tid][t]),
    !crate::utilities::spec::log::is_io_deregistered_before(
      s.task_logs[tid], rid, s.task_logs[tid].len() as int),
  ensures
    crate::composed::spec::alignment::composed_active_rid(s, tid, rid),
{
  let l = s.reactor_log;
  let lp = s.task_logs[tid];
  crate::composed::proof::contract_bridges::composed_wf_implies_reactor_wf(s);
  assert(crate::composed::spec::alignment::has_registered_rid(lp, rid));
  assert forall |jj: int| r < jj < l.len() implies
    !(reactor_log::io_syscall_deregistered_at(l, jj) &&
      crate::reactor::spec::events::get_io_syscall_deregister_rid(l[jj]) == rid) by {
    if reactor_log::io_syscall_deregistered_at(l, jj) &&
       crate::reactor::spec::events::get_io_syscall_deregister_rid(l[jj]) == rid {
      crate::reactor::proof::io_liveness::first_io_dereg_in_props(l, rid, r + 1, l.len() as int, jj);
      let d0 = crate::reactor::proof::io_liveness::first_io_dereg_in(l, rid, r + 1, l.len() as int);
      assert(reactor_log::io_syscall_active_at(l, r, d0));
      assert(crate::composed::spec::alignment::is_task_initiated_reactor_event(l[d0]));
      assert(crate::composed::spec::alignment::reactor_outbound_to_task_exists(s));
      let (tid_d, task_d): (TaskId, int) = choose |tt: TaskId, ti: int|
        s.task_logs.contains_key(tt) && 0 <= ti < s.task_logs[tt].len() &&
        crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(l[d0], s.task_logs[tt][ti]);
      reveal(crate::composed::spec::alignment::succ_deregister_io_by_owner);
      assert(crate::composed::spec::alignment::succ_deregister_io_by_owner(s));
      assert(tid_d == tid);
      assert(crate::utilities::spec::events::is_deregister_io(lp[task_d]));
      assert(crate::utilities::spec::events::get_resource_id(lp[task_d]) == Some(rid));
      assert(crate::utilities::spec::log::is_io_deregistered_before(lp, rid, lp.len() as int));
      assert(false);
    }
  };
  crate::composed::spec::alignment::reveal_composed_active_rid(s, tid, rid, t, r);
}

// Wrapper: from the composed-level active-io-with-waker, extract the io witness
// (register op + matching reactor event) + composed_active_rid + find_last>=0, then
// consume the reactor io contract via composed_io_pending_to_poll_via_contract.
#[verifier::rlimit(100)]
pub proof fn composed_io_pending_to_poll(
  s: ComposedState, l_prime: ComposedState, chunk: nat, cap: nat, tid: TaskId, rid: ResourceIdView,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    env_N(s, tid, cap),
    ete_reachable_N(s, l_prime, chunk, cap, tid),
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    // tid genuinely holds rid: it never deregisters rid in its own log. (Under the
    // reuse-tolerant io_remains_active this is load-bearing — is_io_active alone
    // permits a trailing self-deregister that the old leftmost form excluded.)
    !crate::utilities::spec::log::is_io_deregistered_before(
      s.task_logs[tid], rid, s.task_logs[tid].len() as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    cap >= 1,
    // Phase B (io): +1 for the modeled queue's extra drain tick, +1 for the
    // (get_io_ready_bound + 1)-round wake window (see via_contract).
    chunk > get_io_ready_bound(s, tid) + get_max_queue_length(s) + 2,
  ensures
    executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int),
{
  let last = (s.task_logs[tid].len() - 1) as int;
  crate::composed::proof::contract_bridges::composed_active_io_implies_reactor_trigger(s, rid, tid);
  // find_last >= 0 from trigger_fn
  assert(crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
    s.reactor_log, rid, s.reactor_log.len() as int) >= 0);
  // extract the register op (t) from is_io_active
  let t: int = choose |j: int|
    0 <= j < last &&
    crate::utilities::spec::events::is_register_io(s.task_logs[tid][j]) &&
    crate::utilities::spec::events::get_resource_id(s.task_logs[tid][j]) == Some(rid);
  assert(crate::composed::spec::alignment::is_reactor_operation(s.task_logs[tid][t]));
  // matching reactor event (r) from operation_to_reactor_exists
  let r: int = choose |k: int|
    0 <= k < s.reactor_log.len() &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[k], s.task_logs[tid][t]);
  assert(reactor_log::io_syscall_registered_at(s.reactor_log, r));
  assert(crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[r]) == rid);
  // composed_active_rid via the reuse-tolerant no-own-deregister bootstrap.
  composed_active_rid_from_no_dereg(s, tid, rid, t, r);
  composed_io_pending_to_poll_via_contract(s, l_prime, chunk, cap, tid, rid, t, r);
}

// Pending io poll -> tid POLLED, CONSUMING the reactor io contract. Case-split on
// whether tid is polled: if yes, done; if not, find_last is stable
// (io_not_polled_gives_find_last_stable), so the io contract fires at l_wake
// (composed_io_wake_fires), env wake_routing queues tid, and queue_member (executor
// contract) drains to a poll — which is has_poll after s (satisfies the goal).
// The window wake-delivery step (io), analog of timer_window_delivers_queued: at
// l_wake the io wake has FIRED after the current SetWaker and tid has NOT been
// polled since s (still Pending, task log unchanged), so wake_fired_unconsumed
// holds and env_N's wake_delivers_here routes tid into the runnable FIFO.
#[verifier::rlimit(50)]
proof fn io_window_delivers_queued(
  s: ComposedState, l_wake: ComposedState, w: nat, cap: nat, tid: TaskId, rid: ResourceIdView,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    ete_reachable_N(s, l_wake, w, cap, tid),
    !executor_log::has_poll_task_for_id_after(l_wake.executor_log, tid, s.executor_log.len() as int),
    io_wake_in_current_window(l_wake.reactor_log, rid),
  ensures
    // Phase B (io): tid's owned io WakeTask has FIRED at l_wake (reactor_wake_arrival,
    // io disjunct) — arrival into the MODELED reactor-wake queue. Delivery is DERIVED
    // by the caller via composed_reactor_wake_pending_to_poll.
    crate::composed::spec::wake_queues::reactor_wake_arrival(l_wake, tid),
    l_wake.task_logs.contains_key(tid),
    executor_log::last_poll_is_pending(l_wake.executor_log, tid),
{
  not_polled_preserves_pending(s, l_wake, w, cap, tid);
  let last = (s.task_logs[tid].len() - 1) as int;
  let lastw = (l_wake.task_logs[tid].len() - 1) as int;
  assert(l_wake.task_logs[tid] =~= s.task_logs[tid]);
  assert(lastw == last);
  ete_reachable_N_gives_env_N_at_end(s, l_wake, w, cap, tid);
  // io disjunct of reactor_wake_arrival, witness rid.
  assert(crate::composed::spec::wake_queues::reactor_wake_arrival(l_wake, tid)) by {
    reveal(crate::composed::spec::wake_queues::reactor_wake_arrival);
    assert(l_wake.task_logs[tid] == s.task_logs[tid]);
    assert(crate::utilities::spec::log::is_io_active(l_wake.task_logs[tid], rid, lastw));
    assert(crate::utilities::spec::log::has_waker_set_in_current_poll(l_wake.task_logs[tid], rid, lastw));
    assert(io_wake_in_current_window(l_wake.reactor_log, rid));
  }
}

#[verifier::rlimit(100)]
pub proof fn composed_io_pending_to_poll_via_contract(
  s: ComposedState, l_prime: ComposedState, chunk: nat, cap: nat, tid: TaskId, rid: ResourceIdView, t: int, r: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    env_N(s, tid, cap),
    ete_reachable_N(s, l_prime, chunk, cap, tid),
    s.task_logs.contains_key(tid),
    0 <= t < s.task_logs[tid].len(),
    crate::utilities::spec::events::is_register_io(s.task_logs[tid][t]),
    crate::utilities::spec::events::get_resource_id(s.task_logs[tid][t]) == Some(rid),
    0 <= r < s.reactor_log.len(),
    reactor_log::io_syscall_registered_at(s.reactor_log, r),
    crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[r]) == rid,
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[r], s.task_logs[tid][t]),
    crate::composed::spec::alignment::composed_active_rid(s, tid, rid),
    crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      s.reactor_log, rid, s.reactor_log.len() as int) >= 0,
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    !crate::utilities::spec::log::is_io_deregistered_before(
      s.task_logs[tid], rid, s.task_logs[tid].len() as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    cap >= 1,
    // Phase B (io): +1 for the modeled queue's extra drain tick, +1 because the
    // wake window is get_io_ready_bound + 1 (dedicated io bound, decoupled from cap).
    chunk > get_io_ready_bound(s, tid) + get_max_queue_length(s) + 2,
  ensures
    executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int),
{
  if executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int) {
    return;
  }
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  // wake window: get_io_ready_bound + 1 rounds (>= 1 even when the bound is 0)
  let w: nat = (get_io_ready_bound(s, tid) + 1) as nat;
  ete_reachable_N_split(s, l_prime, w, (chunk - w) as nat, cap, tid);
  let l_wake: ComposedState = choose |l_wake: ComposedState|
    ete_reachable_N(s, l_wake, w, cap, tid) && ete_reachable_N(l_wake, l_prime, (chunk - w) as nat, cap, tid);
  // extension l_wake -> l_prime, for poll persistence + length
  ete_reachable_N_implies_env(l_wake, l_prime, (chunk - w) as nat, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(
    progress, l_wake, l_prime, (chunk - w) as nat, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(l_wake, l_prime, (chunk - w) as nat);
  // !polled over [s, l_wake] (else it persists to l_prime)
  assert(!executor_log::has_poll_task_for_id_after(l_wake.executor_log, tid, s.executor_log.len() as int)) by {
    if executor_log::has_poll_task_for_id_after(l_wake.executor_log, tid, s.executor_log.len() as int) {
      let pidx = choose |pidx: int|
        s.executor_log.len() as int <= pidx < l_wake.executor_log.len() &&
        executor_log::is_poll_task_for_id_at(l_wake.executor_log, pidx, tid);
      assert(l_wake.executor_log[pidx] == l_prime.executor_log[pidx]);
    }
  };
  io_not_polled_gives_find_last_stable(s, l_wake, w, cap, tid, rid, t, r);
  // wake FIRED at l_wake in the current io window (find_last is stable)
  composed_io_wake_fires(s, l_wake, w, cap, tid, rid);
  // tid's owned io WakeTask has fired at l_wake ⟹ tid is in the MODELED reactor-wake queue
  io_window_delivers_queued(s, l_wake, w, cap, tid, rid);
  // s ⊆ l_wake (executor length) for the drain-based delivery
  ete_reachable_N_implies_env(s, l_wake, w, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_wake, w, env, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_wake, w);
  crate::composed::proof::end_to_end::progress_n_preserves_wf(s, l_wake, w);
  assert(0 < l_wake.executor_log.len());
  assert(get_max_queue_length(l_wake) == get_max_queue_length(s));
  // not-polled-since forall at l_wake (tautological: no poll after the last poll)
  crate::composed::proof::end_to_end::last_poll_idx_properties(l_wake.executor_log, tid);
  // DERIVE delivery via the modeled reactor-wake queue + drain step (no wake_delivers_here)
  composed_reactor_wake_pending_to_poll(l_wake, l_prime, (chunk - w) as nat, cap, tid);
}

// The reactor io CONTRACT fires at l_wake: with find_last stable (== sw_s), w >=
// get_io_ready_bound poll-events have accumulated from sw_s, so env_reactor_io's
// readiness holds and io_env_response_at yields the wake. CONSUMES the reactor io
// contract core, at the DEDICATED io bound (decoupled from cap).
#[verifier::rlimit(100)]
pub proof fn composed_io_wake_fires(
  s: ComposedState, l_wake: ComposedState, w: nat, cap: nat, tid: TaskId, rid: ResourceIdView,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    env_N(s, tid, cap),
    ete_reachable_N(s, l_wake, w, cap, tid),
    w >= 1,
    w >= get_io_ready_bound(s, tid),
    cap >= 1,
    crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      s.reactor_log, rid, s.reactor_log.len() as int) >= 0,
    crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      l_wake.reactor_log, rid, l_wake.reactor_log.len() as int) ==
    crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      s.reactor_log, rid, s.reactor_log.len() as int),
    // t5c: waiter facts at s + !polled over the window — carried to l_wake to
    // instantiate the GUARDED io clause there (env_N_gives_env_reactor_io).
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    !executor_log::has_poll_task_for_id_after(l_wake.executor_log, tid, s.executor_log.len() as int),
  ensures
    (crate::reactor::contracts::bounded_io_wakeup::bounded_io_wakeup().fulfillment)(
      l_wake.reactor_log, rid),
    io_wake_in_current_window(l_wake.reactor_log, rid),
{
  let cprog = crate::composed::spec::progress::composed_module_spec().progress;
  let cenv = |c: ComposedState, tt: TaskId| env_N(c, tt, cap);
  let sw_s = crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
    s.reactor_log, rid, s.reactor_log.len() as int);
  ete_reachable_N_gives_env_N_at_end(s, l_wake, w, cap, tid);
  crate::composed::proof::end_to_end::progress_n_preserves_wf(s, l_wake, w);
  not_polled_preserves_pending(s, l_wake, w, cap, tid);
  assert(l_wake.task_logs[tid] =~= s.task_logs[tid]);
  assert(l_wake.task_logs[tid] == s.task_logs[tid]);
  env_N_gives_env_reactor_io(l_wake, tid, cap, rid);
  // the io bound constant is state-independent (arbitrary()), so it agrees at l_wake
  assert(get_io_ready_bound(l_wake, tid) == get_io_ready_bound(s, tid));
  crate::framework::module_spec::env_progress_n_implies_progress_n(cprog, s, l_wake, w, cenv, tid);
  crate::composed::proof::end_to_end::composed_progress_n_implies_reactor_k_rounds(s, l_wake, w);
  crate::composed::proof::contract_bridges::composed_wf_implies_reactor_wf(s);
  crate::composed::proof::contract_bridges::composed_wf_implies_reactor_wf(l_wake);
  crate::reactor::proof::io_liveness::k_rounds_imply_k_poll_events(s.reactor_log, l_wake.reactor_log, w);
  crate::reactor::proof::io_liveness::find_last_set_waker_returns_succ(
    s.reactor_log, rid, s.reactor_log.len() as int);
  crate::reactor::proof::io_liveness::count_poll_events_split_additive(
    l_wake.reactor_log, sw_s, s.reactor_log.len() as int, l_wake.reactor_log.len() as int);
  crate::reactor::proof::io_liveness::io_env_response_at(
    l_wake.reactor_log, rid, get_io_ready_bound(s, tid));
}

// Crux of the io case-split: if tid is never polled over the trace, find_last is stable
// (no new SetWaker for rid could appear — it would force a poll).
#[verifier::rlimit(100)]
pub proof fn io_not_polled_gives_find_last_stable(
  s: ComposedState, l_x: ComposedState, n: nat, cap: nat, tid: TaskId, rid: ResourceIdView, t: int, r: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    env_N(s, tid, cap),
    ete_reachable_N(s, l_x, n, cap, tid),
    n >= 1,
    s.task_logs.contains_key(tid),
    0 <= t < s.task_logs[tid].len(),
    crate::utilities::spec::events::is_register_io(s.task_logs[tid][t]),
    crate::utilities::spec::events::get_resource_id(s.task_logs[tid][t]) == Some(rid),
    0 <= r < s.reactor_log.len(),
    reactor_log::io_syscall_registered_at(s.reactor_log, r),
    crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[r]) == rid,
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[r], s.task_logs[tid][t]),
    crate::composed::spec::alignment::composed_active_rid(s, tid, rid),
    !crate::utilities::spec::log::is_io_deregistered_before(
      s.task_logs[tid], rid, s.task_logs[tid].len() as int),
    // t5c: waiter facts for the guarded io clause (threaded to io_trace_facts_at).
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    !executor_log::has_poll_task_for_id_after(l_x.executor_log, tid, s.executor_log.len() as int),
  ensures
    crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      l_x.reactor_log, rid, l_x.reactor_log.len() as int) ==
    crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      s.reactor_log, rid, s.reactor_log.len() as int),
{
  let cprog = crate::composed::spec::progress::composed_module_spec().progress;
  let cenv = |c: ComposedState, tt: TaskId| env_N(c, tt, cap);
  let trace: Seq<ComposedState> = choose |trace: Seq<ComposedState>|
    trace.len() == n + 1 && trace.first() == s && trace.last() == l_x &&
    crate::framework::module_spec::is_valid_trace(cprog, trace) &&
    crate::framework::module_spec::env_holds_along(cprog, trace, cenv, tid);
  assert(trace[0] == s && trace[n as int] == l_x);
  // per-state facts, then the four separate foralls new_setwaker_implies_poll needs
  assert forall |k: int| 0 <= k <= n implies #[trigger] io_trace_state_facts(trace, tid, rid, k) by {
    io_trace_facts_at(trace, s, l_x, tid, rid, t, r, cap, n as int, k);
  };
  assert forall |k: int| 0 <= k <= n implies
    #[trigger] crate::composed::spec::progress::composed_well_formed(trace[k]) by {
    assert(io_trace_state_facts(trace, tid, rid, k));
  };
  assert forall |k: int| 0 <= k <= n implies
    crate::composed::spec::alignment::composed_active_rid(#[trigger] trace[k], tid, rid) by {
    assert(io_trace_state_facts(trace, tid, rid, k));
  };
  assert forall |k: int| 0 <= k <= n implies
    crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(
      (#[trigger] trace[k]).reactor_log, rid) by {
    assert(io_trace_state_facts(trace, tid, rid, k));
  };
  assert forall |k: int| 0 <= k <= n implies (#[trigger] trace[k].task_logs).contains_key(tid) by {
    assert(io_trace_state_facts(trace, tid, rid, k));
  };
  crate::framework::module_spec::env_progress_n_implies_progress_n(cprog, s, l_x, n, cenv, tid);
  crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_x, n);
  // No new SetWaker for rid in the window. If one existed at j >= s.len, then
  // p_star = find_last(l_x) >= j >= s.len; p_star is the LAST set-waker for rid,
  // so new_setwaker_implies_poll (which needs exactly the last-set-waker anchor)
  // forces tid to be polled in the window — contradicting !polled.
  assert forall |j: int| s.reactor_log.len() <= j < l_x.reactor_log.len() implies
    !(reactor_log::is_succ_set_waker_at(l_x.reactor_log, j) &&
      crate::reactor::spec::events::get_set_waker_rid(l_x.reactor_log[j]) == rid) by {
    if reactor_log::is_succ_set_waker_at(l_x.reactor_log, j) &&
       crate::reactor::spec::events::get_set_waker_rid(l_x.reactor_log[j]) == rid {
      let p_star = crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
        l_x.reactor_log, rid, l_x.reactor_log.len() as int);
      crate::reactor::proof::io_liveness::find_last_set_waker_ge_match(
        l_x.reactor_log, rid, l_x.reactor_log.len() as int, j);
      crate::reactor::proof::io_liveness::find_last_set_waker_returns_succ(
        l_x.reactor_log, rid, l_x.reactor_log.len() as int);
      crate::reactor::proof::io_liveness::find_last_set_waker_no_later(
        l_x.reactor_log, rid, l_x.reactor_log.len() as int);
      new_setwaker_implies_poll(trace, tid, rid, n as int, p_star);
      assert(executor_log::has_poll_task_for_id_after(
        l_x.executor_log, tid, s.executor_log.len() as int));
    }
  };
  crate::reactor::proof::io_liveness::find_last_stable_no_new_setwaker(
    s.reactor_log, l_x.reactor_log, rid, l_x.reactor_log.len() as int);
}

// io keystone helper (step A): the registration active at the LAST SetWaker for
// rid is owned by tid. reg_star = find_io_syscall_register_for_rid(rid, sw); the reshaped
// io_remains_active gives no-deregister after reg_star ⟹ composed_active_rid for
// reg_star's owner; at_most_one_owner + composed_active_rid(tid) ⟹ owner == tid.
// Returns (task_star, reg_star) witnessing tid owns reg_star.
#[verifier::rlimit(60)]
proof fn keystone_reg_star_owned_by_tid(
  s: ComposedState, tid: TaskId, rid: ResourceIdView, sw: int,
) -> (result: (int, int))
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    crate::composed::spec::alignment::composed_active_rid(s, tid, rid),
    crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(s.reactor_log, rid),
    0 <= sw < s.reactor_log.len(),
    sw == crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      s.reactor_log, rid, s.reactor_log.len() as int),
    reactor_log::is_succ_set_waker_at(s.reactor_log, sw),
    crate::reactor::spec::events::get_set_waker_rid(s.reactor_log[sw]) == rid,
  ensures ({
    let (task_star, reg_star) = result;
    reg_star == crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(
      s.reactor_log, rid, sw) &&
    0 <= reg_star < sw &&
    reactor_log::io_syscall_registered_at(s.reactor_log, reg_star) &&
    crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[reg_star]) == rid &&
    s.task_logs.contains_key(tid) &&
    0 <= task_star < s.task_logs[tid].len() &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[reg_star], s.task_logs[tid][task_star])
  }),
{
  let l = s.reactor_log;
  crate::composed::proof::contract_bridges::composed_wf_implies_reactor_wf(s);
  // reg_star active at sw via set_waker_active_io invariant
  let as_inv = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
  assert(crate::framework::action_safety::action_safety_satisfied(as_inv, l));
  assert((as_inv.acceptance)(l, sw));
  assert((as_inv.validity)(l, sw));
  assert(crate::reactor::invariants::wake_on_io_ready::io_syscall_active_at_set_waker(l, rid, sw));
  let reg_star = crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(l, rid, sw);
  crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid_valid(l, rid, sw);
  assert(0 <= reg_star < sw);
  assert(reactor_log::io_syscall_registered_at(l, reg_star));
  assert(crate::reactor::spec::events::get_io_syscall_register_rid(l[reg_star]) == rid);
  // no dereg of rid after reg_star, directly from reshaped io_remains_active
  // (anchored at reg = find_io_syscall_register_for_rid(rid, find_last) = reg_star).
  assert(reg_star == crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(
    l, rid, crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      l, rid, l.len() as int)));
  assert forall |j: int| reg_star < j < l.len() implies
    !(reactor_log::io_syscall_deregistered_at(l, j) &&
      crate::reactor::spec::events::get_io_syscall_deregister_rid(l[j]) == rid) by {};
  // reg_star has a source op (tid_star, task_star)
  assert(crate::composed::spec::alignment::reactor_registration_to_task_exists(s));
  let (tid_star, task_star): (TaskId, int) = choose |t: TaskId, ti: int|
    s.task_logs.contains_key(t) && 0 <= ti < s.task_logs[t].len() &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(l[reg_star], s.task_logs[t][ti]);
  assert(crate::utilities::spec::events::is_register_io(s.task_logs[tid_star][task_star]));
  assert(crate::utilities::spec::events::get_resource_id(s.task_logs[tid_star][task_star]) == Some(rid));
  assert(crate::composed::spec::alignment::has_registered_rid(s.task_logs[tid_star], rid));
  crate::composed::spec::alignment::reveal_composed_active_rid(s, tid_star, rid, task_star, reg_star);
  assert(crate::composed::spec::alignment::operation_alignment_inv(s));
  crate::composed::proof::rid_uniqueness::rid_uniqueness_from_reactor_safety(s, rid);
  assert(tid_star == tid);
  (task_star, reg_star)
}

// io keystone helper (r_tp < reg_star is absurd): if tid_prime's own registration
// r_tp precedes reg_star, io_reg_uniqueness forces a deregister of rid in
// (r_tp, reg_star); io dereg-by-owner attributes its FIRST such deregister to
// tid_prime's OWN task log, at an index strictly between reg_idx and task_idx —
// contradicting resource_ownership's io_active_before (no own-deregister there).
#[verifier::rlimit(100)]
proof fn keystone_reg_star_reuse_absurd(
  s: ComposedState, tid_prime: TaskId, task_idx: int, rid: ResourceIdView,
  sw: int, reg_star: int, reg_idx: int, r_tp: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    0 <= r_tp < reg_star < sw < s.reactor_log.len(),
    reactor_log::io_syscall_registered_at(s.reactor_log, r_tp),
    crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[r_tp]) == rid,
    reactor_log::io_syscall_registered_at(s.reactor_log, reg_star),
    crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[reg_star]) == rid,
    s.task_logs.contains_key(tid_prime),
    0 <= reg_idx < task_idx < s.task_logs[tid_prime].len(),
    crate::utilities::spec::events::is_register_io(s.task_logs[tid_prime][reg_idx]),
    crate::utilities::spec::events::get_resource_id(s.task_logs[tid_prime][reg_idx]) == Some(rid),
    crate::utilities::spec::events::is_set_waker(s.task_logs[tid_prime][task_idx]),
    !(exists |k: int| reg_idx < k < task_idx &&
        crate::utilities::spec::events::is_deregister_io(s.task_logs[tid_prime][k]) &&
        crate::utilities::spec::events::get_resource_id(s.task_logs[tid_prime][k]) == Some(rid)),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[r_tp], s.task_logs[tid_prime][reg_idx]),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[sw], s.task_logs[tid_prime][task_idx]),
  ensures false,
{
  let l = s.reactor_log;
  let lp = s.task_logs[tid_prime];
  crate::composed::proof::contract_bridges::composed_wf_implies_reactor_wf(s);
  // io_reg_uniqueness at reg_star: r_tp (a prior register) has a dereg in (r_tp, reg_star)
  let iru = crate::reactor::invariants::io_reg_uniqueness::io_reg_uniqueness();
  assert(crate::framework::action_safety::action_safety_satisfied(iru, l));
  assert((iru.acceptance)(l, reg_star));
  assert((iru.validity)(l, reg_star));
  crate::reactor::invariants::io_reg_uniqueness::reveal_no_prior_io_syscall_registration(l, rid, reg_star);
  let w: int = choose |j: int|
    r_tp < j < reg_star &&
    reactor_log::io_syscall_deregistered_at(l, j) &&
    crate::reactor::spec::events::get_io_syscall_deregister_rid(l[j]) == rid;
  // first dereg d0 after r_tp
  crate::reactor::proof::io_liveness::first_io_dereg_in_props(l, rid, r_tp + 1, reg_star, w);
  let d0 = crate::reactor::proof::io_liveness::first_io_dereg_in(l, rid, r_tp + 1, reg_star);
  assert(r_tp + 1 <= d0 < reg_star);
  assert(reactor_log::io_syscall_deregistered_at(l, d0));
  assert(crate::reactor::spec::events::get_io_syscall_deregister_rid(l[d0]) == rid);
  assert(reactor_log::io_syscall_active_at(l, r_tp, d0));
  // d0 has a source op (tid_d, task_d); io dereg-by-owner ⟹ tid_d == tid_prime
  assert(crate::composed::spec::alignment::is_task_initiated_reactor_event(l[d0]));
  assert(crate::composed::spec::alignment::reactor_outbound_to_task_exists(s));
  let (tid_d, task_d): (TaskId, int) = choose |t: TaskId, ti: int|
    s.task_logs.contains_key(t) && 0 <= ti < s.task_logs[t].len() &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(l[d0], s.task_logs[t][ti]);
  reveal(crate::composed::spec::alignment::succ_deregister_io_by_owner);
  assert(crate::composed::spec::alignment::succ_deregister_io_by_owner(s));
  assert(tid_d == tid_prime);
  assert(crate::utilities::spec::events::is_deregister_io(lp[task_d]));
  assert(crate::utilities::spec::events::get_resource_id(lp[task_d]) == Some(rid));
  assert(crate::composed::spec::alignment::is_reactor_operation(lp[task_d]));
  assert(crate::composed::spec::alignment::is_reactor_operation(lp[reg_idx]));
  assert(crate::composed::spec::alignment::is_reactor_operation(lp[task_idx]));
  // converse monotonicity: reg_idx < task_d (register vs dereg ⟹ distinct)
  assert(reg_idx != task_d);
  if reg_idx > task_d {
    crate::composed::spec::alignment::monotonic_alignment_use(s, tid_prime, task_d, reg_idx, d0, r_tp);
    assert(false);
  }
  assert(reg_idx < task_d);
  // converse monotonicity: task_d < task_idx (dereg vs set_waker ⟹ distinct)
  assert(task_d != task_idx) by {
    if task_d == task_idx {
      assert(crate::utilities::spec::events::is_deregister_io(lp[task_idx]));
      assert(crate::utilities::spec::events::is_set_waker(lp[task_idx]));
    }
  };
  if task_d > task_idx {
    crate::composed::spec::alignment::monotonic_alignment_use(s, tid_prime, task_idx, task_d, sw, d0);
    assert(false);
  }
  assert(task_d < task_idx);
  // task_d ∈ (reg_idx, task_idx) is an own-deregister of rid — contradicts io_active_before
  assert(reg_idx < task_d < task_idx &&
    crate::utilities::spec::events::is_deregister_io(lp[task_d]) &&
    crate::utilities::spec::events::get_resource_id(lp[task_d]) == Some(rid));
  assert(false);
}

// io keystone helper (step B): tid_prime — the task whose SetWaker maps to the
// LAST reactor SetWaker sw for rid — owns reg_star. Via resource_ownership its own
// register r_tp precedes sw; find_io_syscall_register_for_rid_ge ⟹ r_tp <= reg_star; the
// r_tp < reg_star case is absurd (above); r_tp == reg_star ⟹ reactor_to_operation
// _unique ⟹ tid_prime == tid_star.
#[verifier::rlimit(100)]
proof fn keystone_tp_owns_reg_star(
  s: ComposedState, tid_prime: TaskId, task_idx: int, rid: ResourceIdView,
  sw: int, reg_star: int, tid_star: TaskId, task_star: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    0 <= sw < s.reactor_log.len(),
    reg_star == crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(s.reactor_log, rid, sw),
    0 <= reg_star < sw,
    reactor_log::io_syscall_registered_at(s.reactor_log, reg_star),
    crate::reactor::spec::events::get_io_syscall_register_rid(s.reactor_log[reg_star]) == rid,
    s.task_logs.contains_key(tid_star),
    0 <= task_star < s.task_logs[tid_star].len(),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[reg_star], s.task_logs[tid_star][task_star]),
    s.task_logs.contains_key(tid_prime),
    0 <= task_idx < s.task_logs[tid_prime].len(),
    crate::utilities::spec::events::is_set_waker(s.task_logs[tid_prime][task_idx]),
    crate::utilities::spec::events::get_resource_id(s.task_logs[tid_prime][task_idx]) == Some(rid),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[sw], s.task_logs[tid_prime][task_idx]),
  ensures
    tid_prime == tid_star,
{
  let l = s.reactor_log;
  let lp = s.task_logs[tid_prime];
  crate::composed::proof::contract_bridges::composed_wf_implies_reactor_wf(s);
  // resource_ownership: tp's set_waker ⟹ io_active_before ⟹ own register reg_idx
  let ro = crate::utilities::invariants::resource_ownership::resource_ownership();
  assert(crate::framework::action_safety::action_safety_satisfied(ro, lp));
  assert((ro.acceptance)(lp, task_idx));
  assert((ro.validity)(lp, task_idx));
  assert(crate::utilities::invariants::resource_ownership::io_active_before(lp, rid, task_idx));
  let reg_idx: int = choose |j: int|
    0 <= j < task_idx &&
    crate::utilities::spec::events::is_register_io(lp[j]) &&
    crate::utilities::spec::events::get_resource_id(lp[j]) == Some(rid) &&
    !(exists |k: int| j < k < task_idx &&
        crate::utilities::spec::events::is_deregister_io(lp[k]) &&
        crate::utilities::spec::events::get_resource_id(lp[k]) == Some(rid));
  assert(crate::composed::spec::alignment::is_reactor_operation(lp[reg_idx]));
  assert(crate::composed::spec::alignment::operation_to_reactor_exists(s));
  let r_tp: int = choose |k: int|
    0 <= k < l.len() &&
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(l[k], lp[reg_idx]);
  assert(reactor_log::io_syscall_registered_at(l, r_tp));
  assert(crate::reactor::spec::events::get_io_syscall_register_rid(l[r_tp]) == rid);
  assert(crate::composed::spec::alignment::is_reactor_operation(lp[task_idx]));
  // monotonic: reg_idx < task_idx ⟹ r_tp < sw
  crate::composed::spec::alignment::monotonic_alignment_use(s, tid_prime, reg_idx, task_idx, r_tp, sw);
  assert(r_tp < sw);
  // reg_star is the largest register < sw ⟹ r_tp <= reg_star
  crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid_ge(l, rid, sw, r_tp);
  assert(r_tp <= reg_star);
  if r_tp == reg_star {
    assert(crate::composed::spec::alignment::reactor_to_operation_unique(s));
    assert(tid_prime == tid_star);
  } else {
    keystone_reg_star_reuse_absurd(s, tid_prime, task_idx, rid, sw, reg_star, reg_idx, r_tp);
  }
}

// Ownership crux for the io find_last link (REUSE-TOLERANT, t5): given tid owns
// rid (composed_active_rid) and the reshaped io_remains_active, a task tid_prime
// whose SetWaker maps to the LAST reactor SetWaker for rid IS tid. Combines the
// two helpers: reg_star (active at the last set-waker) is owned by tid, and
// tid_prime owns reg_star ⟹ tid_prime == tid. Load-bearing hyp (vs the old
// leftmost form): the set-waker is the LAST one — stale set-wakers by other tasks
// are (correctly) not covered; the consumer only invokes it for find_last.
pub proof fn setwaker_op_owner_is_tid(
  s: ComposedState, tid: TaskId, tid_prime: TaskId, task_idx: int, rid: ResourceIdView,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    crate::composed::spec::alignment::composed_active_rid(s, tid, rid),
    crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(s.reactor_log, rid),
    crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
      s.reactor_log, rid, s.reactor_log.len() as int) >= 0,
    s.task_logs.contains_key(tid_prime),
    0 <= task_idx < s.task_logs[tid_prime].len(),
    crate::utilities::spec::events::is_set_waker(s.task_logs[tid_prime][task_idx]),
    crate::utilities::spec::events::get_resource_id(s.task_logs[tid_prime][task_idx]) == Some(rid),
    // tid_prime's SetWaker maps to the LAST reactor SetWaker for rid.
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
        s.reactor_log, rid, s.reactor_log.len() as int)],
      s.task_logs[tid_prime][task_idx]),
  ensures
    tid_prime == tid,
{
  let l = s.reactor_log;
  let sw = crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
    l, rid, l.len() as int);
  crate::reactor::proof::io_liveness::find_last_set_waker_returns_succ(l, rid, l.len() as int);
  assert(0 <= sw < l.len());
  assert(reactor_log::is_succ_set_waker_at(l, sw));
  assert(crate::reactor::spec::events::get_set_waker_rid(l[sw]) == rid);
  let (task_star, reg_star) = keystone_reg_star_owned_by_tid(s, tid, rid, sw);
  keystone_tp_owns_reg_star(s, tid_prime, task_idx, rid, sw, reg_star, tid, task_star);
}

// Per-state io projection: env_N at a composed state gives the reactor module's
// env_reactor_io at that reactor_log, at the DEDICATED io bound get_io_ready_bound
// (not cap). io_remains_active + count-conditional readiness
// come from env_N (contract_io_assumption_here + io_ready_forward_here); io_active +
// is_succ at the latest SetWaker come from reactor_inv (set_waker_active_io invariant
// + find_last_set_waker_returns_succ). Bridge for composed to consume the io contract.
pub proof fn env_N_gives_env_reactor_io(s: ComposedState, tid: TaskId, cap: nat, rid: ResourceIdView)
  requires
    env_N(s, tid, cap),
    crate::composed::spec::progress::composed_well_formed(s),
    // t5c: the guarded io clause obliges only currently-awaited rids — supply
    // the current-waiter witness facts for tid/rid.
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
  ensures
    crate::reactor::proof::io_liveness::env_reactor_io(
      s.reactor_log, rid, get_io_ready_bound(s, tid)),
{
  crate::composed::proof::contract_bridges::composed_wf_implies_reactor_wf(s);
  env_N_implies_env(s, tid, cap);
  env_gives_core_clauses(s, tid);
  io_assumption_here_gives_active(s, tid, rid);
  assert(io_ready_forward_here(s.reactor_log, rid, get_io_ready_bound(s, tid)));
  let sw = crate::reactor::contracts::bounded_io_wakeup::find_last_set_waker_for_rid(
    s.reactor_log, rid, s.reactor_log.len() as int);
  if sw >= 0 {
    crate::reactor::proof::io_liveness::find_last_set_waker_returns_succ(
      s.reactor_log, rid, s.reactor_log.len() as int);
    let as_inv = crate::reactor::invariants::set_waker_active_io::set_waker_active_io();
    assert(crate::framework::action_safety::action_safety_satisfied(as_inv, s.reactor_log));
    assert((as_inv.acceptance)(s.reactor_log, sw));
    assert((as_inv.validity)(s.reactor_log, sw));
    assert(crate::reactor::spec::events::get_set_waker_rid(s.reactor_log[sw]) == rid);
    assert(crate::reactor::contracts::bounded_io_wakeup::io_syscall_active_at_set_waker(s.reactor_log, rid, sw));
    // Cancellation-guard bridge: io_remains_active forbids any dereg of rid after
    // the registration reg < sw, so in particular none strictly after sw.
    let reg = crate::reactor::invariants::wake_on_io_ready::find_io_syscall_register_for_rid(s.reactor_log, rid, sw);
    assert(reg >= 0 && reg < sw);
    assert forall |j: int| sw < j < s.reactor_log.len() implies
      !(reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
        crate::reactor::spec::events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid) by {
      assert(reg < j < s.reactor_log.len());
    };
    assert(!(exists |j: int|
        sw < j < s.reactor_log.len() &&
        #[trigger] reactor_log::io_syscall_deregistered_at(s.reactor_log, j) &&
        crate::reactor::spec::events::get_io_syscall_deregister_rid(s.reactor_log[j]) == rid));
  }
}

// Composed timer-wake fulfillment: a pending task with a timer registered at s,
// driven k >= timer_concrete_bound rounds to l_wake (with one-further l' for the
// active-coverage), gets its reactor wake FULFILLED at l_wake — entirely from env
// (no forall-ext timer_assumption). Feeds env_timer_wake_general_at via the composed
// bridges. This is the composed-level reactor wake.
pub proof fn composed_env_timer_fulfillment(
  s: ComposedState, l_wake: ComposedState, l_prime: ComposedState,
  k: nat, n2: nat, cap: nat, tid: TaskId, rid: ResourceIdView, i: int, t: int,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    s.task_logs.contains_key(tid),
    executor_log::last_poll_is_pending(s.executor_log, tid),
    0 <= i < s.reactor_log.len(),
    reactor_log::is_succ_register_timer_at(s.reactor_log, i),
    crate::reactor::spec::events::get_register_timer_rid(s.reactor_log[i]) == rid,
    0 <= t < s.task_logs[tid].len(),
    crate::utilities::spec::events::is_register_timer(s.task_logs[tid][t]),
    crate::utilities::spec::log::in_current_poll_cycle(
      s.task_logs[tid], t, (s.task_logs[tid].len() - 1) as int),
    crate::composed::spec::alignment::succ_reactor_event_matches_task_operation(
      s.reactor_log[i], s.task_logs[tid][t]),
    ete_reachable_N(s, l_wake, k, cap, tid),
    ete_reachable_N(l_wake, l_prime, n2, cap, tid),
    ete_reachable_N(s, l_prime, (k + n2) as nat, cap, tid),
    !executor_log::has_poll_task_for_id_after(l_wake.executor_log, tid, s.executor_log.len() as int),
    k >= crate::reactor::proof::timer_liveness::timer_concrete_bound_at(s.reactor_log, i),
    k >= 1,
    n2 >= 1,
  ensures
    crate::reactor::contracts::bounded_timer_wakeup::response_at(l_wake.reactor_log, i),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  crate::composed::proof::contract_bridges::composed_wf_implies_reactor_wf(s);
  // reactor_inv(l_wake) + s.reactor ⊆ l_wake.reactor, strict length
  ete_reachable_N_implies_env(s, l_wake, k, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_wake, k, env, tid);
  crate::composed::proof::end_to_end::progress_n_preserves_wf(s, l_wake, k);
  crate::composed::proof::contract_bridges::composed_wf_implies_reactor_wf(l_wake);
  crate::composed::proof::end_to_end::composed_progress_n_implies_reactor_k_rounds(s, l_wake, k);
  crate::reactor::proof::round_extension::extends_by_k_rounds_implies_prefix(s.reactor_log, l_wake.reactor_log, k);
  crate::reactor::proof::round_extension::k_rounds_len_growth(s.reactor_log, l_wake.reactor_log, k);
  // timestamps at l_wake
  ete_reachable_N_gives_env_N_at_end(s, l_wake, k, cap, tid);
  env_N_implies_env(l_wake, tid, cap);
  env_gives_core_clauses(l_wake, tid);
  // not-deregistered at the fixed i through l_wake (from weakened A4' via witness t)
  env_reactor_timer_active_between_at(s, l_wake, k, cap, tid, i, t);
  // i-keyed core wake lemma: i's own waker fires by l_wake ⇒ response_at(l_wake, i)
  crate::reactor::proof::timer_liveness::env_timer_wake_general_at(
    s.reactor_log, l_wake.reactor_log, i, k);
}



// t5c: establish the io currency guard from a concrete current-waiter witness tid.
#[verifier::rlimit(50)]
pub proof fn io_rid_current_poll_awaited_from_witness(
  s: ComposedState, tid: TaskId, rid: ResourceIdView,
)
  requires
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
  ensures
    crate::composed::spec::assumptions::io_rid_current_poll_awaited(s, rid),
{
  reveal(crate::composed::spec::assumptions::io_rid_current_poll_awaited);
}

// io analogue: env's io_assumption_here supplies the io fact the io wake path
// needs — io_remains_active_assumption (not deregistered after register). Parallel to
// timer_assumption_here_gives_active; keeps the io wake case env-fed.
// t5c: takes the composed state + current-waiter witness tid (is_io_active +
// current-poll waker + Pending) to instantiate the GUARDED env clause.
#[verifier::rlimit(50)]
pub proof fn io_assumption_here_gives_active(s: ComposedState, tid: TaskId, rid: ResourceIdView)
  requires
    contract_io_assumption_here(s),
    s.task_logs.contains_key(tid),
    crate::utilities::spec::log::is_io_active(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    crate::utilities::spec::log::has_waker_set_in_current_poll(
      s.task_logs[tid], rid, (s.task_logs[tid].len() - 1) as int),
    executor_log::last_poll_is_pending(s.executor_log, tid),
  ensures
    crate::reactor::contracts::bounded_io_wakeup::io_remains_active_assumption(s.reactor_log, rid),
{
  io_rid_current_poll_awaited_from_witness(s, tid, rid);
  assert(io_assumption_here(s.reactor_log, rid));
}

pub proof fn spawned_implies_in_fifo(l: crate::executor::spec::log::Log, tid: TaskId)
  requires
    crate::composed::spec::contract::task_spawned_in(l, tid),
  ensures
    exists |enter_idx: int| 0 < enter_idx <= l.len()
      && #[trigger] crate::composed::proof::end_to_end::tid_in_fifo_queue_at(l, enter_idx, tid),
{
  let i: int = choose |i: int|
    0 <= i < l.len() &&
    crate::executor::spec::log::is_pop_injection_at(l, i) &&
    crate::executor::spec::events::get_pop_injection_task(l[i]).is_some() &&
    crate::executor::spec::events::get_pop_injection_task(l[i]).unwrap().id == tid;
  crate::executor::proof::bounded_injection_poll::pop_injection_adds_to_queue(l, i, tid);
  assert(crate::composed::proof::end_to_end::tid_in_fifo_queue_at(l, i + 1, tid));
  assert(0 < i + 1 <= l.len());
}

// MAJOR piece, fully env-sourced: tid already in the runnable FIFO queue at s +
// n > C env_N-good steps ⟹ tid is polled by l'. Reuses the assumption-FREE
// progress_yields_polled_or_count (n steps ⟹ polled OR count ≥ n) and, in the
// count≥n>C branch, the re-plumbed fifo_member_eventually_polled_b with the
// uniform C. No external_assumptions anywhere.
pub proof fn queue_member_eventually_polled_on_trace(
  s: ComposedState, l_prime: ComposedState, n: nat, cap: nat, tid: TaskId,
)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    ete_reachable_N(s, l_prime, n, cap, tid),
    0 < s.executor_log.len(),
    crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
      s.executor_log, s.executor_log.len() as int, tid),
    n > get_max_queue_length(s),
  ensures
    executor_log::has_poll_task_for_id_after(l_prime.executor_log, tid, s.executor_log.len() as int),
{
  // CONSUME the executor's env-form drainage contract:
  // env_progress_n ⟹ executor progress_n; env's single-state queue bound gives
  // queue_bound_at; the module lemma drains the queued tid to a poll.
  let ms = crate::composed::spec::progress::composed_module_spec();
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  ete_reachable_N_implies_env(s, l_prime, n, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(ms.progress, s, l_prime, n, env, tid);
  crate::composed::proof::contract_bridges::composed_progress_n_implies_executor_progress_n(s, l_prime, n);
  crate::composed::proof::end_to_end::progress_n_preserves_wf(s, l_prime, n);
  assert(crate::executor::invariants::executor_inv(s.executor_log));
  assert(crate::executor::invariants::executor_inv(l_prime.executor_log));
  trace_reachable_gives_clauses_at_end(s, l_prime, n, tid);
  queue_length_bounded_gives_queue_bound_at(l_prime);
  assert(get_max_queue_length(l_prime) == get_max_queue_length(s));
  // Attest the executor's bounded_liveness_env drainage contract, then consume its
  // bound-explicit response for the concrete endpoint.
  crate::executor::proof::bounded_liveness::executor_drain_satisfies_liveness_env(
    s.executor_log, get_max_queue_length(l_prime));
  crate::executor::proof::bounded_liveness::executor_drain_env_response_within(
    s.executor_log, l_prime.executor_log, tid, get_max_queue_length(l_prime), n);
}

// env's queue_length_bounded(s) IS queue_bound_at(s.executor_log, C) with the
// uniform constant C = get_max_queue_length(s) — same forall, so the executor
// FIFO lemma (fifo_member_eventually_polled_b) applies with b = C from env.
pub proof fn queue_length_bounded_gives_queue_bound_at(s: ComposedState)
  requires
    queue_length_bounded(s),
  ensures
    crate::executor::proof::queue_bound_single_state::queue_bound_at(
      s.executor_log, get_max_queue_length(s)),
{
}

// From an env-good trace to l', all 17 single-state clauses hold at l' (env at
// endpoint + projection). The `_here` clauses are exactly the single-state facts
// the scheduling proof uses at each reached state, so this is the env-sourced
// replacement for the (vacuous) assumption_persists + assumption_for_self chain.
pub proof fn trace_reachable_gives_clauses_at_end(s: ComposedState, l_prime: ComposedState, n: nat, tid: TaskId)
  requires
    ete_trace_reachable(s, l_prime, n, tid),
  ensures
    timestamps_strictly_increasing(l_prime.reactor_log),
    crate::reactor::timestamps_positive(l_prime.reactor_log),
    timer_deadline_gap_bounded(l_prime, tid),
    timer_resources_remain_active(l_prime),
    queue_length_bounded(l_prime),
    executor_log::tid_unique(l_prime.executor_log, tid),
    contract_io_assumption_here(l_prime),
{
  trace_reachable_gives_env_at_end(s, l_prime, n, tid);
  env_gives_core_clauses(l_prime, tid);
}

// ---- Piece (II): the trace goal — every env-good n-step continuation polls tid ----
pub open spec fn ete_trace_reaches_goal(s: ComposedState, tid: TaskId, n: nat) -> bool {
  forall |l2: ComposedState| #[trigger] ete_trace_reachable(s, l2, n, tid)
    ==> crate::composed::spec::contract::end_to_end_response(l2, tid)
}

// (II), trivial case: if tid is ALREADY polled-to-ready at s, the goal holds for
// every n — readiness persists to every continuation. (The hard case is when tid
// is not yet ready at s; that is the direct filtered response still to prove.)
pub proof fn ete_trace_reaches_goal_when_already_ready(s: ComposedState, tid: TaskId, n: nat)
  requires
    crate::composed::spec::contract::end_to_end_response(s, tid),
  ensures
    ete_trace_reaches_goal(s, tid, n),
{
  let ms = crate::composed::spec::progress::composed_module_spec();
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  assert forall |l2: ComposedState| #[trigger] ete_trace_reachable(s, l2, n, tid)
    implies crate::composed::spec::contract::end_to_end_response(l2, tid) by {
    crate::framework::module_spec::env_progress_n_implies_progress_n(ms.progress, s, l2, n, env, tid);
    crate::composed::proof::end_to_end::progress_n_implies_extension(s, l2, n);
    crate::composed::proof::end_to_end::task_polled_to_ready_persists(
      s.executor_log, l2.executor_log, tid);
  };
}

// count_polls_for_tid is monotone under prefix extension.
pub proof fn count_polls_prefix_monotone(a: crate::executor::spec::log::Log, b: crate::executor::spec::log::Log, tid: TaskId)
  requires
    crate::executor::spec::log::is_prefix_of(a, b),
  ensures
    count_polls_for_tid(a, tid) <= count_polls_for_tid(b, tid),
  decreases b.len(),
{
  if b.len() == 0 {
  } else if b.len() == a.len() {
    assert(a =~= b);
  } else {
    let b_pre = b.subrange(0, b.len() - 1);
    assert(crate::executor::spec::log::is_prefix_of(a, b_pre)) by {
      assert(a =~= b.subrange(0, a.len() as int));
      assert(a =~= b_pre.subrange(0, a.len() as int));
    };
    count_polls_prefix_monotone(a, b_pre, tid);
  }
}

// A poll for tid at some index >= s.len() in the extension strictly increments
// the poll count — the per-chunk count growth for the completion loop.
pub proof fn count_polls_grows_with_new_poll(
  s_exec: crate::executor::spec::log::Log, l_exec: crate::executor::spec::log::Log, tid: TaskId, poll_idx: int)
  requires
    crate::executor::spec::log::is_prefix_of(s_exec, l_exec),
    s_exec.len() <= poll_idx < l_exec.len(),
    crate::executor::spec::log::is_poll_task_for_id_at(l_exec, poll_idx, tid),
  ensures
    count_polls_for_tid(l_exec, tid) > count_polls_for_tid(s_exec, tid),
  decreases l_exec.len(),
{
  let l_pre = l_exec.subrange(0, l_exec.len() - 1);
  if poll_idx == l_exec.len() - 1 {
    count_polls_prefix_monotone(s_exec, l_pre, tid);
  } else {
    assert(crate::executor::spec::log::is_prefix_of(s_exec, l_pre)) by {
      assert(s_exec =~= l_exec.subrange(0, s_exec.len() as int));
      assert(s_exec =~= l_pre.subrange(0, s_exec.len() as int));
    };
    assert(l_pre[poll_idx] == l_exec[poll_idx]);
    count_polls_grows_with_new_poll(s_exec, l_pre, tid, poll_idx);
  }
}

// Entry: an ARRIVING task (in the injection queue) gets its FIRST poll. First
// step spawns tid (task_delivered_next_tick); spawned_implies_in_fifo puts it in
// the runnable FIFO; tid_survives_or_polled_in_range says it is either already
// polled in that tick or still in the FIFO at the step end — in which case
// queue_member drains it to a poll. Assumption-free (the executor spawn+drain is
// modeled).
pub proof fn composed_arrival_to_poll(s: ComposedState, l_prime: ComposedState, n: nat, cap: nat, tid: TaskId)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    crate::composed::spec::contract::end_to_end_arrival(s, tid),
    ete_reachable_N(s, l_prime, n, cap, tid),
    n >= 1,
    (n - 1) as nat > get_max_queue_length(s),
  ensures
    crate::executor::spec::log::has_poll_for_id(l_prime.executor_log, tid),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  ete_reachable_N_split(s, l_prime, 1, (n - 1) as nat, cap, tid);
  let s1: ComposedState = choose |s1: ComposedState|
    ete_reachable_N(s, s1, 1, cap, tid) && ete_reachable_N(s1, l_prime, (n - 1) as nat, cap, tid);
  // composed_progress(s, s1)
  ete_reachable_N_implies_env(s, s1, 1, cap, tid);
  crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, s1, 1, env, tid);
  assert(crate::composed::spec::progress::composed_progress(s, s1)) by {
    let tr: Seq<ComposedState> = choose |tr: Seq<ComposedState>|
      tr.len() == 2 && tr.first() == s && tr.last() == s1 &&
      crate::framework::module_spec::is_valid_trace(progress, tr);
    assert((progress)(tr[0], tr[1]));
    assert(tr[0] == s && tr[1] == s1);
  };
  // arrival ⟹ spawned at s1
  assert(crate::composed::spec::contract::task_spawned_in(s1.executor_log, tid));
  spawned_implies_in_fifo(s1.executor_log, tid);
  let enter_idx: int = choose |ei: int| 0 < ei <= s1.executor_log.len()
    && crate::composed::proof::end_to_end::tid_in_fifo_queue_at(s1.executor_log, ei, tid);
  crate::composed::proof::end_to_end::progress_n_preserves_wf(s, s1, 1);
  crate::composed::proof::end_to_end::tid_survives_or_polled_in_range(
    s1.executor_log, tid, enter_idx, s1.executor_log.len() as int);
  if exists |pidx: int| enter_idx <= pidx < s1.executor_log.len()
    && crate::executor::spec::log::is_poll_task_for_id_at(s1.executor_log, pidx, tid) {
    // already polled in the spawn tick — persists to l' (prefix)
    let pidx: int = choose |pidx: int| enter_idx <= pidx < s1.executor_log.len()
      && crate::executor::spec::log::is_poll_task_for_id_at(s1.executor_log, pidx, tid);
    ete_reachable_N_implies_env(s1, l_prime, (n - 1) as nat, cap, tid);
    crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s1, l_prime, (n - 1) as nat, env, tid);
    crate::composed::proof::end_to_end::progress_n_implies_extension(s1, l_prime, (n - 1) as nat);
    assert(crate::executor::spec::log::is_prefix_of(s1.executor_log, l_prime.executor_log));
    assert(s1.executor_log[pidx] == l_prime.executor_log[pidx]);
  } else {
    // still in FIFO at s1's end — queue_member drains it
    assert(crate::composed::proof::end_to_end::tid_in_fifo_queue_at(
      s1.executor_log, s1.executor_log.len() as int, tid));
    assert(0 < s1.executor_log.len());
    assert(get_max_queue_length(s1) == get_max_queue_length(s));
    queue_member_eventually_polled_on_trace(s1, l_prime, (n - 1) as nat, cap, tid);
  }
}

// Completion wiring: a once-polled task reaches the env_N goal at n = cap*chunk.
// For every env_N-good n-step continuation l': uniform_chunks(cap chunks) gives
// Ready or count >= count(s)+cap >= cap; in the latter, cap_polls_gives_ready
// (env_N at l') gives Ready. So every continuation reaches Ready.
pub proof fn ete_reaches_goal_N_from_polled(s: ComposedState, tid: TaskId, cap: nat, chunk: nat)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    crate::executor::spec::log::has_poll_for_id(s.executor_log, tid),
    chunk > get_max_timer_deadline_gap(s, tid) + get_io_ready_bound(s, tid)
      + cap + get_max_queue_length(s) + 1,
    cap >= 1,
  ensures
    ete_reaches_goal_N(s, tid, cap, (cap * chunk) as nat),
{
  assert forall |l2: ComposedState| #[trigger] ete_reachable_N(s, l2, (cap * chunk) as nat, cap, tid)
    implies crate::composed::spec::contract::end_to_end_response(l2, tid) by {
    uniform_chunks(s, l2, tid, cap, cap, chunk);
    if !crate::composed::spec::contract::end_to_end_response(l2, tid) {
      assert(count_polls_for_tid(l2.executor_log, tid) >= count_polls_for_tid(s.executor_log, tid) + cap);
      ete_reachable_N_gives_env_N_at_end(s, l2, (cap * chunk) as nat, cap, tid);
      cap_polls_gives_ready(l2, tid, cap);
    }
  };
}

// The completion loop (uniform): from a once-polled task, driving j chunks (each
// chunk > C steps) either reaches Ready or accumulates j more polls. Each chunk:
// not-ready ⟹ pending (last_pending_poll_from_count) ⟹ composed_pending_to_poll
// gives a distinct new poll ⟹ count strictly grows; recurse. No per-source
// dispatch, no timer-bound arithmetic — the uniform wake_delivers_here handles it.
pub proof fn uniform_chunks(s: ComposedState, l_prime: ComposedState, tid: TaskId, cap: nat, j: nat, chunk: nat)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    crate::executor::spec::log::has_poll_for_id(s.executor_log, tid),
    ete_reachable_N(s, l_prime, (j * chunk) as nat, cap, tid),
    chunk > get_max_timer_deadline_gap(s, tid) + get_io_ready_bound(s, tid)
      + cap + get_max_queue_length(s) + 1,
    cap >= 1,
  ensures
    crate::composed::spec::contract::end_to_end_response(l_prime, tid) ||
    count_polls_for_tid(l_prime.executor_log, tid) >= count_polls_for_tid(s.executor_log, tid) + j,
  decreases j,
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  if j == 0 {
    assert((j * chunk) == 0) by (nonlinear_arith) requires j == 0nat {};
    ete_reachable_N_implies_env(s, l_prime, 0, cap, tid);
    crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_prime, 0, env, tid);
    crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_prime, 0);
    assert(s.executor_log =~= l_prime.executor_log);
  } else if crate::composed::spec::contract::end_to_end_response(s, tid) {
    ete_reachable_N_implies_env(s, l_prime, (j * chunk) as nat, cap, tid);
    crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, l_prime, (j * chunk) as nat, env, tid);
    crate::composed::proof::end_to_end::progress_n_implies_extension(s, l_prime, (j * chunk) as nat);
    crate::composed::proof::end_to_end::task_polled_to_ready_persists(s.executor_log, l_prime.executor_log, tid);
  } else {
    crate::composed::proof::end_to_end::last_pending_poll_from_count(s, tid);
    let pidx: int = choose |pidx: int|
      crate::composed::spec::assumptions::is_task_pending_at(s, tid, pidx) &&
      s.task_logs.contains_key(tid) &&
      (forall |jj: int| pidx < jj < s.executor_log.len() ==>
        !crate::executor::spec::log::is_poll_task_for_id_at(s.executor_log, jj, tid));
    assert((j * chunk) == chunk + ((j - 1) * chunk)) by (nonlinear_arith) requires j >= 1nat {};
    ete_reachable_N_split(s, l_prime, chunk, ((j - 1) * chunk) as nat, cap, tid);
    let s_mid: ComposedState = choose |s_mid: ComposedState|
      ete_reachable_N(s, s_mid, chunk, cap, tid) &&
      ete_reachable_N(s_mid, l_prime, ((j - 1) * chunk) as nat, cap, tid);
    composed_pending_to_poll_derived(s, s_mid, chunk, cap, tid, pidx);
    let poll_idx: int = choose |i: int|
      s.executor_log.len() as int <= i < s_mid.executor_log.len() &&
      crate::executor::spec::log::is_poll_task_for_id_at(s_mid.executor_log, i, tid);
    ete_reachable_N_implies_env(s, s_mid, chunk, cap, tid);
    crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, s_mid, chunk, env, tid);
    crate::composed::proof::end_to_end::progress_n_implies_extension(s, s_mid, chunk);
    crate::composed::proof::end_to_end::progress_n_preserves_wf(s, s_mid, chunk);
    assert(crate::executor::spec::log::is_prefix_of(s.executor_log, s_mid.executor_log));
    count_polls_grows_with_new_poll(s.executor_log, s_mid.executor_log, tid, poll_idx);
    assert(crate::executor::spec::log::has_poll_for_id(s_mid.executor_log, tid));
    assert(get_max_queue_length(s_mid) == get_max_queue_length(s));
    assert(get_max_timer_deadline_gap(s_mid, tid) == get_max_timer_deadline_gap(s, tid));
    assert(get_io_ready_bound(s_mid, tid) == get_io_ready_bound(s, tid));
    uniform_chunks(s_mid, l_prime, tid, cap, (j - 1) as nat, chunk);
  }
}

// Completion step: once tid has been polled at least cap times, env_N's uniform
// poll bound gives task_polled_to_ready. This is the terminal step of the wake
// loop — the chunks induction accumulates cap polls, then this yields Ready.
pub proof fn cap_polls_gives_ready(l_prime: ComposedState, tid: TaskId, cap: nat)
  requires
    env_N(l_prime, tid, cap),
    count_polls_for_tid(l_prime.executor_log, tid) >= cap,
  ensures
    crate::composed::spec::contract::end_to_end_response(l_prime, tid),
{
  assert(bounded_poll_count_here_with_bound(l_prime, tid, cap));
}

// env_N-based goal (fixed uniform bound cap): every env_N-good n-step
// continuation polls tid to Ready. The not-ready scheduling proof establishes
// this for EVERY cap >= 1 (see ete_reaches_goal_for_cap), with n a function of
// cap: n = chunk + cap*chunk, chunk = K + B + C + cap + 2 (B = the io readiness
// bound get_io_ready_bound, carried separately from cap).
pub open spec fn ete_reaches_goal_N(s: ComposedState, tid: TaskId, cap: nat, n: nat) -> bool {
  forall |l2: ComposedState| #[trigger] ete_reachable_N(s, l2, n, cap, tid)
    ==> crate::composed::spec::contract::end_to_end_response(l2, tid)
}

// ∀cap packaging: for THIS cap there is a step budget n within which every
// env_N(cap)-good continuation reaches Ready. The top theorem quantifies cap
// UNIVERSALLY (cap >= 1), so it covers every task completion bound — the old
// ∃cap form was dischargeable at the degenerate cap = 1 alone ("polled once
// ⇒ ready") and said nothing about multi-poll tasks.
pub open spec fn ete_reaches_goal_for_cap(s: ComposedState, tid: TaskId, cap: nat) -> bool {
  exists |n: nat| #[trigger] ete_reaches_goal_N(s, tid, cap, n)
}

pub proof fn ete_reaches_goal_N_when_already_ready(s: ComposedState, tid: TaskId, cap: nat, n: nat)
  requires
    crate::composed::spec::contract::end_to_end_response(s, tid),
  ensures
    ete_reaches_goal_N(s, tid, cap, n),
{
  ete_trace_reaches_goal_when_already_ready(s, tid, n);
  assert forall |l2: ComposedState| #[trigger] ete_reachable_N(s, l2, n, cap, tid)
    implies crate::composed::spec::contract::end_to_end_response(l2, tid) by {
    ete_reachable_N_implies_env(s, l2, n, cap, tid);
  };
}

// The env_N target theorem (composed-local, □env ⇒ ◇goal with a uniform bound):
// for every qualifying (s,tid) and EVERY task completion bound cap >= 1, some n
// such that all env_N(cap)-good n-step continuations reach Ready. Precondition
// uses end_to_end_env (satisfiable), since ∃cap. env_N(s,tid,cap) ⇔
// end_to_end_env(s,tid).
pub open spec fn end_to_end_liveness_env_N_trace() -> bool {
  crate::framework::module_spec::progress_preserves_wf(
    crate::composed::spec::progress::composed_module_spec()) &&
  forall |s: ComposedState, tid: TaskId, cap: nat|
    #![trigger ete_reaches_goal_for_cap(s, tid, cap)]
    crate::composed::spec::progress::composed_well_formed(s) &&
    !crate::composed::spec::contract::end_to_end_trigger(s, tid) &&
    end_to_end_env(s, tid) &&
    crate::composed::spec::contract::end_to_end_arrival(s, tid) &&
    cap >= 1
    ==> ete_reaches_goal_for_cap(s, tid, cap)
}

// The SOLE remaining obligation: not-yet-ready qualifying states reach the goal
// for every cap >= 1. (Ready states discharge at n=0 for any cap.)
pub open spec fn ete_goal_obligation_N_not_ready() -> bool {
  forall |s: ComposedState, tid: TaskId, cap: nat|
    #![trigger ete_reaches_goal_for_cap(s, tid, cap)]
    crate::composed::spec::progress::composed_well_formed(s) &&
    !crate::composed::spec::contract::end_to_end_trigger(s, tid) &&
    end_to_end_env(s, tid) &&
    crate::composed::spec::contract::end_to_end_arrival(s, tid) &&
    cap >= 1 &&
    !crate::composed::spec::contract::end_to_end_response(s, tid)
    ==> ete_reaches_goal_for_cap(s, tid, cap)
}

pub proof fn end_to_end_liveness_env_N_trace_from_goal()
  requires
    ete_goal_obligation_N_not_ready(),
  ensures
    end_to_end_liveness_env_N_trace(),
{
  crate::composed::proof::end_to_end::progress_preserves_wf_helper();
  assert forall |s: ComposedState, tid: TaskId, cap: nat|
    crate::composed::spec::progress::composed_well_formed(s) &&
    !crate::composed::spec::contract::end_to_end_trigger(s, tid) &&
    end_to_end_env(s, tid) &&
    crate::composed::spec::contract::end_to_end_arrival(s, tid) &&
    cap >= 1
    implies #[trigger] ete_reaches_goal_for_cap(s, tid, cap) by {
    if crate::composed::spec::contract::end_to_end_response(s, tid) {
      ete_reaches_goal_N_when_already_ready(s, tid, cap, 0nat);
      assert(ete_reaches_goal_N(s, tid, cap, 0nat));
    }
  };
}

// THE (II) OBLIGATION, PROVEN for every cap >= 1: chunk = K + B + C + cap + 2,
// n = chunk + cap*chunk; for every env_N(cap)-good n-continuation l2: split at
// chunk into s→s1 (composed_arrival_to_poll: s1 is polled) and s1→l2
// (ete_reaches_goal_N_from_polled: cap chunks accumulate cap polls, then
// env_N's uniform poll bound yields Ready). Fully env-sourced, zero axioms.
pub proof fn ete_goal_obligation_N_not_ready_holds()
  ensures
    ete_goal_obligation_N_not_ready(),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  assert forall |s: ComposedState, tid: TaskId, cap: nat|
    crate::composed::spec::progress::composed_well_formed(s) &&
    !crate::composed::spec::contract::end_to_end_trigger(s, tid) &&
    end_to_end_env(s, tid) &&
    crate::composed::spec::contract::end_to_end_arrival(s, tid) &&
    cap >= 1 &&
    !crate::composed::spec::contract::end_to_end_response(s, tid)
    implies #[trigger] ete_reaches_goal_for_cap(s, tid, cap) by {
    let chunk: nat = (get_max_timer_deadline_gap(s, tid) + get_io_ready_bound(s, tid)
      + get_max_queue_length(s) + cap + 2) as nat;
    let n: nat = (chunk + cap * chunk) as nat;
    assert forall |l2: ComposedState| #[trigger] ete_reachable_N(s, l2, n, cap, tid)
      implies crate::composed::spec::contract::end_to_end_response(l2, tid) by {
      ete_reachable_N_split(s, l2, chunk, (cap * chunk) as nat, cap, tid);
      let s1: ComposedState = choose |s1: ComposedState|
        ete_reachable_N(s, s1, chunk, cap, tid) &&
        ete_reachable_N(s1, l2, (cap * chunk) as nat, cap, tid);
      composed_arrival_to_poll(s, s1, chunk, cap, tid);
      ete_reachable_N_implies_env(s, s1, chunk, cap, tid);
      crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, s1, chunk, env, tid);
      crate::composed::proof::end_to_end::progress_n_preserves_wf(s, s1, chunk);
      assert(get_max_timer_deadline_gap(s1, tid) == get_max_timer_deadline_gap(s, tid));
      assert(get_io_ready_bound(s1, tid) == get_io_ready_bound(s, tid));
      assert(get_max_queue_length(s1) == get_max_queue_length(s));
      ete_reaches_goal_N_from_polled(s1, tid, cap, chunk);
    };
    assert(ete_reaches_goal_N(s, tid, cap, n));
  };
}

// The FINAL non-vacuous end-to-end liveness theorem, PROVEN outright (no
// hypothesis): satisfiable env precondition (end_to_end_env) + □env_N ⇒ ◇Ready,
// via the proven obligation. Zero axioms.
pub proof fn end_to_end_liveness_env_N_trace_holds()
  ensures
    end_to_end_liveness_env_N_trace(),
{
  ete_goal_obligation_N_not_ready_holds();
  end_to_end_liveness_env_N_trace_from_goal();
}

// Explicit-bound corollary: the top theorem packages the step budget as ∃n;
// this spells the witness out in the signature — n = chunk + cap·chunk with
// chunk = K + B + C + cap + 2 (K = get_max_timer_deadline_gap, B =
// get_io_ready_bound, C = get_max_queue_length). Same proof as the not-ready
// obligation, plus the already-Ready case at the same n.
pub proof fn ete_reaches_goal_explicit_bound(s: ComposedState, tid: TaskId, cap: nat)
  requires
    crate::composed::spec::progress::composed_well_formed(s),
    !crate::composed::spec::contract::end_to_end_trigger(s, tid),
    end_to_end_env(s, tid),
    crate::composed::spec::contract::end_to_end_arrival(s, tid),
    cap >= 1,
  ensures
    ete_reaches_goal_N(s, tid, cap, ({
      let chunk: nat = (get_max_timer_deadline_gap(s, tid) + get_io_ready_bound(s, tid)
        + get_max_queue_length(s) + cap + 2) as nat;
      (chunk + cap * chunk) as nat
    })),
{
  let progress = crate::composed::spec::progress::composed_module_spec().progress;
  let env = |s2: ComposedState, tid2: TaskId| end_to_end_env(s2, tid2);
  let chunk: nat = (get_max_timer_deadline_gap(s, tid) + get_io_ready_bound(s, tid)
    + get_max_queue_length(s) + cap + 2) as nat;
  let n: nat = (chunk + cap * chunk) as nat;
  if crate::composed::spec::contract::end_to_end_response(s, tid) {
    ete_reaches_goal_N_when_already_ready(s, tid, cap, n);
  } else {
    assert forall |l2: ComposedState| #[trigger] ete_reachable_N(s, l2, n, cap, tid)
      implies crate::composed::spec::contract::end_to_end_response(l2, tid) by {
      ete_reachable_N_split(s, l2, chunk, (cap * chunk) as nat, cap, tid);
      let s1: ComposedState = choose |s1: ComposedState|
        ete_reachable_N(s, s1, chunk, cap, tid) &&
        ete_reachable_N(s1, l2, (cap * chunk) as nat, cap, tid);
      composed_arrival_to_poll(s, s1, chunk, cap, tid);
      ete_reachable_N_implies_env(s, s1, chunk, cap, tid);
      crate::framework::module_spec::env_progress_n_implies_progress_n(progress, s, s1, chunk, env, tid);
      crate::composed::proof::end_to_end::progress_n_preserves_wf(s, s1, chunk);
      assert(get_max_timer_deadline_gap(s1, tid) == get_max_timer_deadline_gap(s, tid));
      assert(get_io_ready_bound(s1, tid) == get_io_ready_bound(s, tid));
      assert(get_max_queue_length(s1) == get_max_queue_length(s));
      ete_reaches_goal_N_from_polled(s1, tid, cap, chunk);
    };
  }
}

pub proof fn env_gives_core_clauses(s: ComposedState, tid: TaskId)
  requires
    end_to_end_env(s, tid),
  ensures
    timestamps_strictly_increasing(s.reactor_log),
    crate::reactor::timestamps_positive(s.reactor_log),
    timer_deadline_gap_bounded(s, tid),
    timer_resources_remain_active(s),
    queue_length_bounded(s),
    executor_log::tid_unique(s.executor_log, tid),
    contract_io_assumption_here(s),
{
}

}
