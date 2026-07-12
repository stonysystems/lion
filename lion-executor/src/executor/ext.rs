use std::task::Context;
use crate::tls;
use crate::types::{create_waker, create_raw_task_waker, Duration, Instant, PollResult, Task, TaskId, TID, TaskView, WakeSource};
use crate::spec::log::*;
use crate::proof::invariants::*;
use crate::proof::helpers::*;
use super::Executor;
use vstd::prelude::*;

// Ghost-log action macro: the ONE definition of the "ghost-log shape" trusted
// on the executor side. Every expansion is an external_body method whose whole
// contract is (a) append exactly the given event to the log and (b) leave every
// other Executor field (local_queue / task_slab@ / task_slab.wf() / ledger)
// unchanged. Auditing the frame clauses of all log actions reduces to auditing
// this macro body once.
//
// macro_rules! cannot live inside verus! (proc macro), so each expansion emits
// its own `verus! { impl Executor { .. } }` block; the event is captured as raw
// token trees because verus spec syntax (`@` etc.) is not plain rust expr.
//
// The local_queue frame clause uses `==` where the handwritten originals used
// `=~=`: the `=~=` punct loses token jointness through macro_rules transcription
// and the plain-cargo builtin_macros parser (vstd rev db81a74) rejects it
// ("expected an expression" at `~`). As an ASSUMED external_body postcondition
// the two are logically equivalent for Seq (`==` gives `=~=` by congruence;
// `=~=` gives `==` by the extensionality axiom), and `==` is the direct form.
macro_rules! executor_log_action {
  ($(#[$attr:meta])* $vis:vis fn $name:ident(&mut self $(, $arg:ident: $ty:ty)* $(,)?) => $($event:tt)*) => {
    verus! {
      impl Executor {
        $(#[$attr])*
        #[verifier::external_body]
        $vis fn $name(&mut self $(, $arg: $ty)*)
          ensures
            self.log@ == old(self).log@.push($($event)*),
            self.local_queue@ == old(self).local_queue@,
            self.task_slab@ == old(self).task_slab@,
            self.task_slab.wf() == old(self).task_slab.wf(),
            self.ledger == old(self).ledger,
        { }
      }
    }
  };
}

executor_log_action! {
  pub fn tick_begin_action(&mut self) =>
    ExecutorEvent::Inbound(InboundCall::Tick { result: None })
}

executor_log_action! {
  pub fn tick_end_action(&mut self) =>
    ExecutorEvent::Inbound(InboundCall::Tick { result: Some(()) })
}

// Ghost-log shape trust only: appends the PollTask event recording what the
// verified layer observed; touches nothing else.
executor_log_action! {
  fn log_poll_task_action(&mut self, task_id: TaskId, task: &Option<Task>, result: &PollResult<()>) =>
    ExecutorEvent::Outbound(OutboundCall::PollTask {
      task_id: task_id@,
      task: match *task { Some(t) => Some(t@), None => None },
      result: *result,
    })
}

// Ghost-log shape trust only: appends the PopInjection event recording
// exactly what the verified layer decided (accepted task or None).
executor_log_action! {
  fn log_pop_injection_action(&mut self, task: &Option<Task>) =>
    ExecutorEvent::Outbound(OutboundCall::PopInjection {
      task: match *task { Some(t) => Some(t@), None => None }
    })
}

// Ghost-log shape trust only: append one Drain event recording exactly the
// ids the verified layer kept.
executor_log_action! {
  fn log_drain_task_wake_action(&mut self, ids: &Vec<TaskId>) =>
    ExecutorEvent::Outbound(OutboundCall::Drain {
      source: DrainSource::TaskWake,
      task_ids: ids@.map_values(|t: TaskId| t@),
    })
}

executor_log_action! {
  fn log_drain_reactor_wake_action(&mut self, ids: &Vec<TaskId>) =>
    ExecutorEvent::Outbound(OutboundCall::Drain {
      source: DrainSource::ReactorWake,
      task_ids: ids@.map_values(|t: TaskId| t@),
    })
}

executor_log_action! {
  fn log_drain_deferred_action(&mut self, ids: &Vec<TaskId>) =>
    ExecutorEvent::Outbound(OutboundCall::Drain {
      source: DrainSource::Deferred,
      task_ids: ids@.map_values(|t: TaskId| t@),
    })
}

verus! {

impl Executor {
  // Runs the user future. This free function takes NO executor reference —
  // that the executor state is untouched during a user poll is now a fact of
  // the type system, not a trusted claim. Residual trust: user wake/spawn
  // effects route through TLS (consumed by the drain path), and the returned
  // pair has the shape below.
  #[verifier::external_body]
  fn poll_future_raw(task_id: TaskId, task: Option<Task>)
    -> (ret: (PollResult<()>, Option<Task>))
    ensures
      task.is_some() ==> ret.1.is_some(),
      task.is_some() ==> (ret.0 == PollResult::<()>::Ready(()) || ret.0 == PollResult::<()>::Pending),
      task.is_none() ==> ret.0 == PollResult::<()>::Pending && ret.1.is_none(),
  {
    match task {
      Some(mut t) => {
        tls::set_current_task(task_id);
        let waker = create_waker(task_id, WakeSource::Task, false);
        let mut context = Context::from_waker(&waker);
        let poll_result = PollResult::from(t.poll(&mut context));
        tls::clear_current_task();
        (poll_result, Some(t))
      }
      None => {
        (PollResult::Pending, None)
      }
    }
  }

  // The old poll_task_action contract, now ASSEMBLED from the two pieces
  // above inside verified code (poll without executor access, then log).
  pub fn poll_task_action(&mut self, task_id: TaskId, task: Option<Task>)
    -> (ret: (PollResult<()>, Option<Task>))
    ensures self.log@ == old(self).log@.push(
      ExecutorEvent::Outbound(OutboundCall::PollTask {
        task_id: task_id@,
        task: match ret.1 { Some(t) => Some(t@), None => None },
        result: ret.0,
      })
    ),
    self.local_queue@ =~= old(self).local_queue@,
    self.task_slab@ == old(self).task_slab@,
    self.task_slab.wf() == old(self).task_slab.wf(),
    self.ledger == old(self).ledger,
    task.is_some() ==> ret.1.is_some(),
    task.is_some() ==> (ret.0 == PollResult::<()>::Ready(()) || ret.0 == PollResult::<()>::Pending),
    task.is_none() ==> ret.0 == PollResult::<()>::Pending && ret.1.is_none(),
  {
    let has_task = task.is_some();
    let (result, task_back) = Self::poll_future_raw(task_id, task);
    self.log_poll_task_action(task_id, &task_back, &result);
    (result, task_back)
  }

  #[verifier::external_body]
  pub fn poll_task_invalid_action(&mut self, task_id: TaskId)
    ensures
      self.log@ == old(self).log@.push(
        ExecutorEvent::Outbound(OutboundCall::PollTask {
          task_id: task_id@,
          task: None::<TaskView>,
          result: PollResult::<()>::Invalid,
        })
      ),
      self.local_queue@ =~= old(self).local_queue@,
      self.task_slab@ == old(self).task_slab@,
      self.task_slab.wf() == old(self).task_slab.wf(),
      self.ledger == old(self).ledger,
  { }

  // Raw channel pop. Takes only the receiver — no executor access, no ghost
  // effects, no semantic claims about what comes out of the mpsc.
  #[verifier::external_body]
  fn try_recv_raw(rx: &crate::collections::MpscReceiver<Task>) -> Option<Task>
  {
    rx.try_recv()
  }

  // The old pop_injection_action freshness AXIOM, now a verified runtime
  // check: the popped TID is compared against the ledger (which mirrors the
  // log's pop history — ledger_matches_log); a duplicate is dropped and
  // recorded as an empty pop, so the log provably never contains two
  // successful pops of the same TID. The duplicate branch is dead in reality
  // (spawn allocates TIDs from a monotone atomic counter); its existence is
  // what turns trust in the sender into a receiver-side proof.
  pub fn pop_injection_action(&mut self) -> (ret: Option<Task>)
    requires
      ledger_matches_log(old(self).ledger, old(self).log@),
      inv_valid_task_polling(old(self).log@),
    ensures
      self.log@ == old(self).log@.push(
        ExecutorEvent::Outbound(OutboundCall::PopInjection {
          task: match ret { Some(t) => Some(t@), None => None }
        })
      ),
      self.local_queue@ =~= old(self).local_queue@,
      self.task_slab@ == old(self).task_slab@,
      self.task_slab.wf() == old(self).task_slab.wf(),
      ledger_matches_log(self.ledger, self.log@),
      ret.is_some() ==>
        !tid_was_injected_before(old(self).log@, old(self).log@.len() as int, ret.unwrap()@.id),
      ret.is_some() ==>
        !tid_returned_ready_before(old(self).log@, old(self).log@.len() as int, ret.unwrap()@.id),
  {
    let raw = Self::try_recv_raw(&self.injection_queue);
    match raw {
      None => {
        let none: Option<Task> = None;
        self.log_pop_injection_action(&none);
        proof {
          ledger_preserved_by_non_pop(self.ledger, old(self).log@, self.log@);
        }
        None
      }
      Some(task) => {
        let task_id = task.id();
        if self.ledger.contains(task_id) {
          let none: Option<Task> = None;
          self.log_pop_injection_action(&none);
          proof {
            ledger_preserved_by_non_pop(self.ledger, old(self).log@, self.log@);
          }
          None
        } else {
          let ghost pre_ledger = self.ledger;
          let ghost tid = task_id@;
          self.ledger.mark(task_id);
          let some_task = Some(task);
          self.log_pop_injection_action(&some_task);
          proof {
            assert(!pre_ledger.spec_has(tid));
            assert(!tid_was_injected_before(old(self).log@, old(self).log@.len() as int, tid));
            not_injected_implies_not_ready(old(self).log@, tid);
            ledger_updated_by_pop_some(pre_ledger, self.ledger, old(self).log@, self.log@, tid);
          }
          some_task
        }
      }
    }
  }

  #[verifier::external_body]
  pub fn park_action(&mut self, require_timeout: bool)
    ensures
      self.log@ == old(self).log@.push(
        ExecutorEvent::Outbound(OutboundCall::Park)
      ),
      self.local_queue@ =~= old(self).local_queue@,
      self.task_slab@ == old(self).task_slab@,
      self.task_slab.wf() == old(self).task_slab.wf(),
      self.ledger == old(self).ledger,
  {
    let timeout = if require_timeout {
      Some(Duration::from_millis(100))
    } else {
      Some(Duration::zero())
    };
    self.reactor.flush_pending_deregister();
    self.reactor.park(timeout);
  }

  #[verifier::external_body]
  pub fn reset_and_drain_cross_thread_action(&self)
  {
    tls::reset_interrupt();
    tls::drain_cross_thread();
  }

  #[verifier::external_body]
  pub fn has_deferred_action(&self) -> (ret: bool)
  {
    tls::has_deferred()
  }

  #[verifier::external_body]
  pub fn has_reactor_ready_action(&self) -> (ret: bool)
  {
    tls::has_reactor_ready()
  }

  #[verifier::external_body]
  pub fn has_task_ready_action(&self) -> (ret: bool)
  {
    tls::has_task_ready()
  }

  #[verifier::external_body]
  pub fn take_block_on_yielded_action(&self) -> (ret: bool)
  {
    tls::take_block_on_yielded()
  }

  // Raw TLS takers: hand over whatever the wake path pushed, as a plain Vec.
  // No executor access, no ghost effects, no semantic claims — fabricated
  // TIDs are filtered by the verified layer below; lost wakes remain covered
  // by the model-side arrival assumptions.
  #[verifier::external_body]
  fn take_task_ready_from_tls() -> Vec<TaskId>
  {
    tls::drain_cross_thread();
    tls::take_task_ready().into()
  }

  #[verifier::external_body]
  fn take_reactor_ready_from_tls() -> Vec<TaskId>
  {
    tls::take_reactor_ready().into()
  }

  #[verifier::external_body]
  fn take_deferred_from_tls() -> Vec<TaskId>
  {
    tls::take_deferred().into()
  }

  // Verified half of every drain: keep only ledger-known (= provably
  // injected) TIDs and append them to the local queue. The FIFO-append
  // equality and the all-queued-injected facts are PROVEN here — they were
  // trusted ensures of the old external_body drains.
  fn filter_and_enqueue(&mut self, ids: Vec<TaskId>) -> (kept: Vec<TaskId>)
    requires
      all_queue_tids_injected(old(self).log@, old(self).local_queue@),
      ledger_matches_log(old(self).ledger, old(self).log@),
    ensures
      self.log == old(self).log,
      self.task_slab@ == old(self).task_slab@,
      self.task_slab.wf() == old(self).task_slab.wf(),
      self.ledger == old(self).ledger,
      self.local_queue@ =~= old(self).local_queue@ + kept@.map_values(|t: TaskId| t@),
      all_queue_tids_injected(self.log@, self.local_queue@),
  {
    let mut kept: Vec<TaskId> = Vec::new();
    let mut i: usize = 0;
    while i < ids.len()
      invariant
        self.log == old(self).log,
        self.task_slab@ == old(self).task_slab@,
        self.task_slab.wf() == old(self).task_slab.wf(),
        self.ledger == old(self).ledger,
        ledger_matches_log(self.ledger, self.log@),
        all_queue_tids_injected(self.log@, self.local_queue@),
        self.local_queue@ =~= old(self).local_queue@ + kept@.map_values(|t: TaskId| t@),
      decreases ids@.len() - i,
    {
      let t = ids[i];
      if self.ledger.contains(t) {
        let ghost pre_kept = kept@;
        let ghost pre_queue = self.local_queue@;
        kept.push(t);
        self.local_queue.push_back(t);
        proof {
          assert(self.ledger.spec_has(t@));
          assert(tid_was_injected_before(self.log@, self.log@.len() as int, t@));
          assert(kept@.map_values(|x: TaskId| x@) =~=
            pre_kept.map_values(|x: TaskId| x@).push(t@));
          assert(self.local_queue@ =~= pre_queue.push(t@));
        }
      }
      i = i + 1;
    }
    kept
  }

  pub fn drain_task_ready_into_local(&mut self)
    requires
      all_queue_tids_injected(old(self).log@, old(self).local_queue@),
      ledger_matches_log(old(self).ledger, old(self).log@),
    ensures
      exists |task_ids: Seq<TID>| {
        &&& self.log@ == old(self).log@.push(
          ExecutorEvent::Outbound(OutboundCall::Drain {
            source: DrainSource::TaskWake,
            task_ids: task_ids,
          })
        )
        &&& self.local_queue@ =~= old(self).local_queue@ + task_ids
        &&& all_queue_tids_injected(self.log@, self.local_queue@)
      },
      self.task_slab@ == old(self).task_slab@,
      self.task_slab.wf() == old(self).task_slab.wf(),
      self.ledger == old(self).ledger,
      ledger_matches_log(self.ledger, self.log@),
  {
    let ids = Self::take_task_ready_from_tls();
    let kept = self.filter_and_enqueue(ids);
    let ghost mid_log = self.log@;
    self.log_drain_task_wake_action(&kept);
    proof {
      let tids = kept@.map_values(|t: TaskId| t@);
      assert(mid_log =~= self.log@.subrange(0, mid_log.len() as int));
      data_inv_preserved_by_extension(mid_log, self.log@, self.local_queue@);
      ledger_preserved_by_non_pop(self.ledger, mid_log, self.log@);
      assert(self.local_queue@ =~= old(self).local_queue@ + tids);
    }
  }

  pub fn drain_reactor_ready_into_local(&mut self)
    requires
      all_queue_tids_injected(old(self).log@, old(self).local_queue@),
      ledger_matches_log(old(self).ledger, old(self).log@),
    ensures
      exists |task_ids: Seq<TID>| {
        &&& self.log@ == old(self).log@.push(
          ExecutorEvent::Outbound(OutboundCall::Drain {
            source: DrainSource::ReactorWake,
            task_ids: task_ids,
          })
        )
        &&& self.local_queue@ =~= old(self).local_queue@ + task_ids
        &&& all_queue_tids_injected(self.log@, self.local_queue@)
      },
      self.task_slab@ == old(self).task_slab@,
      self.task_slab.wf() == old(self).task_slab.wf(),
      self.ledger == old(self).ledger,
      ledger_matches_log(self.ledger, self.log@),
  {
    let ids = Self::take_reactor_ready_from_tls();
    let kept = self.filter_and_enqueue(ids);
    let ghost mid_log = self.log@;
    self.log_drain_reactor_wake_action(&kept);
    proof {
      let tids = kept@.map_values(|t: TaskId| t@);
      assert(mid_log =~= self.log@.subrange(0, mid_log.len() as int));
      data_inv_preserved_by_extension(mid_log, self.log@, self.local_queue@);
      ledger_preserved_by_non_pop(self.ledger, mid_log, self.log@);
      assert(self.local_queue@ =~= old(self).local_queue@ + tids);
    }
  }

  pub fn drain_deferred_into_local(&mut self)
    requires
      all_queue_tids_injected(old(self).log@, old(self).local_queue@),
      ledger_matches_log(old(self).ledger, old(self).log@),
    ensures
      exists |task_ids: Seq<TID>| {
        &&& self.log@ == old(self).log@.push(
          ExecutorEvent::Outbound(OutboundCall::Drain {
            source: DrainSource::Deferred,
            task_ids: task_ids,
          })
        )
        &&& self.local_queue@ =~= old(self).local_queue@ + task_ids
        &&& all_queue_tids_injected(self.log@, self.local_queue@)
      },
      self.task_slab@ == old(self).task_slab@,
      self.task_slab.wf() == old(self).task_slab.wf(),
      self.ledger == old(self).ledger,
      ledger_matches_log(self.ledger, self.log@),
  {
    let ids = Self::take_deferred_from_tls();
    let kept = self.filter_and_enqueue(ids);
    let ghost mid_log = self.log@;
    self.log_drain_deferred_action(&kept);
    proof {
      let tids = kept@.map_values(|t: TaskId| t@);
      assert(mid_log =~= self.log@.subrange(0, mid_log.len() as int));
      data_inv_preserved_by_extension(mid_log, self.log@, self.local_queue@);
      ledger_preserved_by_non_pop(self.ledger, mid_log, self.log@);
      assert(self.local_queue@ =~= old(self).local_queue@ + tids);
    }
  }

}

} // end verus!

