use vstd::prelude::*;
use crate::executor::spec::log::Log as ExecutorLog;
use crate::reactor::spec::log::Log as ReactorLog;
use crate::utilities::spec::log::Log as TaskLog;
use crate::composed::spec::types::TaskId;
use crate::executor::spec::types::TaskView;

verus! {

pub struct ComposedState {
  pub executor_log: ExecutorLog,
  pub reactor_log: ReactorLog,
  pub task_logs: Map<TaskId, TaskLog>,
  // Ghost model of the (external) Injection Queue's committed delivery order.
  // Fixed across progress (see is_extension_of); pops read from it (schedule_delivers_tid).
  pub injection_schedule: Seq<TaskView>,
}

pub open spec fn empty_composed_state() -> ComposedState {
  ComposedState {
    executor_log: Seq::empty(),
    reactor_log: Seq::empty(),
    task_logs: Map::empty(),
    injection_schedule: Seq::empty(),
  }
}

pub open spec fn is_extension_of(s: ComposedState, s_prime: ComposedState) -> bool {
  crate::executor::spec::log::is_prefix_of(s.executor_log, s_prime.executor_log) &&
  crate::reactor::spec::log::is_prefix_of(s.reactor_log, s_prime.reactor_log) &&
  s.injection_schedule == s_prime.injection_schedule &&
  forall |tid: TaskId|
    s.task_logs.contains_key(tid) ==> (
      s_prime.task_logs.contains_key(tid) &&
      is_task_log_prefix(s.task_logs[tid], s_prime.task_logs[tid])
    )
}

pub open spec fn is_task_log_prefix(
  l: crate::utilities::spec::log::Log,
  l_prime: crate::utilities::spec::log::Log
) -> bool {
  l.len() <= l_prime.len() &&
  forall |i: int| 0 <= i < l.len() ==> l[i] == #[trigger] l_prime[i]
}

}
