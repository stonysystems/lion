use vstd::prelude::*;

verus! {

// Method tag (the `M`) for the WaiterKernel. `Wait` is the awaiting side
// (Notify::notified().poll / Semaphore::acquire / Mutex::lock) — it may park
// (PassWaker) and suspend. `Signal` is the releasing side (notify_one /
// add_permits / unlock) — a synchronous call that may wake a parked waiter
// (WakeWaker). R = () (the waited value is unit; concrete guards live in glue).
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum SyncMethod {
  Wait,
  Signal,
}

}
