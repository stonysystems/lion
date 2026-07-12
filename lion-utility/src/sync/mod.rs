// Cross-task signalling primitives (PassWaker class). Unlike time/net (reactor-
// mediated, liveness delegated to the reactor), these utilities' wake mechanism
// lives in their own state (a waiter queue): a task parks its waker (PassWaker)
// and another task's method call (notify / release / send) fires it (WakeWaker).
// They therefore must verify the PassWaker Contract (bounded liveness), not just
// the safety invariants. See ../../TODO.md §2/§3.
//
// `waiter` = the shared WaiterKernel (permit + waiter queue) underlying
// Notify / Semaphore / Mutex.
pub mod waiter;
pub mod notify;
pub mod semaphore;
pub mod mutex;
pub mod oneshot_kernel;
pub mod channel_kernel;
pub mod watch_kernel;
pub mod broadcast_kernel;
pub mod oneshot;
pub mod mpsc;
pub mod watch;
pub mod broadcast;

pub use mutex::{Lock, LockOwned, Mutex, MutexGuard, OwnedMutexGuard};
pub use notify::{Notified, Notify};
pub use semaphore::{Acquire, AcquireError, Semaphore, SemaphorePermit};
