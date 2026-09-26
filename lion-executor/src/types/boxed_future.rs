use std::future::Future;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::task::{Context, Poll};
use super::join_handle::{JoinError, JoinSender};
use vstd::prelude::*;

verus! {

pub type BoxedFutureView = int;

#[verifier::external_body]
pub struct BoxedFuture {
  inner: Pin<Box<dyn Future<Output = ()> + Send + 'static>>,
}

impl View for BoxedFuture {
  type V = BoxedFutureView;

  #[verifier::external_body]
  open spec fn view(&self) -> BoxedFutureView {
  0int
  }
}

} // end verus!

impl BoxedFuture {
  pub(crate) fn with_join_sender<F>(future: F, sender: JoinSender<F::Output>) -> Self
  where
    F: Future + Send + 'static,
    F::Output: Send + 'static,
  {
  BoxedFuture {
    inner: Box::pin(TaskCell::new(future, sender)),
  }
  }

  pub(crate) fn poll(&mut self, cx: &mut Context) -> Poll<()> {
  self.inner.as_mut().poll(cx)
  }
}

// Trusted glue: the outermost future of every spawned task, and the only thing
// the executor ever polls (through `Executor::poll_future_raw`). It turns
// every way a task can end into a completed poll, so the verified executor
// sees just `Ready(())` and retires the task exactly as it retires one whose
// future finished:
// - the future returns Ready(v): the handle gets Ok(v);
// - the future's poll panics: the unwind stops here and the handle gets a
//   panic JoinError carrying the payload;
// - the handle was aborted: at the next poll (abort wakes the task) the future
//   is dropped without being polled again and the handle gets a cancelled
//   JoinError.
// In every case the user future is dropped here, in place, on the thread that
// polls it, before the JoinHandle is resolved, and a panic from its destructor
// or from the JoinHandle's waker is contained too. TaskCell::poll therefore
// does not unwind.
pub(crate) struct TaskCell<F: Future> {
  // Structurally pinned: never moved out of the cell; dropped only in place
  // (assigning None, or dropping the cell). TaskCell implements neither Drop
  // nor Unpin by hand, so it is Unpin exactly when F is.
  future: Option<F>,
  sender: Option<JoinSender<F::Output>>,
  waker_registered: bool,
}

impl<F: Future> TaskCell<F> {
  pub(crate) fn new(future: F, sender: JoinSender<F::Output>) -> Self {
    TaskCell { future: Some(future), sender: Some(sender), waker_registered: false }
  }
}

impl<F: Future> Future for TaskCell<F> {
  type Output = ();

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
    // SAFETY: only `future` is treated as pinned, and it is never moved: it is
    // re-pinned below by reference and later dropped in place. The other
    // fields are ordinary values.
    let this = unsafe { self.get_unchecked_mut() };
    let sender = match this.sender.as_ref() {
      Some(s) => s,
      // Already finished; the executor never polls a retired task again.
      None => return Poll::Ready(()),
    };
    // Register the task's waker before reading the flag: an abort either sees
    // the waker and wakes the task, or set the flag before this read.
    if !this.waker_registered {
      sender.register_task_waker(cx.waker());
      this.waker_registered = true;
    }
    let outcome = if sender.is_cancelled() {
      Err(JoinError::cancelled())
    } else {
      let future = this.future.as_mut().expect("unfinished task has its future");
      // SAFETY: `future` lives inside the pinned cell and is never moved.
      let future = unsafe { Pin::new_unchecked(future) };
      match catch_unwind(AssertUnwindSafe(|| future.poll(cx))) {
        Ok(Poll::Pending) => return Poll::Pending,
        Ok(Poll::Ready(value)) => Ok(value),
        Err(payload) => Err(JoinError::panic(payload)),
      }
    };
    // Finished. Drop the future in place, here, before resolving the handle.
    // A panicking destructor turns the outcome into that panic, as in tokio.
    let future = &mut this.future;
    let outcome = match catch_unwind(AssertUnwindSafe(|| *future = None)) {
      Ok(()) => outcome,
      Err(payload) => {
        let _ = catch_unwind(AssertUnwindSafe(move || drop(outcome)));
        Err(JoinError::panic(payload))
      }
    };
    let sender = this.sender.take().expect("unfinished task has its sender");
    // Resolving the handle wakes whoever awaits it, which is arbitrary code.
    let _ = catch_unwind(AssertUnwindSafe(move || sender.finish(outcome)));
    Poll::Ready(())
  }
}
