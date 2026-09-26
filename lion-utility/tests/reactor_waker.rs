// `create_reactor_waker_for_current` regressions. The waker the reactor stores
// for a task's io wait is an `Arc` + `std::task::Wake` waker. Woken on the
// owner thread (where the reactor wakes it) it must re-queue the task; woken on
// any other thread it must reach the owner through the cross-thread queue. The
// former hand-written vtable waker pushed onto the calling thread's own TLS
// queue, so a foreign-thread wake was lost and the task never ran again.

use lion_executor::{create_reactor_waker_for_current, spawn, Runtime};
use lion_utility::time::timeout;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::time::Duration;

// Returns Pending once after handing the task's reactor waker to `deliver`,
// then Ready on the next poll.
struct WaitForReactorWake<D: FnMut(Waker) + Unpin> {
  deliver: D,
  armed: bool,
}

impl<D: FnMut(Waker) + Unpin> Future for WaitForReactorWake<D> {
  type Output = ();
  fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
    if self.armed {
      return Poll::Ready(());
    }
    self.armed = true;
    let waker = create_reactor_waker_for_current();
    (self.deliver)(waker);
    Poll::Pending
  }
}

#[test]
fn reactor_waker_woken_on_owner_thread_repolls_task() {
  let rt = Runtime::new().expect("runtime");
  rt.block_on(async {
    let task = spawn(WaitForReactorWake { deliver: |w: Waker| w.wake(), armed: false });
    let joined = timeout(Duration::from_secs(5), task).await;
    assert!(matches!(joined, Ok(Ok(()))), "owner-thread reactor wake lost");
  });
}

#[test]
fn reactor_waker_woken_off_thread_repolls_task() {
  let rt = Runtime::new().expect("runtime");
  rt.block_on(async {
    let task = spawn(WaitForReactorWake {
      deliver: |w: Waker| {
        std::thread::spawn(move || {
          std::thread::sleep(Duration::from_millis(50));
          w.wake();
        });
      },
      armed: false,
    });
    let joined = timeout(Duration::from_secs(5), task).await;
    assert!(matches!(joined, Ok(Ok(()))), "foreign-thread reactor wake lost");
  });
}
