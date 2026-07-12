// Trusted glue: yield_now — cooperatively defer the current task once. Plain Rust
// over the executor's defer mechanism; verus::trusted under Verus.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use lion_executor::tls;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub async fn yield_now() {
  YieldNow { yielded: false }.await
}

struct YieldNow {
  yielded: bool,
}

impl Future for YieldNow {
  type Output = ();

  fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
    if self.yielded {
      Poll::Ready(())
    } else {
      self.yielded = true;
      tls::defer_current();
      Poll::Pending
    }
  }
}
