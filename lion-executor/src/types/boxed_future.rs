use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
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
  pub(crate) fn new(future: impl Future<Output = ()> + Send + 'static) -> Self {
  BoxedFuture {
    inner: Box::pin(future),
  }
  }

  pub(crate) fn with_join_sender<T: Send + 'static>(
  future: impl Future<Output = T> + Send + 'static,
  sender: super::JoinSender<T>,
  ) -> Self {
  BoxedFuture {
    inner: Box::pin(async move {
    let result = future.await;
    sender.complete(result);
    }),
  }
  }

  pub(crate) fn poll(&mut self, cx: &mut Context) -> Poll<()> {
  self.inner.as_mut().poll(cx)
  }
}
