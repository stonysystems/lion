use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};

pub struct JoinError;

impl std::fmt::Display for JoinError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "task failed")
  }
}

impl std::fmt::Debug for JoinError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "JoinError")
  }
}

impl std::error::Error for JoinError {}

impl From<JoinError> for std::io::Error {
  fn from(e: JoinError) -> Self {
    std::io::Error::other(e)
  }
}

struct JoinState<T> {
  result: Option<T>,
  waker: Option<Waker>,
}

pub struct JoinHandle<T> {
  state: Arc<Mutex<JoinState<T>>>,
}

impl<T> JoinHandle<T> {
  pub fn abort(&self) {}

  pub fn new() -> (Self, JoinSender<T>) {
    let state = Arc::new(Mutex::new(JoinState {
      result: None,
      waker: None,
    }));
    let handle = JoinHandle { state: state.clone() };
    let sender = JoinSender { state };
    (handle, sender)
  }
}

impl<T> Future for JoinHandle<T> {
  type Output = Result<T, JoinError>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<T, JoinError>> {
    let mut state = self.state.lock().unwrap();

    if let Some(result) = state.result.take() {
      Poll::Ready(Ok(result))
    } else {
      state.waker = Some(cx.waker().clone());
      Poll::Pending
    }
  }
}

pub struct JoinSender<T> {
  state: Arc<Mutex<JoinState<T>>>,
}

impl<T> JoinSender<T> {
  pub fn complete(self, result: T) {
    let mut state = self.state.lock().unwrap();
    state.result = Some(result);
    if let Some(waker) = state.waker.take() {
      waker.wake();
    }
  }
}

unsafe impl<T: Send> Send for JoinSender<T> {}
