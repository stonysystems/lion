use super::IoResult;
use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub struct IoEventQueue {
  pub(crate) inner: mio::Events,
}

impl View for IoEventQueue {
  type V = int;

  #[verifier::external_body]
  spec fn view(&self) -> int {
    unimplemented!()
  }
}

impl IoEventQueue {
  #[verifier::external_body]
  pub fn with_capacity(capacity: usize) -> IoResult<Self> {
    IoResult::Ok(IoEventQueue {
      inner: mio::Events::with_capacity(capacity),
    })
  }
}

}
