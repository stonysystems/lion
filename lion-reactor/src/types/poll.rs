use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub struct Poll {
  pub(crate) inner: mio::Poll,
}

impl View for Poll {
  type V = int;

  #[verifier::external_body]
  spec fn view(&self) -> int {
    unimplemented!()
  }
}

}
