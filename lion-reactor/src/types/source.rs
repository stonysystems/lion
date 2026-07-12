use vstd::prelude::*;
use crate::spec::types::SourceView;

verus! {

#[verifier::external_body]
pub struct Source<'a> {
  pub(crate) inner: &'a mut dyn mio::event::Source,
}

impl View for Source<'_> {
  type V = SourceView;

  #[verifier::external_body]
  spec fn view(&self) -> SourceView {
    unimplemented!()
  }
}

} // end verus!

impl<'a> Source<'a> {
  pub fn new(source: &'a mut dyn mio::event::Source) -> Self {
    Source { inner: source }
  }
}
