// The reactor-side view types now live in the shared `lion-utility-spec` crate
// (shared vocabulary between reactor, utilities, and the composition proof).
// Re-exported here so existing `crate::reactor::spec::types::...` paths resolve.
pub use lion_utility_spec::view_types::*;
