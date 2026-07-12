// Reactor log predicates, re-exported from the shared crate lion-reactor-spec.
// IO ANCHOR (F-K): this crate's io registration predicates are the
// syscall-anchor family (io_syscall_registered_at etc.); lion-reactor uses the
// API-anchor family (io_api_*). See lion-reactor-spec::bridge.
#[allow(unused_imports)]
pub use lion_reactor_spec::log::*;
