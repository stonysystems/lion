use vstd::prelude::*;

verus! {

// The io utility's method tag (the `M` of UtilityEvent<M, R>). One concrete enum
// serves every reactor-io resource — TcpStream uses Read/Write, and a later
// TcpListener will add Accept — because the universal invariant ignores M.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum IoMethod {
  Read,
  Write,
  Accept,
}

// Return type R = () : the io invariant is return-value-agnostic (bytes counts
// live in the real glue, not the logical model).

}
