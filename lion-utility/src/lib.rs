// Plain-build lint allowances: imports/variables flagged unused here are used
// by ghost/proof code that plain `cargo build` (no Verus cfg) cannot see.
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_parens)]
#![allow(dead_code)]

// Formally verified Lion async utilities.
//
// Each utility is split into a VERIFIED KERNEL (a small, pure state machine,
// Verus exec code + proofs, that maintains the universal utility invariants of
// `lion-utility-spec`) and GLUE (the Future/poll shim that performs the real
// reactor I/O and waker delivery). Each glue module is trusted as a WHOLE FILE
// (`#![cfg_attr(verus_keep_ghost, verus::trusted)]`): it is plain Rust that is
// invisible to Verus, so kernel `requires` clauses are upheld by convention at
// glue call sites, not checked by the verifier. Regression tests
// (tests/cancel.rs, tests/decisions.rs) guard the glue conventions the
// verifier cannot.

pub mod time;
pub mod net;
pub mod fs;
pub mod sync;
pub mod task;
pub use task::yield_now;
