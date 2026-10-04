// Plain-build lint allowances: imports/variables flagged unused here are used
// by ghost/proof code that plain `cargo build` (no Verus cfg) cannot see.
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_parens)]
#![allow(dead_code)]

//! Lion's TCP stream and listener over a raw fd, with no OS dependency.
//!
//! [`TcpStream`] wraps a connected, non-blocking socket and [`TcpListener`] a
//! bound, listening one. The embedder creates the socket, keeps it open until
//! the stream or listener is dropped, and closes it afterwards: neither type
//! owns the fd or performs a syscall of its own. Each operation is the
//! embedder's, passed as a closure over the raw fd (`poll_read_with`,
//! `poll_write_with`, `poll_accept_with`) or through a [`SocketOps`]
//! implementation taken generically (`poll_read`, `poll_write`,
//! `poll_accept`), so a zero-sized implementation costs no indirection. The
//! crate depends on lion-reactor without its `mio` feature, the Verus
//! standard library and the spec crates, and nothing else.
//!
//! # What is verified and what is trusted
//!
//! * **Verified** (`net/tcp/{method,kernel,proof}.rs`, inside `verus!`): the
//!   io kernel. `IoKernel::poll_step(method, was_ready, would_block)` decides
//!   each poll: `Arm` (suspend) exactly when `!was_ready || would_block`,
//!   `Complete` otherwise, and appends the poll's segment to the utility io
//!   log, preserving its invariant: the wakeup guarantee (a `Pending` tick
//!   has an io waker set in its own cycle, on a resource still registered)
//!   and resource ownership (every resource event names a registered
//!   resource). `new` and `drop_step` record registration and
//!   deregistration. The kernel's waker is a ghost `arbitrary()`, and the log
//!   is this utility's own: no theorem links it to lion-liveness's composed
//!   model (see TCB_and_limitations.md).
//! * **Trusted** (`net/tcp/{stream,listener,ops}.rs`, whole files marked
//!   `verus::trusted`, plain Rust Verus never sees): the glue that feeds the
//!   kernel truthful observations and carries out its decision. Per poll it
//!   reads the direction's readiness flag (`was_ready`), runs the operation
//!   through AsyncFd's ready guard if the flag is set (`would_block` is
//!   whether it returned `WouldBlock`), calls `poll_step`, and on `Arm`
//!   registers `cx.waker()` for the direction and returns `Pending`; on
//!   `Complete` it returns the operation's result. Also trusted: that the
//!   real waker registered is the one the kernel's ghost waker stands for,
//!   the embedder's syscalls (the [`SocketOps`] contract), and lion-reactor's
//!   `AsyncFd` and readiness table beneath.
//!
//! The decision is enforced by construction: the glue returns `Pending` only
//! on the kernel's `Arm`, and then only after registering the caller's waker
//! (or, should the registration find the flag set again or fail, after
//! waking the caller, whose next poll observes again).
//!
//! # Invariants inherited from `AsyncFd`
//!
//! Readiness is lion-reactor's `AsyncFd` (its module comment states the
//! protocol); the stream adds no flag logic of its own:
//!
//! 1. Only a park sets a flag, so a poll is atomic with respect to readiness.
//! 2. Only an operation that returned `WouldBlock` clears a flag, only that
//!    direction's, in the same poll. A short read or write, a successful
//!    accept or connect, and a readiness wait leave it set; the next
//!    operation finds out.
//! 3. A waiting poll registers the waker, re-checks the flag, then returns
//!    `Pending`.
//! 4. The waker stored is the caller's `cx.waker()`, one per direction: a
//!    wait allocates nothing, a combinator's sub-future is the one woken, and
//!    a reader task and a writer task can share one stream.
//! 5. Both flags start set, so the first operation discovers the real state.
//!
//! Like `AsyncFd`, a stream or listener is `Send` and `Sync` (no `unsafe
//! impl`): every use first checks that the thread's current reactor is the
//! one it registered with, so used anywhere else it fails closed (an error,
//! the operation not run, no waker armed) and its drop leaves the
//! registration to its own reactor. Dropping it on its own reactor
//! deregisters the fd, before the owner closes it; the kernel's `drop_step`
//! records that after the real deregistration.

pub mod net;

pub use net::tcp::listener::TcpListener;
pub use net::tcp::ops::SocketOps;
pub use net::tcp::stream::TcpStream;
