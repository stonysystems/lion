// Trusted glue: the socket seam. Plain Rust that Verus never sees.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

//! The socket operations an embedder supplies.
//!
//! A [`TcpStream`](crate::TcpStream) or [`TcpListener`](crate::TcpListener)
//! performs no syscall of its own. The primitive form passes each operation as
//! a closure over the raw fd (`poll_read_with`, `poll_write_with`,
//! `poll_accept_with`); the convenience form (`poll_read`, `poll_write`,
//! `poll_accept`) takes the embedder's [`SocketOps`], generically, so an
//! embedder's zero-sized implementation costs no indirection. The trait holds
//! exactly the operations the stream and listener perform: `shutdown(2)`,
//! `getsockopt(SO_ERROR)`, `connect(2)` and `close(2)` stay with the owner of
//! the fd, which needs no readiness to perform them.
//!
//! # The contract
//!
//! * Every fd is a non-blocking socket. An operation that cannot proceed
//!   returns an error of kind `WouldBlock` (`EAGAIN`/`EWOULDBLOCK`); the
//!   stream then waits for the next readiness edge. Any other error is
//!   returned to the caller as it is (`Interrupted` is not retried), and should
//!   carry the errno (`io::Error::from_raw_os_error`).
//! * `recv` is `recv(2)`: `Ok(0)` is end of stream (for a non-empty `buf`).
//! * `send` is `send(2)` with SIGPIPE suppressed (`MSG_NOSIGNAL`).
//! * `accept` is `accept4(2)` on a listening fd. The returned fd is already
//!   non-blocking (and close-on-exec); the caller owns it.
//! * No operation closes the fd. The owner closes it after the stream or
//!   listener that wraps it is dropped.
//!
//! All methods run on the thread of the reactor the socket is registered with.

use lion_reactor::RawFd;
use std::io;

/// The socket syscalls a stream or listener performs, supplied by the
/// embedder. See the module documentation for the contract.
pub trait SocketOps {
  /// `recv(2)` into `buf`.
  fn recv(&self, fd: RawFd, buf: &mut [u8]) -> io::Result<usize>;

  /// `send(2)` from `buf`, without SIGPIPE.
  fn send(&self, fd: RawFd, buf: &[u8]) -> io::Result<usize>;

  /// `accept4(2)`: a new non-blocking, close-on-exec connection fd.
  fn accept(&self, listener: RawFd) -> io::Result<RawFd>;
}
