// Trusted glue: a TCP listener over a raw fd, driven by the verified IoKernel
// (method Accept). Like the stream glue this whole module is the trust
// boundary — `verus::trusted` under Verus, plain Rust under cargo.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::net::tcp::method::IoMethod;
use crate::net::tcp::ops::SocketOps;
use crate::net::tcp::stream::{Dir, IoResource};
use lion_reactor::{RawFd, ResourceId};
use std::io;
use std::task::{Context, Poll};

/// A bound, listening, non-blocking socket registered with the current
/// thread's Lion reactor. Like [`TcpStream`](crate::TcpStream) it does not own
/// the fd, which must stay open until the listener is dropped.
pub struct TcpListener {
  io: IoResource,
}

impl TcpListener {
  /// Registers `fd`, a listening non-blocking socket, with the current
  /// thread's reactor.
  pub fn from_raw_fd(fd: RawFd) -> io::Result<TcpListener> {
    Ok(TcpListener { io: IoResource::new(fd)? })
  }

  /// The registered fd.
  pub fn as_raw_fd(&self) -> RawFd {
    self.io.as_raw_fd()
  }

  /// The reactor's io resource id.
  pub fn resource_id(&self) -> Option<ResourceId> {
    self.io.resource_id()
  }

  /// Runs the accept operation `f` when the listener may be readable. `Ready`
  /// with its result unless it returned `WouldBlock` or the listener was not
  /// readable; then `Pending`, with `cx.waker()` registered for the next
  /// connection.
  pub fn poll_accept_with<R>(&mut self, cx: &mut Context<'_>, f: impl FnOnce(RawFd) -> io::Result<R>) -> Poll<io::Result<R>> {
    self.io.poll_io(Dir::Read, IoMethod::Accept, cx, f)
  }

  /// `accept4(2)` through `ops`: the new connection's fd, non-blocking, owned
  /// by the caller.
  pub fn poll_accept<O: SocketOps + ?Sized>(&mut self, cx: &mut Context<'_>, ops: &O) -> Poll<io::Result<RawFd>> {
    self.io.poll_io(Dir::Read, IoMethod::Accept, cx, |fd: RawFd| -> io::Result<RawFd> { ops.accept(fd) })
  }
}

impl std::fmt::Debug for TcpListener {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("TcpListener").field("fd", &self.as_raw_fd()).finish()
  }
}
