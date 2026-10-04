// Trusted glue: a TCP stream over a raw fd, driven by the verified IoKernel.
// This whole module is the trust boundary (the reactor, Pin/Waker, the
// embedder's syscalls) — `verus::trusted` under Verus, plain Rust under cargo.
// The kernel's verified new/poll_step/drop_step are invoked at exactly the
// points where the real reactor effects happen (register / set_waker /
// deregister), so the io log it maintains stays faithful to the real I/O.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

//! [`TcpStream`]: a connected socket, polled through the verified io kernel.
//!
//! Each poll makes two raw observations and hands them to
//! `IoKernel::poll_step`: `was_ready`, the reactor's readiness flag for the
//! direction, and `would_block`, whether the embedder's operation returned
//! `WouldBlock`. The kernel decides `Arm` exactly when
//! `!was_ready || would_block`, and the poll then follows the decision: it
//! returns the operation's result on `Complete`, and on `Arm` registers
//! `cx.waker()` for the direction and returns `Pending`.
//!
//! Readiness is lion-reactor's [`AsyncFd`] and its five invariants (see
//! `lion_reactor::async_fd`). In particular only a `WouldBlock` clears a flag,
//! and only the flag of the direction that observed it, through the ready
//! guard; a short read or write leaves it set, so the next poll's operation
//! finds out (one more syscall, which returns `WouldBlock` if nothing arrived
//! meanwhile). The waker registered is the caller's, so a wait allocates
//! nothing and a combinator's sub-future is the one woken.

use crate::net::tcp::kernel::{IoAction, IoKernel};
use crate::net::tcp::method::IoMethod;
use crate::net::tcp::ops::SocketOps;
use lion_reactor::{AsyncFd, AsyncFdReadyGuard, RawFd, ResourceId};
use std::io;
use std::task::{Context, Poll};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Dir {
  Read,
  Write,
}

/// One registered socket and its io kernel: the part a stream and a listener
/// share.
pub(crate) struct IoResource {
  // Some until drop, which takes it first: the real deregistration happens
  // before the kernel records it, whatever order a translation destroys the
  // fields in.
  fd: Option<AsyncFd>,
  kernel: IoKernel,
}

fn gone() -> io::Error {
  io::Error::new(io::ErrorKind::Other, "lion-net: socket used after its registration was released")
}

// Observation only (AsyncFd invariant 1: nothing sets a flag within a poll).
fn observe(fd: &AsyncFd, dir: Dir) -> io::Result<Option<AsyncFdReadyGuard<'_>>> {
  match dir {
    Dir::Read => fd.try_read_ready(),
    Dir::Write => fd.try_write_ready(),
  }
}

// Carries out the kernel's Arm: registers `cx.waker()` for the direction and
// returns Pending (AsyncFd invariants 3 and 4). The flag is clear here: it was
// clear when observed, or the WouldBlock just cleared it, and only a park sets
// it. Should the re-check that `poll_*_ready` makes after registering find it
// set anyway, the Arm still stands, and the task wakes itself so that it polls
// again rather than sleep on readiness it has been told about. An error here
// cannot happen (the reactor check passed in this poll); it too wakes the
// task, whose next poll reports it from its observation.
fn arm<R>(fd: &AsyncFd, dir: Dir, cx: &mut Context<'_>) -> Poll<io::Result<R>> {
  let polled = match dir {
    Dir::Read => fd.poll_read_ready(cx),
    Dir::Write => fd.poll_write_ready(cx),
  };
  match polled {
    Poll::Pending => {}
    Poll::Ready(Ok(_set_meanwhile)) => cx.waker().wake_by_ref(),
    Poll::Ready(Err(_)) => cx.waker().wake_by_ref(),
  }
  Poll::Pending
}

impl IoResource {
  pub(crate) fn new(fd: RawFd) -> io::Result<IoResource> {
    let registered = AsyncFd::new(fd)?;
    let kernel = IoKernel::new(registered.resource_id().0);
    Ok(IoResource { fd: Some(registered), kernel })
  }

  pub(crate) fn as_raw_fd(&self) -> RawFd {
    match self.fd.as_ref() {
      Some(fd) => fd.as_raw_fd(),
      None => -1,
    }
  }

  pub(crate) fn resource_id(&self) -> Option<ResourceId> {
    self.fd.as_ref().map(|fd| fd.resource_id())
  }

  // One io poll: observe, run the operation if ready, let the kernel decide,
  // and follow its decision.
  pub(crate) fn poll_io<R>(
    &mut self,
    dir: Dir,
    method: IoMethod,
    cx: &mut Context<'_>,
    f: impl FnOnce(RawFd) -> io::Result<R>,
  ) -> Poll<io::Result<R>> {
    let fd: &AsyncFd = match self.fd.as_ref() {
      Some(fd) => fd,
      None => return Poll::Ready(Err(gone())),
    };
    let guard = match observe(fd, dir) {
      Ok(guard) => guard,
      Err(e) => return Poll::Ready(Err(e)),
    };
    let was_ready = guard.is_some();
    let mut would_block = false;
    let mut done: Option<io::Result<R>> = None;
    if let Some(guard) = guard {
      // The guard clears this direction's flag iff `f` returned WouldBlock
      // (AsyncFd invariant 2).
      match guard.try_io(f) {
        Err(e) if e.kind() == io::ErrorKind::WouldBlock => would_block = true,
        result => done = Some(result),
      }
    }
    match self.kernel.poll_step(method, was_ready, would_block) {
      // Complete <=> was_ready && !would_block, so `done` holds the result.
      IoAction::Complete => match done {
        Some(result) => Poll::Ready(result),
        None => Poll::Ready(Err(gone())),
      },
      IoAction::Arm => arm::<R>(fd, dir, cx),
    }
  }

  // A readiness wait through the kernel: no operation, so no WouldBlock.
  pub(crate) fn poll_ready(&mut self, dir: Dir, method: IoMethod, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
    let fd: &AsyncFd = match self.fd.as_ref() {
      Some(fd) => fd,
      None => return Poll::Ready(Err(gone())),
    };
    // The guard is not used: a Ready result obliges the caller to run its
    // operation through `try_io`, which observes again.
    let was_ready = match observe(fd, dir) {
      Ok(guard) => guard.is_some(),
      Err(e) => return Poll::Ready(Err(e)),
    };
    match self.kernel.poll_step(method, was_ready, false) {
      IoAction::Complete => Poll::Ready(Ok(())),
      IoAction::Arm => arm::<()>(fd, dir, cx),
    }
  }

  // Runs `f` if the direction may be ready, clearing it iff `f` returns
  // WouldBlock; WouldBlock without running `f` if it is not. Not a poll: it
  // registers no waker and makes no kernel step.
  pub(crate) fn try_io<R>(&self, dir: Dir, f: impl FnOnce(RawFd) -> io::Result<R>) -> io::Result<R> {
    let fd: &AsyncFd = match self.fd.as_ref() {
      Some(fd) => fd,
      None => return Err(gone()),
    };
    match observe(fd, dir)? {
      Some(guard) => guard.try_io(f),
      None => Err(io::Error::from(io::ErrorKind::WouldBlock)),
    }
  }
}

impl Drop for IoResource {
  fn drop(&mut self) {
    let registration: Option<AsyncFd> = self.fd.take();
    drop(registration);
    self.kernel.drop_step();
  }
}

/// A connected, non-blocking TCP socket registered with the current thread's
/// Lion reactor.
///
/// The stream does not own the fd: it never reads, writes or closes it
/// itself, and the owner must keep it open until the stream is dropped. Every
/// poll takes `&mut self`; owners that share a stream between a reader and a
/// writer task keep it in a `RefCell` (one thread) or a `Mutex`.
pub struct TcpStream {
  io: IoResource,
}

impl TcpStream {
  /// Registers `fd`, a connected non-blocking socket, with the current
  /// thread's reactor for read and write readiness. Fails if no Lion reactor
  /// is entered on this thread or the backend refuses the fd.
  pub fn from_raw_fd(fd: RawFd) -> io::Result<TcpStream> {
    Ok(TcpStream { io: IoResource::new(fd)? })
  }

  /// The registered fd.
  pub fn as_raw_fd(&self) -> RawFd {
    self.io.as_raw_fd()
  }

  /// The reactor's io resource id.
  pub fn resource_id(&self) -> Option<ResourceId> {
    self.io.resource_id()
  }

  /// Runs the read operation `f` when the socket may be readable. `Ready`
  /// with its result unless it returned `WouldBlock` or the socket was not
  /// readable; then `Pending`, with `cx.waker()` registered for the next read
  /// edge.
  pub fn poll_read_with<R>(&mut self, cx: &mut Context<'_>, f: impl FnOnce(RawFd) -> io::Result<R>) -> Poll<io::Result<R>> {
    self.io.poll_io(Dir::Read, IoMethod::Read, cx, f)
  }

  /// As [`poll_read_with`](TcpStream::poll_read_with), for a write operation.
  pub fn poll_write_with<R>(&mut self, cx: &mut Context<'_>, f: impl FnOnce(RawFd) -> io::Result<R>) -> Poll<io::Result<R>> {
    self.io.poll_io(Dir::Write, IoMethod::Write, cx, f)
  }

  /// `recv(2)` through `ops` into `buf`.
  pub fn poll_read<O: SocketOps + ?Sized>(&mut self, cx: &mut Context<'_>, ops: &O, buf: &mut [u8]) -> Poll<io::Result<usize>> {
    self.io.poll_io(Dir::Read, IoMethod::Read, cx, |fd: RawFd| -> io::Result<usize> { ops.recv(fd, buf) })
  }

  /// `send(2)` through `ops` from `buf`.
  pub fn poll_write<O: SocketOps + ?Sized>(&mut self, cx: &mut Context<'_>, ops: &O, buf: &[u8]) -> Poll<io::Result<usize>> {
    self.io.poll_io(Dir::Write, IoMethod::Write, cx, |fd: RawFd| -> io::Result<usize> { ops.send(fd, buf) })
  }

  /// Ready when the socket may be readable; otherwise `Pending` with
  /// `cx.waker()` registered. A `Ready` obliges the caller to read through
  /// [`try_read_io`](TcpStream::try_read_io) until it returns `WouldBlock`
  /// before waiting again; otherwise nothing will wake it.
  pub fn poll_read_ready(&mut self, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
    self.io.poll_ready(Dir::Read, IoMethod::Read, cx)
  }

  /// As [`poll_read_ready`](TcpStream::poll_read_ready), for writability.
  pub fn poll_write_ready(&mut self, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
    self.io.poll_ready(Dir::Write, IoMethod::Write, cx)
  }

  /// Runs `f` if the socket may be readable, and clears the read readiness
  /// iff `f` returns `WouldBlock`; returns `WouldBlock` without running `f` if
  /// it is not readable. Registers no waker.
  pub fn try_read_io<R>(&self, f: impl FnOnce(RawFd) -> io::Result<R>) -> io::Result<R> {
    self.io.try_io(Dir::Read, f)
  }

  /// As [`try_read_io`](TcpStream::try_read_io), for a write operation and
  /// the write readiness.
  pub fn try_write_io<R>(&self, f: impl FnOnce(RawFd) -> io::Result<R>) -> io::Result<R> {
    self.io.try_io(Dir::Write, f)
  }
}

impl std::fmt::Debug for TcpStream {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("TcpStream").field("fd", &self.as_raw_fd()).finish()
  }
}
