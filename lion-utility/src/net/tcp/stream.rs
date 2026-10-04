// Trusted glue: Lion's tokio-shaped TcpStream (feature `mio`): a mio socket
// that owns the fd, plus lion-net's TcpStream, which registers it and drives
// every poll through the verified IoKernel and lion-reactor's AsyncFd. This
// whole module is the trust boundary — `verus::trusted` under Verus, plain Rust
// under cargo. It writes no readiness protocol of its own: every flag is read,
// cleared and waited on through lion-net (hence AsyncFd).
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::net::addr::ToSocketAddrs;
use lion_reactor::{Interest, ResourceId};
use std::future::Future;
use std::io::{ErrorKind, Read, Result, Write};
use std::net::SocketAddr;
use std::os::unix::io::{AsRawFd, RawFd};
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll};
use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};

// Fields drop in declaration order: `core` deregisters the fd before `inner`
// closes it.
pub struct TcpStream {
  core: lion_net::TcpStream,
  inner: mio::net::TcpStream,
}

impl TcpStream {
  pub async fn connect<A: ToSocketAddrs>(addr: A) -> Result<TcpStream> {
    let addrs = addr.to_socket_addrs()?;
    let mut last_err = None;
    for addr in addrs {
      match mio::net::TcpStream::connect(addr) {
        Ok(stream) => return Connect::new(stream)?.await,
        Err(e) => last_err = Some(e),
      }
    }
    Err(last_err.unwrap_or_else(|| {
      std::io::Error::new(ErrorKind::InvalidInput, "could not resolve to any addresses")
    }))
  }

  pub fn from_std(stream: std::net::TcpStream) -> Result<TcpStream> {
    stream.set_nonblocking(true)?;
    Self::from_mio(mio::net::TcpStream::from_std(stream))
  }

  pub(crate) fn from_mio(stream: mio::net::TcpStream) -> Result<TcpStream> {
    let core = lion_net::TcpStream::from_raw_fd(stream.as_raw_fd())?;
    Ok(TcpStream { core, inner: stream })
  }

  pub fn local_addr(&self) -> Result<SocketAddr> { self.inner.local_addr() }
  pub fn peer_addr(&self) -> Result<SocketAddr> { self.inner.peer_addr() }
  pub fn set_nodelay(&self, nodelay: bool) -> Result<()> { self.inner.set_nodelay(nodelay) }
  pub fn nodelay(&self) -> Result<bool> { self.inner.nodelay() }

  pub fn resource_id(&self) -> ResourceId {
    self.core.resource_id().expect("a live stream is registered")
  }

  /// Ready when the stream may be readable; otherwise `Pending` with
  /// `cx.waker()` registered for the next read edge. (It used to wake the
  /// task at once and return `Pending`, a busy loop.)
  pub fn poll_read_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<()>> {
    self.core.poll_read_ready(cx)
  }

  /// As [`poll_read_ready`](TcpStream::poll_read_ready), for writability.
  pub fn poll_write_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<()>> {
    self.core.poll_write_ready(cx)
  }

  /// Runs `f` if the stream may be ready in the direction `interest` names,
  /// and clears that direction's readiness iff `f` returns `WouldBlock`;
  /// returns `WouldBlock` without running `f` if it is not ready. An interest
  /// naming both directions is treated as readable, and one naming neither
  /// returns `WouldBlock`. The interest is Lion's (`lion_reactor::Interest`,
  /// `lion::io::Interest` in the facade), not tokio's. (It used to accept
  /// any type, run `f` regardless of readiness and always clear the *read*
  /// readiness, whatever the interest.)
  pub fn try_io<R>(&self, interest: Interest, f: impl FnOnce() -> Result<R>) -> Result<R> {
    if interest.readable {
      return self.core.try_read_io(|_fd| f());
    }
    if interest.writable {
      return self.core.try_write_io(|_fd| f());
    }
    Err(std::io::Error::from(ErrorKind::WouldBlock))
  }
}

impl AsRawFd for TcpStream {
  fn as_raw_fd(&self) -> RawFd {
    self.inner.as_raw_fd()
  }
}

impl std::fmt::Debug for TcpStream {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("TcpStream").field("fd", &self.inner.as_raw_fd()).finish()
  }
}

impl AsyncRead for TcpStream {
  fn poll_read(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &mut ReadBuf<'_>) -> Poll<Result<()>> {
    let this = self.get_mut();
    let inner = &this.inner;
    let unfilled = unsafe {
      let u = buf.unfilled_mut();
      std::slice::from_raw_parts_mut(u.as_mut_ptr() as *mut u8, u.len())
    };
    match this.core.poll_read_with(cx, |_fd| { let mut r = inner; r.read(unfilled) }) {
      Poll::Ready(Ok(n)) => {
        unsafe { buf.assume_init(n); }
        buf.advance(n);
        Poll::Ready(Ok(()))
      }
      Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
      Poll::Pending => Poll::Pending,
    }
  }
}

impl AsyncWrite for TcpStream {
  fn poll_write(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &[u8]) -> Poll<Result<usize>> {
    let this = self.get_mut();
    let inner = &this.inner;
    this.core.poll_write_with(cx, |_fd| { let mut w = inner; w.write(buf) })
  }

  fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Result<()>> {
    Poll::Ready(Ok(()))
  }

  fn poll_shutdown(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Result<()>> {
    let this = self.get_mut();
    this.inner.shutdown(std::net::Shutdown::Write)?;
    Poll::Ready(Ok(()))
  }
}

// ── into_split: two owned halves sharing one TcpStream (hence one IoKernel) ──
// The halves share the stream through a Mutex, so they are Send and Sync by
// construction, with no `unsafe impl`. On Lion's thread-per-core runtime both
// halves are polled on the stream's reactor thread, so the lock is never
// contended; polled from another thread, the stream fails closed (AsyncFd's
// reactor check). Both halves' polls go through the SAME verified IoKernel.
pub struct OwnedReadHalf {
  inner: Arc<Mutex<TcpStream>>,
}

pub struct OwnedWriteHalf {
  inner: Arc<Mutex<TcpStream>>,
}

impl TcpStream {
  pub fn into_split(self) -> (OwnedReadHalf, OwnedWriteHalf) {
    let arc = Arc::new(Mutex::new(self));
    (OwnedReadHalf { inner: arc.clone() }, OwnedWriteHalf { inner: arc })
  }
}

fn lock(stream: &Mutex<TcpStream>) -> std::sync::MutexGuard<'_, TcpStream> {
  stream.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

impl AsyncRead for OwnedReadHalf {
  fn poll_read(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &mut ReadBuf<'_>) -> Poll<Result<()>> {
    let mut stream = lock(&self.inner);
    Pin::new(&mut *stream).poll_read(cx, buf)
  }
}

impl AsyncWrite for OwnedWriteHalf {
  fn poll_write(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &[u8]) -> Poll<Result<usize>> {
    let mut stream = lock(&self.inner);
    Pin::new(&mut *stream).poll_write(cx, buf)
  }
  fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<()>> {
    let mut stream = lock(&self.inner);
    Pin::new(&mut *stream).poll_flush(cx)
  }
  fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<()>> {
    let mut stream = lock(&self.inner);
    Pin::new(&mut *stream).poll_shutdown(cx)
  }
}

// Waits for a non-blocking connect to finish: the stream's first write
// readiness, through the kernel like any write wait. "Not connected yet" is
// the connect's WouldBlock, so it alone consumes the write readiness, in the
// poll that observed it; a completed connect leaves the readiness set for the
// first write (the zoo-004 lesson: the connect-completion edge may be the last
// writable edge until the send buffer fills).
pub(crate) struct Connect {
  stream: Option<TcpStream>,
}

impl Connect {
  pub(crate) fn from_mio(mio_stream: mio::net::TcpStream) -> Result<Self> {
    Self::new(mio_stream)
  }

  fn new(mio_stream: mio::net::TcpStream) -> Result<Self> {
    Ok(Connect { stream: Some(TcpStream::from_mio(mio_stream)?) })
  }
}

impl Future for Connect {
  type Output = Result<TcpStream>;

  fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let stream = self.stream.as_mut().expect("Connect polled after completion");
    let inner = &stream.inner;
    let connected = stream.core.poll_write_with(cx, |_fd| {
      if let Some(e) = inner.take_error()? {
        return Err(e);
      }
      match inner.peer_addr() {
        Ok(_) => Ok(()),
        Err(ref e) if e.kind() == ErrorKind::NotConnected => Err(std::io::Error::from(ErrorKind::WouldBlock)),
        Err(e) => Err(e),
      }
    });
    match connected {
      Poll::Ready(Ok(())) => Poll::Ready(Ok(self.stream.take().unwrap())),
      Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
      Poll::Pending => Poll::Pending,
    }
  }
}
