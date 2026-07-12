// Trusted glue: a real TcpStream wrapping the verified IoKernel. This whole
// module is the trust boundary (mio sockets, real syscalls, Pin/Waker, the
// reactor) — `verus::trusted` under Verus, plain Rust under cargo. The kernel's
// verified poll_step/new/drop_step are invoked at exactly the points where the
// real reactor effects happen (register / set_waker / deregister), so the logical
// event log it maintains stays faithful to the real I/O.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::net::addr::ToSocketAddrs;
use crate::net::tcp::kernel::{IoAction, IoKernel};
use crate::net::tcp::method::IoMethod;
use lion_executor::create_reactor_waker_for_current;
use lion_reactor::readiness;
use lion_reactor::{Interest, IoResult, ReactorHandle, ResourceId, Source, Waker};
use std::cell::UnsafeCell;
use std::future::Future;
use std::io::{ErrorKind, Read, Result, Write};
use std::net::SocketAddr;
use std::os::unix::io::{AsRawFd, RawFd};
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll};
use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};

pub struct TcpStream {
  inner: mio::net::TcpStream,
  resource_id: ResourceId,
  kernel: IoKernel,
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

  pub(crate) fn from_mio(mut stream: mio::net::TcpStream) -> Result<TcpStream> {
    let handle = ReactorHandle::new();
    let mut source = Source::new(&mut stream as &mut dyn mio::event::Source);
    let resource_id = match handle.register_io_resource(&mut source, Interest::READABLE_WRITABLE) {
      IoResult::Ok(id) => id,
      IoResult::Err(e) => return Err(std::io::Error::new(ErrorKind::Other, format!("{:?}", e))),
    };
    readiness::init_readiness(resource_id);
    let kernel = IoKernel::new(resource_id.0);
    Ok(TcpStream { inner: stream, resource_id, kernel })
  }

  pub fn local_addr(&self) -> Result<SocketAddr> { self.inner.local_addr() }
  pub fn peer_addr(&self) -> Result<SocketAddr> { self.inner.peer_addr() }
  pub fn set_nodelay(&self, nodelay: bool) -> Result<()> { self.inner.set_nodelay(nodelay) }
  pub fn nodelay(&self) -> Result<bool> { self.inner.nodelay() }

  pub fn resource_id(&self) -> ResourceId { self.resource_id }

  pub fn poll_read_ready(&self, cx: &mut Context<'_>) -> Poll<Result<()>> {
    if readiness::is_readable(self.resource_id) {
      Poll::Ready(Ok(()))
    } else {
      cx.waker().wake_by_ref();
      Poll::Pending
    }
  }

  pub fn try_io<R, I>(&self, _interest: I, f: impl FnOnce() -> Result<R>) -> Result<R> {
    match f() {
      Ok(v) => Ok(v),
      Err(e) if e.kind() == ErrorKind::WouldBlock => {
        readiness::clear_readable(self.resource_id);
        Err(e)
      }
      Err(e) => Err(e),
    }
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
  fn poll_read(self: Pin<&mut Self>, _cx: &mut Context<'_>, buf: &mut ReadBuf<'_>) -> Poll<Result<()>> {
    let this = self.get_mut();
    let handle = ReactorHandle::new();

    // Observe the raw facts; the kernel decides Arm vs Complete.
    let was_ready = readiness::is_readable(this.resource_id);
    let mut would_block = false;
    let mut completed: Poll<Result<()>> = Poll::Ready(Ok(()));
    if was_ready {
      let unfilled = unsafe {
        let u = buf.unfilled_mut();
        std::slice::from_raw_parts_mut(u.as_mut_ptr() as *mut u8, u.len())
      };
      let len = unfilled.len();
      match this.inner.read(unfilled) {
        Ok(n) => {
          if 0 < n && n < len { readiness::clear_readable(this.resource_id); }
          unsafe { buf.assume_init(n); }
          buf.advance(n);
          completed = Poll::Ready(Ok(()));
        }
        Err(ref e) if e.kind() == ErrorKind::WouldBlock => {
          would_block = true;
          readiness::clear_readable(this.resource_id);
        }
        Err(e) => { completed = Poll::Ready(Err(e)); }
      }
    }

    match this.kernel.poll_step(IoMethod::Read, was_ready, would_block) {
      IoAction::Arm => {
        let waker = Waker::from_std(create_reactor_waker_for_current());
        handle.set_waker(this.resource_id, Interest::READABLE, waker);
        Poll::Pending
      }
      IoAction::Complete => completed,
    }
  }
}

impl AsyncWrite for TcpStream {
  fn poll_write(self: Pin<&mut Self>, _cx: &mut Context<'_>, buf: &[u8]) -> Poll<Result<usize>> {
    let this = self.get_mut();
    let handle = ReactorHandle::new();

    let was_ready = readiness::is_writable(this.resource_id);
    let mut would_block = false;
    let mut completed: Poll<Result<usize>> = Poll::Ready(Ok(0));
    if was_ready {
      let len = buf.len();
      match this.inner.write(buf) {
        Ok(n) => {
          if 0 < n && n < len { readiness::clear_writable(this.resource_id); }
          completed = Poll::Ready(Ok(n));
        }
        Err(ref e) if e.kind() == ErrorKind::WouldBlock => {
          would_block = true;
          readiness::clear_writable(this.resource_id);
        }
        Err(e) => { completed = Poll::Ready(Err(e)); }
      }
    }

    match this.kernel.poll_step(IoMethod::Write, was_ready, would_block) {
      IoAction::Arm => {
        let waker = Waker::from_std(create_reactor_waker_for_current());
        handle.set_waker(this.resource_id, Interest::WRITABLE, waker);
        Poll::Pending
      }
      IoAction::Complete => completed,
    }
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
// thread-per-core ⇒ no cross-thread sharing of a stream ⇒ the UnsafeCell + unsafe
// Send is sound. Both halves' polls go through the SAME verified IoKernel, so this
// adds no new proof obligation — it reuses the stream's verified poll path.
pub struct OwnedReadHalf {
  inner: Arc<UnsafeCell<TcpStream>>,
}

pub struct OwnedWriteHalf {
  inner: Arc<UnsafeCell<TcpStream>>,
}

unsafe impl Send for OwnedReadHalf {}
unsafe impl Send for OwnedWriteHalf {}

impl TcpStream {
  pub fn into_split(self) -> (OwnedReadHalf, OwnedWriteHalf) {
    let arc = Arc::new(UnsafeCell::new(self));
    (OwnedReadHalf { inner: arc.clone() }, OwnedWriteHalf { inner: arc })
  }
}

impl AsyncRead for OwnedReadHalf {
  fn poll_read(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &mut ReadBuf<'_>) -> Poll<Result<()>> {
    let stream = unsafe { &mut *self.inner.get() };
    Pin::new(stream).poll_read(cx, buf)
  }
}

impl AsyncWrite for OwnedWriteHalf {
  fn poll_write(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &[u8]) -> Poll<Result<usize>> {
    let stream = unsafe { &mut *self.inner.get() };
    Pin::new(stream).poll_write(cx, buf)
  }
  fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<()>> {
    let stream = unsafe { &mut *self.inner.get() };
    Pin::new(stream).poll_flush(cx)
  }
  fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<()>> {
    let stream = unsafe { &mut *self.inner.get() };
    Pin::new(stream).poll_shutdown(cx)
  }
}

impl Drop for TcpStream {
  fn drop(&mut self) {
    let handle = ReactorHandle::new();
    let mut source = Source::new(&mut self.inner as &mut dyn mio::event::Source);
    let _ = handle.deregister_io_resource(self.resource_id, &mut source);
    self.kernel.drop_step();
  }
}

pub(crate) struct Connect {
  stream: Option<TcpStream>,
}

impl Connect {
  pub(crate) fn from_mio(mio_stream: mio::net::TcpStream) -> Result<Self> {
    Self::new(mio_stream)
  }

  fn new(mut mio_stream: mio::net::TcpStream) -> Result<Self> {
    let handle = ReactorHandle::new();
    let mut source = Source::new(&mut mio_stream as &mut dyn mio::event::Source);
    let resource_id = match handle.register_io_resource(&mut source, Interest::READABLE_WRITABLE) {
      IoResult::Ok(id) => id,
      IoResult::Err(e) => return Err(std::io::Error::new(ErrorKind::Other, format!("{:?}", e))),
    };
    readiness::init_readiness(resource_id);
    let kernel = IoKernel::new(resource_id.0);
    Ok(Connect { stream: Some(TcpStream { inner: mio_stream, resource_id, kernel }) })
  }
}

impl Future for Connect {
  type Output = Result<TcpStream>;

  fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
    let stream = self.stream.as_ref().expect("Connect polled after completion");
    let handle = ReactorHandle::new();

    if readiness::is_writable(stream.resource_id) {
      if let Some(e) = stream.inner.take_error()? {
        return Poll::Ready(Err(e));
      }
      match stream.inner.peer_addr() {
        // Connected: KEEP the writable flag. The socket is genuinely writable
        // right now, and under edge-triggered epoll the connect-completion
        // edge is the last writable edge until a full send buffer drains —
        // clearing here would send the first poll_write into a wait for an
        // edge that never comes (the zoo-004 lost-wakeup hang: the two-poll
        // connect path consumed the real edge's flag and wedged the client
        // task forever). poll_write's own WouldBlock path clears + arms with
        // drain justification, which is the only ET-safe place to do it.
        Ok(_) => return Poll::Ready(Ok(self.stream.take().unwrap())),
        Err(ref e) if e.kind() == ErrorKind::NotConnected => {
          // Not connected yet: the flag we saw was the optimistic init (or a
          // stale signal); consume it before arming so the next wake is
          // edge-driven.
          readiness::clear_writable(stream.resource_id);
        }
        Err(e) => return Poll::Ready(Err(e)),
      }
    }

    let waker = Waker::from_std(create_reactor_waker_for_current());
    handle.set_waker(stream.resource_id, Interest::WRITABLE, waker);
    Poll::Pending
  }
}
