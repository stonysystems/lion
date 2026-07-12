// Trusted glue: a real UdpSocket wrapping the verified IoKernel (one kernel for
// the socket; recv uses the Read direction, send the Write direction). Like the
// TCP glue, the kernel decides Arm-vs-Complete at the points where the real
// reactor effects (set_waker) happen, so the logical event log stays faithful.
// recv_from/send_to take &self (matching tokio), so the kernel sits behind an
// UnsafeCell (thread-per-core ⇒ sound). verus::trusted under Verus, plain Rust
// under cargo.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::net::addr::ToSocketAddrs;
use crate::net::tcp::kernel::{IoAction, IoKernel};
use crate::net::tcp::method::IoMethod;
use lion_executor::create_reactor_waker_for_current;
use lion_reactor::readiness;
use lion_reactor::{Interest, IoResult, ReactorHandle, ResourceId, Source, Waker};
use std::cell::UnsafeCell;
use std::future::Future;
use std::io::{ErrorKind, Result};
use std::net::SocketAddr;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct UdpSocket {
  inner: mio::net::UdpSocket,
  resource_id: ResourceId,
  kernel: UnsafeCell<IoKernel>,
}

unsafe impl Send for UdpSocket {}
unsafe impl Sync for UdpSocket {}

impl UdpSocket {
  pub async fn bind<A: ToSocketAddrs>(addr: A) -> Result<UdpSocket> {
    let addrs = addr.to_socket_addrs()?;
    let mut last_err = None;
    for addr in addrs {
      match mio::net::UdpSocket::bind(addr) {
        Ok(socket) => return Self::new(socket),
        Err(e) => last_err = Some(e),
      }
    }
    Err(last_err.unwrap_or_else(|| {
      std::io::Error::new(ErrorKind::InvalidInput, "could not resolve to any addresses")
    }))
  }

  fn new(mut socket: mio::net::UdpSocket) -> Result<UdpSocket> {
    let handle = ReactorHandle::new();
    let mut source = Source::new(&mut socket as &mut dyn mio::event::Source);
    let resource_id = match handle.register_io_resource(&mut source, Interest::READABLE_WRITABLE) {
      IoResult::Ok(id) => id,
      IoResult::Err(e) => return Err(std::io::Error::new(ErrorKind::Other, format!("{:?}", e))),
    };
    readiness::init_readiness(resource_id);
    let kernel = IoKernel::new(resource_id.0);
    Ok(UdpSocket { inner: socket, resource_id, kernel: UnsafeCell::new(kernel) })
  }

  pub fn from_std(socket: std::net::UdpSocket) -> Result<UdpSocket> {
    socket.set_nonblocking(true)?;
    Self::new(mio::net::UdpSocket::from_std(socket))
  }

  pub fn local_addr(&self) -> Result<SocketAddr> {
    self.inner.local_addr()
  }

  pub async fn recv_from(&self, buf: &mut [u8]) -> Result<(usize, SocketAddr)> {
    RecvFrom { socket: self, buf }.await
  }

  pub async fn send_to(&self, buf: &[u8], target: SocketAddr) -> Result<usize> {
    SendTo { socket: self, buf, target }.await
  }
}

struct RecvFrom<'a> {
  socket: &'a UdpSocket,
  buf: &'a mut [u8],
}

impl<'a> Future for RecvFrom<'a> {
  type Output = Result<(usize, SocketAddr)>;

  fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = self.get_mut();
    let handle = ReactorHandle::new();
    let rid = this.socket.resource_id;

    let was_ready = readiness::is_readable(rid);
    let mut would_block = false;
    let mut completed: Poll<Result<(usize, SocketAddr)>> = Poll::Pending;
    if was_ready {
      match this.socket.inner.recv_from(this.buf) {
        Ok((n, addr)) => completed = Poll::Ready(Ok((n, addr))),
        Err(ref e) if e.kind() == ErrorKind::WouldBlock => {
          would_block = true;
          readiness::clear_readable(rid);
        }
        Err(e) => completed = Poll::Ready(Err(e)),
      }
    }

    let kernel = unsafe { &mut *this.socket.kernel.get() };
    match kernel.poll_step(IoMethod::Read, was_ready, would_block) {
      IoAction::Arm => {
        let waker = Waker::from_std(create_reactor_waker_for_current());
        handle.set_waker(rid, Interest::READABLE, waker);
        Poll::Pending
      }
      IoAction::Complete => completed,
    }
  }
}

struct SendTo<'a> {
  socket: &'a UdpSocket,
  buf: &'a [u8],
  target: SocketAddr,
}

impl<'a> Future for SendTo<'a> {
  type Output = Result<usize>;

  fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = self.get_mut();
    let handle = ReactorHandle::new();
    let rid = this.socket.resource_id;

    let was_ready = readiness::is_writable(rid);
    let mut would_block = false;
    let mut completed: Poll<Result<usize>> = Poll::Pending;
    if was_ready {
      match this.socket.inner.send_to(this.buf, this.target) {
        Ok(n) => completed = Poll::Ready(Ok(n)),
        Err(ref e) if e.kind() == ErrorKind::WouldBlock => {
          would_block = true;
          readiness::clear_writable(rid);
        }
        Err(e) => completed = Poll::Ready(Err(e)),
      }
    }

    let kernel = unsafe { &mut *this.socket.kernel.get() };
    match kernel.poll_step(IoMethod::Write, was_ready, would_block) {
      IoAction::Arm => {
        let waker = Waker::from_std(create_reactor_waker_for_current());
        handle.set_waker(rid, Interest::WRITABLE, waker);
        Poll::Pending
      }
      IoAction::Complete => completed,
    }
  }
}

impl Drop for UdpSocket {
  fn drop(&mut self) {
    let handle = ReactorHandle::new();
    let mut source = Source::new(&mut self.inner as &mut dyn mio::event::Source);
    let _ = handle.deregister_io_resource(self.resource_id, &mut source);
    self.kernel.get_mut().drop_step();
  }
}
