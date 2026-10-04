// Trusted glue: Lion's UdpSocket (feature `mio`): a mio socket that owns the
// fd, plus lion-net's stream core, which registers it and drives recv (Read)
// and send (Write) polls through the verified IoKernel and lion-reactor's
// AsyncFd. The core is fd-generic and clears readiness only on WouldBlock
// (never on a short transfer), which is what a datagram socket needs: one edge
// may stand for several queued datagrams. recv_from/send_to take &self
// (matching tokio), so the core sits in a Mutex: Send and Sync with no
// `unsafe impl`, never contended on Lion's thread-per-core runtime.
// verus::trusted under Verus, plain Rust under cargo.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::net::addr::ToSocketAddrs;
use std::future::Future;
use std::io::{ErrorKind, Result};
use std::net::SocketAddr;
use std::os::unix::io::AsRawFd;
use std::pin::Pin;
use std::sync::Mutex;
use std::task::{Context, Poll};

// Fields drop in declaration order: `core` deregisters the fd before `inner`
// closes it.
pub struct UdpSocket {
  core: Mutex<lion_net::TcpStream>,
  inner: mio::net::UdpSocket,
}

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

  fn new(socket: mio::net::UdpSocket) -> Result<UdpSocket> {
    let core = lion_net::TcpStream::from_raw_fd(socket.as_raw_fd())?;
    Ok(UdpSocket { core: Mutex::new(core), inner: socket })
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

  fn core(&self) -> std::sync::MutexGuard<'_, lion_net::TcpStream> {
    self.core.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
  }
}

struct RecvFrom<'a> {
  socket: &'a UdpSocket,
  buf: &'a mut [u8],
}

impl<'a> Future for RecvFrom<'a> {
  type Output = Result<(usize, SocketAddr)>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = self.get_mut();
    let socket = this.socket;
    let buf = &mut *this.buf;
    let mut core = socket.core();
    core.poll_read_with(cx, |_fd| socket.inner.recv_from(buf))
  }
}

struct SendTo<'a> {
  socket: &'a UdpSocket,
  buf: &'a [u8],
  target: SocketAddr,
}

impl<'a> Future for SendTo<'a> {
  type Output = Result<usize>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = self.get_mut();
    let socket = this.socket;
    let (buf, target) = (this.buf, this.target);
    let mut core = socket.core();
    core.poll_write_with(cx, |_fd| socket.inner.send_to(buf, target))
  }
}
