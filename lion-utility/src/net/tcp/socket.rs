// Trusted glue: TcpSocket is a socket2-based builder (SO_REUSEADDR/REUSEPORT for
// the multi-thread / Tokio-Partition style benchmarks). It performs no reactor
// registration itself — that happens when it converts to a TcpListener (listen)
// or TcpStream (connect), both of which carry a verified IoKernel. Plain Rust /
// `verus::trusted`.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::net::tcp::listener::TcpListener;
use crate::net::tcp::stream::{Connect, TcpStream};
use socket2::{Domain, Protocol, Socket, Type};
use std::io::Result;
use std::net::SocketAddr;
use std::os::unix::io::{AsFd, AsRawFd, BorrowedFd, FromRawFd, IntoRawFd, RawFd};

pub struct TcpSocket {
  inner: Socket,
}

impl TcpSocket {
  pub fn new_v4() -> Result<TcpSocket> {
    let inner = Socket::new(Domain::IPV4, Type::STREAM, Some(Protocol::TCP))?;
    inner.set_nonblocking(true)?;
    Ok(TcpSocket { inner })
  }

  pub fn new_v6() -> Result<TcpSocket> {
    let inner = Socket::new(Domain::IPV6, Type::STREAM, Some(Protocol::TCP))?;
    inner.set_nonblocking(true)?;
    Ok(TcpSocket { inner })
  }

  pub fn set_reuseaddr(&self, reuseaddr: bool) -> Result<()> {
    self.inner.set_reuse_address(reuseaddr)
  }

  #[cfg(not(target_os = "illumos"))]
  pub fn set_reuseport(&self, reuseport: bool) -> Result<()> {
    self.inner.set_reuse_port(reuseport)
  }

  pub fn set_nodelay(&self, nodelay: bool) -> Result<()> {
    self.inner.set_nodelay(nodelay)
  }

  pub fn bind(&self, addr: SocketAddr) -> Result<()> {
    self.inner.bind(&addr.into())
  }

  pub fn listen(self, backlog: u32) -> Result<TcpListener> {
    self.inner.listen(backlog as i32)?;
    let std_listener: std::net::TcpListener = self.inner.into();
    TcpListener::from_std(std_listener)
  }

  pub fn local_addr(&self) -> Result<SocketAddr> {
    self.inner.local_addr().and_then(|addr| {
      addr.as_socket().ok_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::Other, "not a socket address")
      })
    })
  }

  pub async fn connect(self, addr: SocketAddr) -> Result<TcpStream> {
    match self.inner.connect(&addr.into()) {
      Ok(()) => {}
      Err(ref e) if e.raw_os_error() == Some(36) => {}   // EINPROGRESS (macOS)
      Err(ref e) if e.raw_os_error() == Some(115) => {}  // EINPROGRESS (Linux)
      Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
      Err(e) => return Err(e),
    }
    let std_stream: std::net::TcpStream = self.inner.into();
    let mio_stream = mio::net::TcpStream::from_std(std_stream);
    Connect::from_mio(mio_stream)?.await
  }

  pub fn from_std_stream(stream: std::net::TcpStream) -> TcpSocket {
    let raw_fd = stream.into_raw_fd();
    let socket = unsafe { Socket::from_raw_fd(raw_fd) };
    TcpSocket { inner: socket }
  }
}

impl AsRawFd for TcpSocket {
  fn as_raw_fd(&self) -> RawFd {
    self.inner.as_raw_fd()
  }
}

impl AsFd for TcpSocket {
  fn as_fd(&self) -> BorrowedFd<'_> {
    unsafe { BorrowedFd::borrow_raw(self.inner.as_raw_fd()) }
  }
}
