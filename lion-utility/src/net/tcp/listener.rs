// Trusted glue: Lion's tokio-shaped TcpListener (feature `mio`): a mio
// listener that owns the fd, plus lion-net's TcpListener, which registers it
// and drives every accept poll through the verified IoKernel (method Accept)
// and lion-reactor's AsyncFd. This whole module is the trust boundary
// (`verus::trusted` under Verus, plain Rust under cargo).
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::net::addr::ToSocketAddrs;
use crate::net::tcp::stream::TcpStream;
use std::future::Future;
use std::io::{ErrorKind, Result};
use std::net::SocketAddr;
use std::os::unix::io::AsRawFd;
use std::pin::Pin;
use std::sync::Mutex;
use std::task::{Context, Poll};

// `accept` takes `&self`, and lion-net's accept poll `&mut`: the core sits in
// a Mutex, which makes the listener Send and Sync with no `unsafe impl`. On
// Lion's thread-per-core runtime the lock is never contended; polled from
// another thread, the listener fails closed (AsyncFd's reactor check). Fields
// drop in declaration order: `core` deregisters the fd before `inner` closes
// it.
pub struct TcpListener {
  core: Mutex<lion_net::TcpListener>,
  inner: mio::net::TcpListener,
}

impl TcpListener {
  pub async fn bind<A: ToSocketAddrs>(addr: A) -> Result<TcpListener> {
    let addrs = addr.to_socket_addrs()?;
    let mut last_err = None;
    for addr in addrs {
      match mio::net::TcpListener::bind(addr) {
        Ok(listener) => return Self::new(listener),
        Err(e) => last_err = Some(e),
      }
    }
    Err(last_err.unwrap_or_else(|| {
      std::io::Error::new(ErrorKind::InvalidInput, "could not resolve to any addresses")
    }))
  }

  fn new(listener: mio::net::TcpListener) -> Result<TcpListener> {
    let core = lion_net::TcpListener::from_raw_fd(listener.as_raw_fd())?;
    Ok(TcpListener { core: Mutex::new(core), inner: listener })
  }

  pub fn from_std(listener: std::net::TcpListener) -> Result<TcpListener> {
    listener.set_nonblocking(true)?;
    Self::new(mio::net::TcpListener::from_std(listener))
  }

  pub fn local_addr(&self) -> Result<SocketAddr> { self.inner.local_addr() }

  pub async fn accept(&self) -> Result<(TcpStream, SocketAddr)> {
    Accept { listener: self }.await
  }
}

struct Accept<'a> {
  listener: &'a TcpListener,
}

impl<'a> Future for Accept<'a> {
  type Output = Result<(TcpStream, SocketAddr)>;

  fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let l = self.listener;
    let mut core = l.core.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    match core.poll_accept_with(cx, |_fd| l.inner.accept()) {
      Poll::Ready(Ok((stream, addr))) => Poll::Ready(TcpStream::from_mio(stream).map(|s| (s, addr))),
      Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
      Poll::Pending => Poll::Pending,
    }
  }
}

impl std::os::unix::io::AsRawFd for TcpListener {
  fn as_raw_fd(&self) -> std::os::unix::io::RawFd {
    self.inner.as_raw_fd()
  }
}

impl std::fmt::Debug for TcpListener {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("TcpListener").field("fd", &self.inner.as_raw_fd()).finish()
  }
}
