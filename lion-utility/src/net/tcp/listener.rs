// Trusted glue: a real TcpListener wrapping the verified IoKernel. Like the
// stream glue this whole module is the trust boundary (`verus::trusted` under
// Verus, plain Rust under cargo). The listener's own io resource is tracked by a
// kernel; because accept() takes &self, the kernel sits behind an UnsafeCell with
// an unsafe Send/Sync justified by lion's thread-per-core (no cross-thread
// sharing of a listener) model.
#![cfg_attr(verus_keep_ghost, verus::trusted)]

use crate::net::addr::ToSocketAddrs;
use crate::net::tcp::kernel::{IoAction, IoKernel};
use crate::net::tcp::method::IoMethod;
use crate::net::tcp::stream::TcpStream;
use lion_executor::create_reactor_waker_for_current;
use lion_reactor::readiness;
use lion_reactor::{Interest, IoResult, ReactorHandle, ResourceId, Source, Waker};
use std::cell::UnsafeCell;
use std::future::Future;
use std::io::{ErrorKind, Result};
use std::os::unix::io::AsRawFd;
use std::net::SocketAddr;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct TcpListener {
  inner: mio::net::TcpListener,
  resource_id: ResourceId,
  kernel: UnsafeCell<IoKernel>,
}

unsafe impl Send for TcpListener {}
unsafe impl Sync for TcpListener {}

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

  fn new(mut listener: mio::net::TcpListener) -> Result<TcpListener> {
    let handle = ReactorHandle::new();
    let mut source = Source::new(&mut listener as &mut dyn mio::event::Source);
    let resource_id = match handle.register_io_resource(&mut source, Interest::READABLE) {
      IoResult::Ok(id) => id,
      IoResult::Err(e) => return Err(std::io::Error::new(ErrorKind::Other, format!("{:?}", e))),
    };
    readiness::init_readiness(resource_id);
    let kernel = IoKernel::new(resource_id.0);
    Ok(TcpListener { inner: listener, resource_id, kernel: UnsafeCell::new(kernel) })
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

  fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
    let l = self.listener;
    let handle = ReactorHandle::new();
    let kernel = unsafe { &mut *l.kernel.get() };

    let was_ready = readiness::is_readable(l.resource_id);
    let mut would_block = false;
    let mut completed: Option<Poll<Self::Output>> = None;
    if was_ready {
      match l.inner.accept() {
        Ok((stream, addr)) => {
          completed = Some(match TcpStream::from_mio(stream) {
            Ok(s) => Poll::Ready(Ok((s, addr))),
            Err(e) => Poll::Ready(Err(e)),
          });
        }
        Err(ref e) if e.kind() == ErrorKind::WouldBlock => {
          would_block = true;
          readiness::clear_readable(l.resource_id);
        }
        Err(e) => { completed = Some(Poll::Ready(Err(e))); }
      }
    }

    match kernel.poll_step(IoMethod::Accept, was_ready, would_block) {
      IoAction::Arm => {
        let waker = Waker::from_std(create_reactor_waker_for_current());
        handle.set_waker(l.resource_id, Interest::READABLE, waker);
        Poll::Pending
      }
      IoAction::Complete => completed.expect("Complete decision implies an accept result"),
    }
  }
}

impl Drop for TcpListener {
  fn drop(&mut self) {
    let handle = ReactorHandle::new();
    let mut source = Source::new(&mut self.inner as &mut dyn mio::event::Source);
    let _ = handle.deregister_io_resource(self.resource_id, &mut source);
    self.kernel.get_mut().drop_step();
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
