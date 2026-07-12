#![cfg_attr(verus_keep_ghost, verus::trusted)]
// Address resolution trait (plain Rust; trusted under Verus). Ported verbatim
// from the unverified utilities.
use std::io::Result;
use std::net::SocketAddr;

pub trait ToSocketAddrs {
  type Iter: Iterator<Item = SocketAddr>;
  fn to_socket_addrs(&self) -> Result<Self::Iter>;
}

impl ToSocketAddrs for SocketAddr {
  type Iter = std::option::IntoIter<SocketAddr>;

  fn to_socket_addrs(&self) -> Result<Self::Iter> {
    Ok(Some(*self).into_iter())
  }
}

impl ToSocketAddrs for &SocketAddr {
  type Iter = std::option::IntoIter<SocketAddr>;

  fn to_socket_addrs(&self) -> Result<Self::Iter> {
    Ok(Some(**self).into_iter())
  }
}

impl ToSocketAddrs for (std::net::IpAddr, u16) {
  type Iter = std::option::IntoIter<SocketAddr>;

  fn to_socket_addrs(&self) -> Result<Self::Iter> {
    Ok(Some(SocketAddr::from(*self)).into_iter())
  }
}

impl ToSocketAddrs for (&str, u16) {
  type Iter = std::vec::IntoIter<SocketAddr>;

  fn to_socket_addrs(&self) -> Result<Self::Iter> {
    use std::net::{Ipv4Addr, Ipv6Addr, SocketAddrV4, SocketAddrV6};

    let (host, port) = *self;

    if let Ok(addr) = host.parse::<Ipv4Addr>() {
      return Ok(vec![SocketAddr::V4(SocketAddrV4::new(addr, port))].into_iter());
    }

    if let Ok(addr) = host.parse::<Ipv6Addr>() {
      return Ok(vec![SocketAddr::V6(SocketAddrV6::new(addr, port, 0, 0))].into_iter());
    }

    use std::net::ToSocketAddrs as StdToSocketAddrs;
    StdToSocketAddrs::to_socket_addrs(self).map(|iter| iter.collect::<Vec<_>>().into_iter())
  }
}

impl ToSocketAddrs for str {
  type Iter = std::vec::IntoIter<SocketAddr>;

  fn to_socket_addrs(&self) -> Result<Self::Iter> {
    if let Ok(addr) = self.parse::<SocketAddr>() {
      return Ok(vec![addr].into_iter());
    }

    use std::net::ToSocketAddrs as StdToSocketAddrs;
    StdToSocketAddrs::to_socket_addrs(self).map(|iter| iter.collect::<Vec<_>>().into_iter())
  }
}

impl ToSocketAddrs for &str {
  type Iter = std::vec::IntoIter<SocketAddr>;

  fn to_socket_addrs(&self) -> Result<Self::Iter> {
    (*self as &str).to_socket_addrs()
  }
}

impl ToSocketAddrs for String {
  type Iter = std::vec::IntoIter<SocketAddr>;

  fn to_socket_addrs(&self) -> Result<Self::Iter> {
    self.as_str().to_socket_addrs()
  }
}

impl ToSocketAddrs for &String {
  type Iter = std::vec::IntoIter<SocketAddr>;

  fn to_socket_addrs(&self) -> Result<Self::Iter> {
    self.as_str().to_socket_addrs()
  }
}
