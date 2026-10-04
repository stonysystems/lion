pub mod tcp;
#[cfg(feature = "mio")]
pub mod addr;
#[cfg(feature = "mio")]
pub mod udp;

#[cfg(feature = "mio")]
pub use addr::ToSocketAddrs;
#[cfg(feature = "mio")]
pub use tcp::{TcpStream, TcpListener, TcpSocket, OwnedReadHalf, OwnedWriteHalf};
#[cfg(feature = "mio")]
pub use udp::UdpSocket;
