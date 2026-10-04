// The verified io kernel lives in lion-net (with no OS dependency); its modules
// are re-exported here under their old paths.
pub use lion_net::net::tcp::{kernel, method, proof};

// Lion's tokio-shaped sockets, over mio and lion-net (feature `mio`).
#[cfg(feature = "mio")]
pub mod stream;
#[cfg(feature = "mio")]
pub mod listener;
#[cfg(feature = "mio")]
pub mod socket;

#[cfg(feature = "mio")]
pub use stream::{TcpStream, OwnedReadHalf, OwnedWriteHalf};
#[cfg(feature = "mio")]
pub use listener::TcpListener;
#[cfg(feature = "mio")]
pub use socket::TcpSocket;
