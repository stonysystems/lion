// The verified io kernel lives in lion-net (with no OS dependency); its modules
// are re-exported here under their old paths.
pub use lion_net::net::tcp::{kernel, method, proof};

pub mod stream;
pub mod listener;
pub mod socket;

pub use stream::{TcpStream, OwnedReadHalf, OwnedWriteHalf};
pub use listener::TcpListener;
pub use socket::TcpSocket;
