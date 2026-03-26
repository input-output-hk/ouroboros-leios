use std::io;
use std::net::SocketAddr;
use std::time::Duration;

use socket2::{SockRef, TcpKeepalive};
use tokio::io::{ReadHalf, WriteHalf};
use tokio::net::{TcpListener, TcpStream};

use super::Bearer;

/// TCP bearer with Cardano-appropriate socket options (TCP_NODELAY, keepalive).
pub struct TcpBearer {
    stream: TcpStream,
}

impl TcpBearer {
    /// Connect to a remote address.
    pub async fn connect(addr: SocketAddr) -> io::Result<Self> {
        let stream = TcpStream::connect(addr).await?;
        configure_stream(&stream)?;
        Ok(Self { stream })
    }

    /// Connect to a remote address with a timeout.
    pub async fn connect_timeout(addr: SocketAddr, timeout: Duration) -> io::Result<Self> {
        let stream = tokio::time::timeout(timeout, TcpStream::connect(addr))
            .await
            .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "connection timed out"))??;
        configure_stream(&stream)?;
        Ok(Self { stream })
    }

    /// Accept a connection from a listener.
    pub async fn accept(listener: &TcpListener) -> io::Result<(Self, SocketAddr)> {
        let (stream, addr) = listener.accept().await?;
        configure_stream(&stream)?;
        Ok((Self { stream }, addr))
    }
}

impl Bearer for TcpBearer {
    type Read = ReadHalf<TcpStream>;
    type Write = WriteHalf<TcpStream>;

    fn split(self) -> (Self::Read, Self::Write) {
        tokio::io::split(self.stream)
    }
}

fn configure_stream(stream: &TcpStream) -> io::Result<()> {
    stream.set_nodelay(true)?;
    let sock = SockRef::from(stream);
    let keepalive = TcpKeepalive::new()
        .with_time(Duration::from_secs(60))
        .with_interval(Duration::from_secs(15));
    sock.set_tcp_keepalive(&keepalive)?;
    Ok(())
}
