pub mod mem;
pub mod tcp;

use tokio::io::{AsyncRead, AsyncWrite};

/// A bearer is a bidirectional byte stream that can be split into independent
/// read and write halves. Each transport (TCP, Unix, in-memory) implements this
/// trait to plug into the multiplexer.
pub trait Bearer: Send + 'static {
    type Read: AsyncRead + Send + Unpin + 'static;
    type Write: AsyncWrite + Send + Unpin + 'static;

    fn split(self) -> (Self::Read, Self::Write);
}
