use tokio::io::{DuplexStream, duplex};

use super::Bearer;

/// In-memory bearer for testing. Uses a tokio duplex stream internally.
pub struct MemBearer {
    stream: DuplexStream,
}

/// Default buffer size for the in-memory duplex stream (128KB, matching the
/// Haskell implementation's read buffer size).
const DEFAULT_BUFFER_SIZE: usize = 128 * 1024;

impl MemBearer {
    /// Create a connected pair of in-memory bearers. Data written to one side
    /// can be read from the other, and vice versa.
    pub fn pair() -> (Self, Self) {
        Self::pair_with_buffer(DEFAULT_BUFFER_SIZE)
    }

    /// Create a connected pair with a specific buffer size.
    pub fn pair_with_buffer(buffer_size: usize) -> (Self, Self) {
        let (a, b) = duplex(buffer_size);
        (Self { stream: a }, Self { stream: b })
    }
}

impl Bearer for MemBearer {
    type Read = tokio::io::ReadHalf<DuplexStream>;
    type Write = tokio::io::WriteHalf<DuplexStream>;

    fn split(self) -> (Self::Read, Self::Write) {
        tokio::io::split(self.stream)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    #[tokio::test]
    async fn pair_can_exchange_data() {
        let (a, b) = MemBearer::pair();
        let (mut a_read, mut a_write) = a.split();
        let (mut b_read, mut b_write) = b.split();

        a_write.write_all(b"hello").await.unwrap();
        let mut buf = [0u8; 5];
        b_read.read_exact(&mut buf).await.unwrap();
        assert_eq!(&buf, b"hello");

        b_write.write_all(b"world").await.unwrap();
        a_read.read_exact(&mut buf).await.unwrap();
        assert_eq!(&buf, b"world");
    }
}
