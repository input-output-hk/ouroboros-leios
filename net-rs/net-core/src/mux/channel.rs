//! Per-protocol channel halves for the multiplexer.
//!
//! Each registered protocol gets a `ChannelSend` (for outgoing data) and a
//! `ChannelRecv` (for incoming data). These are split from the start so that
//! a future pipelined driver can use them from separate tasks.

use bytes::Bytes;
use tokio::sync::mpsc;

use super::MuxError;

/// Sending half of a protocol channel. Queues payload chunks for the muxer
/// to segment and write to the bearer.
#[derive(Debug)]
pub struct ChannelSend {
    tx: mpsc::Sender<Bytes>,
}

impl ChannelSend {
    pub(crate) fn new(tx: mpsc::Sender<Bytes>) -> Self {
        Self { tx }
    }

    /// Queue a payload chunk for transmission. Blocks if the egress queue is full.
    pub async fn send(&self, payload: Bytes) -> Result<(), MuxError> {
        self.tx
            .send(payload)
            .await
            .map_err(|_| MuxError::Shutdown)
    }
}

/// Receiving half of a protocol channel. Yields reassembled payload chunks
/// from the demuxer.
#[derive(Debug)]
pub struct ChannelRecv {
    rx: mpsc::Receiver<Bytes>,
}

impl ChannelRecv {
    pub(crate) fn new(rx: mpsc::Receiver<Bytes>) -> Self {
        Self { rx }
    }

    /// Receive the next payload chunk. Returns `None` if the mux has shut down.
    pub async fn recv(&mut self) -> Option<Bytes> {
        self.rx.recv().await
    }
}

