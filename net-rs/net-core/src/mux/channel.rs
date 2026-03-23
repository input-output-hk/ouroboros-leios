//! Per-protocol channel halves for the multiplexer.
//!
//! Each registered protocol gets a `ChannelSend` (for outgoing data) and a
//! `ChannelRecv` (for incoming data). These are split from the start so that
//! a future pipelined driver can use them from separate tasks.
//!
//! The ingress side shares an `Arc<AtomicUsize>` byte counter with the
//! demuxer so that buffer accounting stays accurate as the protocol consumes
//! data.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

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
        self.tx.send(payload).await.map_err(|_| MuxError::Shutdown)
    }
}

/// Shared byte counter for ingress buffer accounting. The demuxer increments
/// this when dispatching data; the ChannelRecv decrements when the protocol
/// consumes it.
#[derive(Debug, Clone)]
pub(crate) struct IngressCounter(pub Arc<AtomicUsize>);

impl IngressCounter {
    pub fn new() -> Self {
        Self(Arc::new(AtomicUsize::new(0)))
    }

    pub fn add(&self, bytes: usize) {
        self.0.fetch_add(bytes, Ordering::Relaxed);
    }

    pub fn sub(&self, bytes: usize) {
        self.0.fetch_sub(bytes, Ordering::Relaxed);
    }

    pub fn load(&self) -> usize {
        self.0.load(Ordering::Relaxed)
    }
}

/// Receiving half of a protocol channel. Yields reassembled payload chunks
/// from the demuxer.
#[derive(Debug)]
pub struct ChannelRecv {
    rx: mpsc::Receiver<Bytes>,
    ingress_counter: IngressCounter,
}

impl ChannelRecv {
    pub(crate) fn new(rx: mpsc::Receiver<Bytes>, ingress_counter: IngressCounter) -> Self {
        Self {
            rx,
            ingress_counter,
        }
    }

    /// Receive the next payload chunk. Returns `None` if the mux has shut down.
    /// Decrements the shared ingress byte counter when data is consumed.
    pub async fn recv(&mut self) -> Option<Bytes> {
        let data = self.rx.recv().await?;
        self.ingress_counter.sub(data.len());
        Some(data)
    }
}
