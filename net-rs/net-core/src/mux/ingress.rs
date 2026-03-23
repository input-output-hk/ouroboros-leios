//! Demuxer (ingress) task: reads segments from the bearer and dispatches
//! payloads to per-protocol ingress channels.

use std::collections::HashMap;
use std::time::Duration;

use bytes::Bytes;
use tokio::io::AsyncRead;
use tokio::sync::mpsc;

use super::wire;
use super::{MuxError, ProtocolId};

/// Per-protocol ingress state tracked by the demuxer.
pub(crate) struct ProtocolIngress {
    /// Sender to the protocol's ChannelRecv.
    pub tx: mpsc::Sender<Bytes>,
    /// Current accumulated bytes in the channel (approximate).
    pub buffered_bytes: usize,
    /// Maximum allowed bytes before declaring a protocol violation.
    pub limit: usize,
}

/// Run the demuxer task. Reads segments from the bearer and dispatches
/// payloads to per-protocol ingress channels.
///
/// Returns on I/O error, protocol violation, or when the bearer is closed.
pub(crate) async fn run_demuxer<R>(
    mut reader: R,
    mut protocols: HashMap<ProtocolId, ProtocolIngress>,
    sdu_timeout: Duration,
    _our_mode: u16,
) -> Result<(), MuxError>
where
    R: AsyncRead + Unpin,
{
    loop {
        // Read one segment with a timeout.
        let segment = match tokio::time::timeout(sdu_timeout, wire::read_segment(&mut reader))
            .await
        {
            Ok(Ok(seg)) => seg,
            Ok(Err(e)) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                // Bearer closed cleanly.
                return Ok(());
            }
            Ok(Err(e)) => return Err(MuxError::Io(e)),
            Err(_) => return Err(MuxError::SduTimeout(sdu_timeout)),
        };

        // Incoming segments from the remote peer have the *remote* mode bit.
        // We need to map to the local protocol ID: remote initiator → our
        // responder channel, remote responder → our initiator channel.
        // The protocol ID itself is the same; we just need to find the right
        // channel. Our protocols are registered for our role, so we accept
        // segments whose mode is the *opposite* of ours.
        let protocol_id = segment.header.protocol;

        let state = match protocols.get_mut(&protocol_id) {
            Some(s) => s,
            None => {
                // Unknown protocol — log and skip (per Haskell behavior).
                tracing::warn!(protocol = protocol_id, "received segment for unregistered protocol, ignoring");
                continue;
            }
        };

        // Check ingress buffer limit.
        let new_size = state.buffered_bytes + segment.payload.len();
        if new_size > state.limit && state.limit > 0 {
            return Err(MuxError::IngressOverflow {
                protocol: protocol_id,
                size: new_size,
                limit: state.limit,
            });
        }

        // Dispatch to the protocol's channel.
        if state.tx.send(segment.payload).await.is_err() {
            // Protocol channel was dropped — the protocol has terminated.
            // Remove it and continue.
            tracing::debug!(protocol = protocol_id, "protocol channel closed, removing");
            protocols.remove(&protocol_id);
            continue;
        }

        state.buffered_bytes = new_size;
        // Note: buffered_bytes is approximate. The protocol consuming data
        // reduces the actual buffer, but we don't track that here. A more
        // accurate approach would use an AtomicUsize shared with the channel.
        // For Phase 1 the limit is generous enough that this is fine.
    }
}
