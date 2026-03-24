//! Demuxer (ingress) task: reads segments from the bearer and dispatches
//! payloads to per-protocol ingress channels.

use std::collections::HashMap;
use std::time::Duration;

use bytes::Bytes;
use tokio::io::AsyncRead;
use tokio::sync::mpsc;

use super::channel::IngressCounter;
use super::wire;
use super::{ChannelKey, MuxError};

/// Per-protocol ingress state tracked by the demuxer.
pub(crate) struct ProtocolIngress {
    /// Sender to the protocol's ChannelRecv.
    pub tx: mpsc::Sender<Bytes>,
    /// Shared byte counter — incremented here, decremented by ChannelRecv.
    pub counter: IngressCounter,
    /// Maximum allowed bytes before declaring a protocol violation.
    pub limit: usize,
}

/// Run the demuxer task. Reads segments from the bearer and dispatches
/// payloads to per-protocol ingress channels.
///
/// Routes by `(protocol_id, mode)` composite key, supporting both
/// unidirectional and duplex connections.
///
/// Returns on I/O error, protocol violation, or when the bearer is closed.
pub(crate) async fn run_demuxer<R>(
    mut reader: R,
    mut protocols: HashMap<ChannelKey, ProtocolIngress>,
    sdu_timeout: Duration,
    max_sdu_payload: usize,
) -> Result<(), MuxError>
where
    R: AsyncRead + Unpin,
{
    loop {
        // Read one segment with a timeout.
        let segment = match tokio::time::timeout(
            sdu_timeout,
            wire::read_segment(&mut reader, max_sdu_payload),
        )
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

        let protocol_id = segment.header.protocol;
        let mode = segment.header.mode;
        let key = (protocol_id, mode);

        let state = match protocols.get_mut(&key) {
            Some(s) => s,
            None => {
                // Unknown protocol/direction — log and skip (per Haskell behavior).
                tracing::warn!(
                    protocol = protocol_id,
                    mode = mode,
                    "received segment for unregistered protocol/direction, ignoring"
                );
                continue;
            }
        };

        // Check ingress buffer limit using the shared counter.
        let current = state.counter.load();
        let new_size = current + segment.payload.len();
        if state.limit > 0 && new_size > state.limit {
            return Err(MuxError::IngressOverflow {
                protocol: protocol_id,
                size: new_size,
                limit: state.limit,
            });
        }

        // Increment the counter before dispatching.
        let payload_len = segment.payload.len();
        state.counter.add(payload_len);

        // Dispatch to the protocol's channel. Use try_send to avoid blocking
        // the demuxer (which would stall ALL protocols). If the channel is
        // full, the protocol is not consuming fast enough — treat as overload.
        match state.tx.try_send(segment.payload) {
            Ok(()) => {}
            Err(mpsc::error::TrySendError::Full(_)) => {
                // Undo the counter increment since we didn't actually deliver.
                state.counter.sub(payload_len);
                return Err(MuxError::IngressOverflow {
                    protocol: protocol_id,
                    size: state.counter.load() + payload_len,
                    limit: state.limit,
                });
            }
            Err(mpsc::error::TrySendError::Closed(_)) => {
                // Protocol channel was dropped — the protocol has terminated.
                state.counter.sub(payload_len);
                tracing::debug!(
                    protocol = protocol_id,
                    mode = mode,
                    "protocol channel closed, removing"
                );
                protocols.remove(&key);
                continue;
            }
        }
    }
}
