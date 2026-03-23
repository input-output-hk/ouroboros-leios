//! Demuxer (ingress) task: reads segments from the bearer and dispatches
//! payloads to per-protocol ingress channels.

use std::collections::HashMap;
use std::time::Duration;

use bytes::Bytes;
use tokio::io::AsyncRead;
use tokio::sync::mpsc;

use super::channel::IngressCounter;
use super::wire;
use super::{MuxError, ProtocolId, MODE_INITIATOR, MODE_RESPONDER};

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
/// Returns on I/O error, protocol violation, or when the bearer is closed.
pub(crate) async fn run_demuxer<R>(
    mut reader: R,
    mut protocols: HashMap<ProtocolId, ProtocolIngress>,
    sdu_timeout: Duration,
    max_sdu_payload: usize,
    our_mode: u16,
) -> Result<(), MuxError>
where
    R: AsyncRead + Unpin,
{
    // The expected mode bit on incoming segments: opposite of ours.
    let expected_remote_mode = if our_mode == MODE_INITIATOR {
        MODE_RESPONDER
    } else {
        MODE_INITIATOR
    };

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

        // Validate the mode bit: incoming segments should have the remote mode.
        if segment.header.mode != expected_remote_mode {
            tracing::warn!(
                protocol = segment.header.protocol,
                expected_mode = expected_remote_mode,
                actual_mode = segment.header.mode,
                "received segment with unexpected mode bit, ignoring"
            );
            continue;
        }

        let protocol_id = segment.header.protocol;

        let state = match protocols.get_mut(&protocol_id) {
            Some(s) => s,
            None => {
                // Unknown protocol — log and skip (per Haskell behavior).
                tracing::warn!(
                    protocol = protocol_id,
                    "received segment for unregistered protocol, ignoring"
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
                tracing::debug!(protocol = protocol_id, "protocol channel closed, removing");
                protocols.remove(&protocol_id);
                continue;
            }
        }
    }
}
