//! Muxer (egress) task: reads from per-protocol queues, segments into SDUs,
//! and writes to the bearer.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

use bytes::Bytes;
use tokio::io::AsyncWrite;
use tokio::sync::{mpsc, Notify};

use super::scheduler::Scheduler;
use super::wire;
use super::{ChannelKey, MuxError, ProtocolId};

/// Per-protocol egress state tracked by the muxer.
pub(crate) struct ProtocolEgress {
    /// Receiver for payloads queued by the protocol's ChannelSend.
    pub rx: mpsc::Receiver<Bytes>,
    /// Mode bit (initiator or responder) for wire encoding.
    pub mode: u16,
    /// Staging buffer: data consumed from rx but not yet written to bearer.
    /// The scheduler may not choose this protocol immediately, so we hold
    /// the data here until it's selected.
    pub pending: Option<Bytes>,
}

impl ProtocolEgress {
    /// Try to fill the pending buffer from the receiver (non-blocking).
    /// Returns true if pending has data (either already had some, or just received).
    fn fill_pending(&mut self) -> bool {
        if self.pending.is_some() {
            return true;
        }
        match self.rx.try_recv() {
            Ok(data) => {
                self.pending = Some(data);
                true
            }
            Err(_) => false,
        }
    }

    /// Take the pending data, leaving the buffer empty.
    fn take_pending(&mut self) -> Option<Bytes> {
        self.pending.take()
    }
}

/// Run the muxer task. Pulls data from protocol egress queues according to
/// the scheduler, fragments into SDUs, and writes segments to the bearer.
///
/// Returns when all protocol senders are dropped (all channels closed) or
/// on I/O error.
pub(crate) async fn run_muxer<W, S>(
    mut writer: W,
    mut protocols: HashMap<ChannelKey, ProtocolEgress>,
    mut scheduler: S,
    sdu_size: usize,
    clock: Instant,
    notify: Arc<Notify>,
) -> Result<(), MuxError>
where
    W: AsyncWrite + Unpin,
    S: Scheduler,
{
    loop {
        // Wait until at least one protocol has data.
        wait_for_any_data(&mut protocols, &notify).await;

        // Remove dead protocols (sender dropped, no pending data).
        protocols.retain(|_, state| !state.rx.is_closed() || state.pending.is_some());
        if protocols.is_empty() {
            return Ok(());
        }

        // Fill pending buffers from all receivers (non-blocking).
        for state in protocols.values_mut() {
            state.fill_pending();
        }

        // Collect protocol IDs (not composite keys) that have data ready.
        // The scheduler works at the protocol level, not per-direction.
        let ready: Vec<ProtocolId> = protocols
            .iter()
            .filter(|(_, state)| state.pending.is_some())
            .map(|((id, _), _)| *id)
            .collect();

        if ready.is_empty() {
            continue;
        }

        // Ask the scheduler which protocol to service.
        let chosen_id = match scheduler.next(&ready) {
            Some(id) => id,
            None => continue,
        };

        // Find the first composite key for this protocol ID that has data.
        let chosen_key = protocols
            .iter()
            .find(|((id, _), state)| *id == chosen_id && state.pending.is_some())
            .map(|(key, _)| *key);

        if let Some(key) = chosen_key {
            if let Some(state) = protocols.get_mut(&key) {
                if let Some(data) = state.take_pending() {
                    let mode = state.mode;
                    let protocol_id = key.0;
                    let timestamp = clock.elapsed().as_micros() as u32;
                    let segments =
                        wire::segment_payload(protocol_id, mode, timestamp, &data, sdu_size);

                    for segment in &segments {
                        wire::write_segment(&mut writer, segment).await?;
                    }
                }
            }
        }
    }
}

/// Block until at least one protocol has data available, either in its
/// pending buffer or in its receiver channel.
///
/// Uses a shared `Notify` signalled by `ChannelSend::send()` to avoid
/// busy-waiting. A periodic timeout (100ms) handles closed-channel cleanup.
async fn wait_for_any_data(protocols: &mut HashMap<ChannelKey, ProtocolEgress>, notify: &Notify) {
    // Check pending buffers first (fast path).
    if protocols.values().any(|s| s.pending.is_some()) {
        return;
    }

    loop {
        // Register listener *before* checking receivers to avoid a race
        // where data arrives between the check and the wait.
        let notified = notify.notified();

        for state in protocols.values_mut() {
            if state.fill_pending() {
                return;
            }
        }

        // Remove disconnected protocols with no pending data.
        protocols.retain(|_, state| !state.rx.is_closed() || state.pending.is_some());
        if protocols.is_empty() {
            return;
        }

        // Wait for a ChannelSend to signal, or periodic closed-channel check.
        tokio::select! {
            _ = notified => {}
            _ = tokio::time::sleep(Duration::from_millis(100)) => {}
        }
    }
}
