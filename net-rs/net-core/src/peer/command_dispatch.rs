//! Shared command dispatch for client-side protocol tasks.
//!
//! Both `peer_task` (initiator-only) and `duplex_task` (initiator+responder)
//! dispatch `PeerCommand`s to the same set of client protocol sub-tasks.
//! This module provides a single implementation to avoid duplication.

use tokio::sync::mpsc;

use crate::protocols::txsubmission::PendingTx;
use crate::types::Point;

use super::peer_task::LeiosFetchCommand;
use super::types::PeerCommand;

/// Channel senders for dispatching commands to client-side protocol tasks.
pub(crate) struct ClientProtocolSenders {
    pub fetch: mpsc::Sender<(Point, Point)>,
    pub peer_share: mpsc::Sender<u8>,
    pub tx_submit: mpsc::Sender<PendingTx>,
    pub leios_fetch: Option<mpsc::Sender<LeiosFetchCommand>>,
    /// Signal to ChainSync sub-task to re-run find_intersection.
    pub chainsync_reintersect: mpsc::Sender<()>,
}

/// Dispatch a single PeerCommand to the appropriate protocol task.
/// Returns `false` when the peer should disconnect (Disconnect or channel closed).
pub(crate) async fn dispatch_command(
    cmd: Option<PeerCommand>,
    senders: &ClientProtocolSenders,
) -> bool {
    match cmd {
        Some(PeerCommand::FetchBlocks { from, to }) => {
            let _ = senders.fetch.send((from, to)).await;
        }
        Some(PeerCommand::RequestPeers { amount }) => {
            let _ = senders.peer_share.send(amount).await;
        }
        Some(PeerCommand::ProvideTxs { txs }) => {
            // `try_send` + drop on overflow: tx submission is
            // best-effort gossip — another peer will re-broadcast.
            // Blocking the dispatch loop here would back-pressure the
            // per-peer command channel and trip the coordinator's
            // "command channel full" disconnect.
            use tokio::sync::mpsc::error::TrySendError;
            let mut dropped = 0usize;
            for tx in txs {
                match senders.tx_submit.try_send(tx) {
                    Ok(()) => {}
                    Err(TrySendError::Full(_)) => dropped += 1,
                    Err(TrySendError::Closed(_)) => return false,
                }
            }
            if dropped > 0 {
                tracing::warn!(dropped, "tx_submit channel saturated; dropping txs");
            }
        }
        Some(PeerCommand::FetchLeiosBlock { point }) => {
            if let Some(ref lf) = senders.leios_fetch {
                let _ = lf.send(LeiosFetchCommand::Block { point }).await;
            }
        }
        Some(PeerCommand::FetchLeiosBlockTxs { point, bitmap }) => {
            if let Some(ref lf) = senders.leios_fetch {
                let _ = lf.send(LeiosFetchCommand::BlockTxs { point, bitmap }).await;
            }
        }
        Some(PeerCommand::ReIntersect) => {
            let _ = senders.chainsync_reintersect.send(()).await;
        }
        Some(PeerCommand::Disconnect) | None => return false,
    }
    true
}
