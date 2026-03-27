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
        Some(PeerCommand::SubmitTransaction { tx }) => {
            let _ = senders.tx_submit.send(tx).await;
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
        Some(PeerCommand::FetchLeiosVotes { votes }) => {
            if let Some(ref lf) = senders.leios_fetch {
                let _ = lf.send(LeiosFetchCommand::Votes { votes }).await;
            }
        }
        Some(PeerCommand::Disconnect) | None => return false,
    }
    true
}
