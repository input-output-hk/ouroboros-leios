//! Leios consensus layer.
//!
//! Currently owns only the Leios event routing — offer events issue fetches,
//! received events are logged — that previously lived in the monolithic
//! `consensus.rs`. Future work will add stage/election state, EB candidate
//! ranking, vote aggregation, certificate formation, and certified-EB
//! extraction for RB header population.

use std::collections::HashMap;
use std::time::{Duration, Instant};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::Point;
use tokio::sync::mpsc;
use tracing::info;

/// How long an in-flight Leios fetch entry remains active before being
/// considered stale. Matches the Praos in-flight TTL.
const IN_FLIGHT_TTL: Duration = Duration::from_secs(15);

/// Leios consensus state. Today it tracks only which EBs / TX bundles have
/// a fetch in flight; real election/vote/certificate state lands in later
/// commits.
pub struct LeiosConsensus {
    node_id: String,
    commands: mpsc::Sender<NetworkCommand>,
    /// Leios points currently being fetched. Separate from the Praos
    /// in-flight set because Leios data lives outside the chain.
    in_flight: HashMap<Point, Instant>,
}

impl LeiosConsensus {
    pub fn new(node_id: String, commands: mpsc::Sender<NetworkCommand>) -> Self {
        Self {
            node_id,
            commands,
            in_flight: HashMap::new(),
        }
    }

    /// Handle one Leios-shaped network event. Returns true if the event was
    /// consumed by this layer (caller should not log it separately).
    pub async fn handle_event(&mut self, event: &NetworkEvent) -> bool {
        self.evict_stale_in_flight();
        match event {
            NetworkEvent::LeiosBlockOffered { point } => {
                if !self.in_flight.contains_key(point) {
                    self.mark_in_flight(point.clone());
                    info!(node_id = %self.node_id, %point, "fetching leios block");
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchLeiosBlock {
                            point: point.clone(),
                        })
                        .await;
                }
                true
            }
            NetworkEvent::LeiosBlockTxsOffered { point } => {
                // Distinct synthetic key so the TX-bundle fetch doesn't
                // collide with the EB-body fetch for the same point.
                let key = Point::Specific {
                    slot: match point {
                        Point::Specific { slot, .. } => *slot,
                        _ => 0,
                    },
                    hash: [0xFE; 32],
                };
                if !self.in_flight.contains_key(&key) {
                    self.mark_in_flight(key);
                    info!(node_id = %self.node_id, %point, "fetching leios block txs");
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchLeiosBlockTxs {
                            point: point.clone(),
                            bitmap: std::collections::BTreeMap::new(),
                        })
                        .await;
                }
                true
            }
            NetworkEvent::LeiosVotesOffered { votes } => {
                if !votes.is_empty() {
                    info!(
                        node_id = %self.node_id,
                        count = votes.len(),
                        "fetching leios votes"
                    );
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchLeiosVotes {
                            votes: votes.clone(),
                        })
                        .await;
                }
                true
            }
            NetworkEvent::LeiosBlockReceived { point, .. } => {
                self.in_flight.remove(point);
                info!(node_id = %self.node_id, %point, "leios block received");
                true
            }
            NetworkEvent::LeiosVotesReceived { votes } => {
                info!(
                    node_id = %self.node_id,
                    count = votes.len(),
                    "leios votes received"
                );
                true
            }
            NetworkEvent::LeiosBlockTxsReceived {
                point,
                transactions,
            } => {
                info!(
                    node_id = %self.node_id,
                    %point,
                    count = transactions.len(),
                    "leios block txs received"
                );
                true
            }
            _ => false,
        }
    }

    fn mark_in_flight(&mut self, point: Point) {
        self.in_flight.insert(point, Instant::now());
    }

    fn evict_stale_in_flight(&mut self) {
        let now = Instant::now();
        self.in_flight
            .retain(|_, started| now.duration_since(*started) < IN_FLIGHT_TTL);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn point(slot: u64) -> Point {
        Point::Specific {
            slot,
            hash: [slot as u8; 32],
        }
    }

    #[tokio::test]
    async fn block_offered_issues_fetch() {
        let (tx, mut rx) = mpsc::channel(8);
        let mut leios = LeiosConsensus::new("test".into(), tx);

        let p = point(100);
        assert!(
            leios
                .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
                .await
        );

        match rx.try_recv() {
            Ok(NetworkCommand::FetchLeiosBlock { point: got }) => assert_eq!(got, p),
            other => panic!("expected FetchLeiosBlock, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn duplicate_block_offer_dedup() {
        let (tx, mut rx) = mpsc::channel(8);
        let mut leios = LeiosConsensus::new("test".into(), tx);

        let p = point(100);
        leios
            .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
            .await;

        // First offer emits a fetch; second is deduped.
        assert!(matches!(
            rx.try_recv(),
            Ok(NetworkCommand::FetchLeiosBlock { .. })
        ));
        assert!(rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn received_clears_in_flight() {
        let (tx, _rx) = mpsc::channel(8);
        let mut leios = LeiosConsensus::new("test".into(), tx);

        let p = point(200);
        leios
            .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: p.clone(),
                block: vec![],
            })
            .await;
        assert!(!leios.in_flight.contains_key(&p));
    }

    #[tokio::test]
    async fn non_leios_event_not_consumed() {
        let (tx, _rx) = mpsc::channel(8);
        let mut leios = LeiosConsensus::new("test".into(), tx);

        let consumed = leios
            .handle_event(&NetworkEvent::PeerDisconnected {
                peer_id: net_core::peer::PeerId(0),
                reason: String::new(),
            })
            .await;
        assert!(!consumed);
    }
}
