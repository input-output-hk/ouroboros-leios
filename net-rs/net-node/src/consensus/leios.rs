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

use crate::validation::{LedgerCommand, Validator};

/// How long an in-flight Leios fetch entry remains active before being
/// considered stale. Matches the Praos in-flight TTL.
const IN_FLIGHT_TTL: Duration = Duration::from_secs(15);

/// Leios consensus state. Today it tracks only which EBs / TX bundles have
/// a fetch in flight; real election/vote/certificate state lands in later
/// commits.
pub struct LeiosConsensus {
    node_id: String,
    commands: mpsc::Sender<NetworkCommand>,
    validator: Validator,
    /// Leios points currently being fetched. Separate from the Praos
    /// in-flight set because Leios data lives outside the chain.
    in_flight: HashMap<Point, Instant>,
}

impl LeiosConsensus {
    pub fn new(
        node_id: String,
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
    ) -> Self {
        Self {
            node_id,
            commands,
            validator,
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
                self.validator
                    .submit(LedgerCommand::ValidateEb {
                        point: point.clone(),
                    })
                    .await;
                true
            }
            NetworkEvent::LeiosVotesReceived { vote_ids, .. } => {
                self.validator
                    .submit(LedgerCommand::ValidateVotes {
                        vote_ids: vote_ids.clone(),
                    })
                    .await;
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

    /// Called when EB validation completes.
    pub fn on_validated_eb(&mut self, point: Point) {
        info!(node_id = %self.node_id, %point, "eb validated");
    }

    /// Called when vote validation completes.
    pub fn on_validated_votes(&mut self, vote_ids: &[(u64, Vec<u8>)]) {
        info!(node_id = %self.node_id, count = vote_ids.len(), "votes validated");
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
    use crate::config::DynamicConfig;
    use tokio::sync::watch;

    fn point(slot: u64) -> Point {
        Point::Specific {
            slot,
            hash: [slot as u8; 32],
        }
    }

    fn test_dyn_config() -> watch::Receiver<DynamicConfig> {
        let config = DynamicConfig {
            rb_generation_probability: 0.0,
            eb_generation_probability: 0.0,
            vote_generation_probability: 0.0,
            rb_head_validation_ms: 0.0,
            rb_body_validation_ms_constant: 0.0,
            rb_body_validation_ms_per_byte: 0.0,
            eb_validation_ms: 0.0,
            vote_validation_ms: 0.0,
            tx_rate: 0.0,
        };
        watch::channel(config).1
    }

    fn test_validator() -> (Validator, mpsc::Receiver<crate::validation::LedgerOutcome>) {
        Validator::new(test_dyn_config())
    }

    #[tokio::test]
    async fn block_offered_issues_fetch() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _outcome_rx) = test_validator();
        let mut leios = LeiosConsensus::new("test".into(), tx, validator);

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
        let (validator, _outcome_rx) = test_validator();
        let mut leios = LeiosConsensus::new("test".into(), tx, validator);

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
        let (validator, _outcome_rx) = test_validator();
        let mut leios = LeiosConsensus::new("test".into(), tx, validator);

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
        let (validator, _outcome_rx) = test_validator();
        let mut leios = LeiosConsensus::new("test".into(), tx, validator);

        let consumed = leios
            .handle_event(&NetworkEvent::PeerDisconnected {
                peer_id: net_core::peer::PeerId(0),
                reason: String::new(),
            })
            .await;
        assert!(!consumed);
    }

    #[tokio::test]
    async fn block_received_triggers_eb_validation() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, mut outcome_rx) = test_validator();
        let mut leios = LeiosConsensus::new("test".into(), tx, validator);

        let p = point(99);
        leios
            .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: p.clone(),
                block: vec![],
            })
            .await;

        match outcome_rx.recv().await.expect("outcome") {
            crate::validation::LedgerOutcome::EbValidated { point: got } => {
                assert_eq!(got, p);
            }
            other => panic!("expected EbValidated, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn votes_received_triggers_vote_validation() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, mut outcome_rx) = test_validator();
        let mut leios = LeiosConsensus::new("test".into(), tx, validator);

        let vote_ids = vec![(10u64, vec![0xAAu8])];
        leios
            .handle_event(&NetworkEvent::LeiosVotesReceived {
                vote_ids: vote_ids.clone(),
                vote_data: vec![vec![0x01]],
            })
            .await;

        match outcome_rx.recv().await.expect("outcome") {
            crate::validation::LedgerOutcome::VotesValidated { vote_ids: got } => {
                assert_eq!(got, vote_ids);
            }
            other => panic!("expected VotesValidated, got {other:?}"),
        }
    }
}
