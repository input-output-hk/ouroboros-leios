//! Longest-chain consensus.
//!
//! Tracks the local validated chain tip. When a peer announces a longer
//! chain, fetches the block, validates it, and adopts it. Self-produced
//! blocks are tracked to avoid re-fetching them.

use std::collections::HashSet;

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::{BlockBody, Point, Tip, WrappedHeader};
use tokio::sync::mpsc;
use tracing::info;

use crate::validation::{ValidationComplete, Validator};

/// Consensus state tracking the local chain tip.
pub struct Consensus {
    node_id: String,
    local_tip: Option<Tip>,
    /// Points of blocks we produced (skip re-fetching).
    self_produced: HashSet<Point>,
    /// Points currently being fetched or validated (avoid duplicate requests).
    in_flight: HashSet<Point>,
    commands: mpsc::Sender<NetworkCommand>,
    validator: Validator,
}

impl Consensus {
    pub fn new(
        node_id: String,
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
    ) -> Self {
        Self {
            node_id,
            local_tip: None,
            self_produced: HashSet::new(),
            in_flight: HashSet::new(),
            commands,
            validator,
        }
    }

    /// Register a block we produced ourselves, so we don't re-fetch it.
    pub fn register_self_produced(&mut self, point: &Point) {
        self.self_produced.insert(point.clone());
    }

    /// Handle a network event. Returns true if the event was consumed by
    /// consensus (caller should not log it separately).
    pub async fn handle_event(&mut self, event: &NetworkEvent) -> bool {
        match event {
            NetworkEvent::TipAdvanced { tip, header } => {
                self.on_tip_advanced(tip, header).await;
                true
            }
            NetworkEvent::BlockReceived { point, body } => {
                self.on_block_received(point, body);
                true
            }
            NetworkEvent::RolledBack { point, tip } => {
                self.on_rolled_back(point, tip).await;
                true
            }
            NetworkEvent::BlockFetchFailed { from, to } => {
                // Remove from in-flight so it can be retried.
                self.in_flight.remove(from);
                self.in_flight.remove(to);
                info!(
                    node_id = %self.node_id,
                    from = %from,
                    to = %to,
                    "block fetch failed"
                );
                true
            }
            _ => false,
        }
    }

    /// Handle a completed validation: inject the block so downstream peers
    /// can fetch it, and update the local tip.
    pub async fn on_validation_complete(&mut self, result: ValidationComplete) {
        let ValidationComplete { point, body } = result;
        self.in_flight.remove(&point);

        // Build a header from the body for injection.
        let header = WrappedHeader::opaque(body.raw.clone());

        // Update local tip (increment block_no).
        let block_no = self.local_tip.as_ref().map_or(1, |t| t.block_no + 1);
        let new_tip = Tip {
            point: point.clone(),
            block_no,
        };

        info!(
            node_id = %self.node_id,
            %point,
            block_no,
            "block validated, adopting"
        );

        self.local_tip = Some(new_tip);

        // Inject into chain store so we serve it to downstream peers.
        let _ = self
            .commands
            .send(NetworkCommand::InjectBlock {
                point,
                header: Box::new(header),
                body,
            })
            .await;
    }

    /// A peer announced a new tip.
    async fn on_tip_advanced(&mut self, tip: &Tip, _header: &WrappedHeader) {
        let dominated = self
            .local_tip
            .as_ref()
            .is_none_or(|local| tip.block_no > local.block_no);

        if !dominated {
            return;
        }

        let point = &tip.point;

        // Don't fetch our own blocks.
        if self.self_produced.contains(point) {
            // We produced this — just adopt the tip directly.
            info!(
                node_id = %self.node_id,
                %tip,
                "adopting self-produced tip"
            );
            self.local_tip = Some(tip.clone());
            return;
        }

        // Don't issue duplicate fetches.
        if self.in_flight.contains(point) {
            return;
        }

        info!(
            node_id = %self.node_id,
            %tip,
            "fetching block for longer chain"
        );

        self.in_flight.insert(point.clone());
        let _ = self
            .commands
            .send(NetworkCommand::FetchBlock {
                point: point.clone(),
            })
            .await;
    }

    /// A fetched block arrived — submit to validation.
    fn on_block_received(&mut self, point: &Point, body: &BlockBody) {
        info!(
            node_id = %self.node_id,
            %point,
            body_len = body.raw.len(),
            "block received, validating"
        );
        self.validator.validate_block(point.clone(), body.clone());
    }

    /// Chain rolled back.
    async fn on_rolled_back(&mut self, point: &Point, tip: &Tip) {
        info!(
            node_id = %self.node_id,
            to = %point,
            %tip,
            "rolling back"
        );

        // Reset local tip to the rollback point.
        self.local_tip = Some(tip.clone());

        let _ = self
            .commands
            .send(NetworkCommand::InjectRollback {
                point: point.clone(),
            })
            .await;
    }

    /// Current local tip.
    #[allow(dead_code)]
    pub fn local_tip(&self) -> Option<&Tip> {
        self.local_tip.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_tip(slot: u64, block_no: u64) -> (Tip, WrappedHeader) {
        let hash = [slot as u8; 32];
        let point = Point::Specific { slot, hash };
        let tip = Tip { point, block_no };
        let header = WrappedHeader::opaque(vec![0u8; 10]);
        (tip, header)
    }

    #[tokio::test]
    async fn skips_self_produced_blocks() {
        let (cmd_tx, mut cmd_rx) = mpsc::channel(16);
        let config = crate::config::ValidationConfig::default();
        let (validator, _val_rx) = Validator::new(config);
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator);

        let (tip, header) = make_tip(1, 1);
        consensus.register_self_produced(&tip.point);

        let event = NetworkEvent::TipAdvanced {
            tip: tip.clone(),
            header,
        };
        consensus.handle_event(&event).await;

        // Should NOT issue a FetchBlock command.
        assert!(cmd_rx.try_recv().is_err());
        // But should adopt the tip.
        assert_eq!(consensus.local_tip().unwrap().block_no, 1);
    }

    #[tokio::test]
    async fn fetches_longer_chain() {
        let (cmd_tx, mut cmd_rx) = mpsc::channel(16);
        let config = crate::config::ValidationConfig::default();
        let (validator, _val_rx) = Validator::new(config);
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator);

        let (tip, header) = make_tip(1, 1);
        let event = NetworkEvent::TipAdvanced { tip, header };
        consensus.handle_event(&event).await;

        // Should issue a FetchBlock command.
        let cmd = cmd_rx.recv().await.unwrap();
        match cmd {
            NetworkCommand::FetchBlock { point } => {
                assert_eq!(
                    point,
                    Point::Specific {
                        slot: 1,
                        hash: [1; 32]
                    }
                );
            }
            other => panic!("expected FetchBlock, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn ignores_shorter_chain() {
        let (cmd_tx, mut cmd_rx) = mpsc::channel(16);
        let config = crate::config::ValidationConfig::default();
        let (validator, _val_rx) = Validator::new(config);
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator);

        // Set local tip to block 5.
        let (tip5, header5) = make_tip(5, 5);
        consensus.register_self_produced(&tip5.point);
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip5,
                header: header5,
            })
            .await;

        // Announce block 3 — should be ignored.
        let (tip3, header3) = make_tip(3, 3);
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip3,
                header: header3,
            })
            .await;

        assert!(cmd_rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn no_duplicate_fetches() {
        let (cmd_tx, mut cmd_rx) = mpsc::channel(16);
        let config = crate::config::ValidationConfig::default();
        let (validator, _val_rx) = Validator::new(config);
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator);

        let (tip, header) = make_tip(1, 1);

        // Announce same tip twice.
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip.clone(),
                header: header.clone(),
            })
            .await;
        consensus
            .handle_event(&NetworkEvent::TipAdvanced { tip, header })
            .await;

        // Only one FetchBlock command.
        let _cmd = cmd_rx.recv().await.unwrap();
        assert!(cmd_rx.try_recv().is_err());
    }
}
