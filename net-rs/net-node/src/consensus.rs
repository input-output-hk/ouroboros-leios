//! Longest-chain consensus with fork tracking.

use std::collections::HashSet;

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::{BlockBody, Point, Tip, WrappedHeader};
use tokio::sync::mpsc;
use tracing::info;

use crate::chain_tree::ChainTree;
use crate::validation::{ValidationComplete, Validator};

/// Consensus state with fork-tracking chain tree.
pub struct Consensus {
    node_id: String,
    chain_tree: ChainTree,
    /// Hash of the last block we actually injected into the chain store.
    /// Distinct from chain_tree.best_tip() which is speculative.
    adopted_tip_hash: Option<[u8; 32]>,
    /// Points of blocks we produced (skip re-fetching).
    self_produced: HashSet<Point>,
    /// Points currently being fetched or validated (avoid duplicate requests).
    in_flight: HashSet<Point>,
    commands: mpsc::Sender<NetworkCommand>,
    validator: Validator,
    /// Security parameter k — prune blocks deeper than this.
    security_param_k: u64,
}

impl Consensus {
    pub fn new(
        node_id: String,
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
        security_param_k: u64,
    ) -> Self {
        Self {
            node_id,
            chain_tree: ChainTree::new(),
            adopted_tip_hash: None,
            self_produced: HashSet::new(),
            in_flight: HashSet::new(),
            commands,
            validator,
            security_param_k,
        }
    }

    /// Register a block we produced ourselves, so we don't re-fetch it.
    /// Returns the block_no to use for injection.
    pub fn register_self_produced(&mut self, point: &Point, header: &WrappedHeader) -> u64 {
        self.self_produced.insert(point.clone());

        // Insert into chain tree from header info.
        if let Some(info) = header.parsed.as_ref() {
            let hash = match point {
                Point::Specific { hash, .. } => *hash,
                _ => return 1,
            };
            self.chain_tree.insert(
                hash,
                point.clone(),
                info.block_number,
                info.slot,
                info.prev_hash,
            );
            // Self-produced blocks are immediately injected.
            self.adopted_tip_hash = Some(hash);
            info.block_number
        } else {
            // Fallback for opaque headers.
            self.chain_tree.best_tip().map_or(1, |(_, bn)| bn + 1)
        }
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

            // Leios: fetch offered EBs, votes, and txs.
            NetworkEvent::LeiosBlockOffered { point } => {
                if !self.in_flight.contains(point) {
                    self.in_flight.insert(point.clone());
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
                let key = Point::Specific {
                    slot: match point {
                        Point::Specific { slot, .. } => *slot,
                        _ => 0,
                    },
                    hash: [0xFE; 32], // distinct key to avoid collision with block fetch
                };
                if !self.in_flight.contains(&key) {
                    self.in_flight.insert(key);
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

    /// Handle a completed validation: inject the block so downstream peers
    /// can fetch it, and update the chain tree. If this causes a fork switch,
    /// issue a rollback to the common ancestor first.
    /// Returns `true` if a fork switch rollback was issued.
    pub async fn on_validation_complete(&mut self, result: ValidationComplete) -> bool {
        let ValidationComplete { point, body } = result;
        self.in_flight.remove(&point);

        // Extract the header from the block body for injection.
        let header = body
            .header()
            .unwrap_or_else(|| WrappedHeader::opaque(Vec::new()));

        let new_hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => [0u8; 32],
        };

        // Insert into chain tree (may already be there from TipAdvanced).
        let block_no = if let Some(info) = header.parsed.as_ref() {
            self.chain_tree.insert(
                new_hash,
                point.clone(),
                info.block_number,
                info.slot,
                info.prev_hash,
            );
            info.block_number
        } else {
            self.chain_tree
                .block_number(&new_hash)
                .unwrap_or_else(|| self.chain_tree.best_tip().map_or(1, |(_, bn)| bn + 1))
        };

        // Detect fork switch: compare against the last adopted tip.
        // If the new block's chain doesn't descend from the adopted tip,
        // we need to rollback to the common ancestor.
        let mut rolled_back = false;
        if let Some(adopted_hash) = self.adopted_tip_hash {
            if adopted_hash != new_hash {
                // Check if adopted tip is an ancestor of the new block
                // (simple chain extension) or on a different fork.
                let is_ancestor = self.chain_tree.ancestors(new_hash).contains(&adopted_hash);

                if !is_ancestor {
                    // Fork switch! Find common ancestor and rollback.
                    if let Some(ancestor) =
                        self.chain_tree.find_common_ancestor(adopted_hash, new_hash)
                    {
                        if let Some(ancestor_point) = self.chain_tree.point(&ancestor) {
                            let ancestor_point = ancestor_point.clone();
                            info!(
                                node_id = %self.node_id,
                                new_tip = %point,
                                ancestor = %ancestor_point,
                                "fork switch: rolling back to common ancestor"
                            );

                            let _ = self
                                .commands
                                .send(NetworkCommand::InjectRollback {
                                    point: ancestor_point,
                                })
                                .await;
                            rolled_back = true;
                        }
                    }
                }
            }
        }

        info!(
            node_id = %self.node_id,
            %point,
            block_no,
            "block validated, adopting"
        );

        // Update adopted tip.
        self.adopted_tip_hash = Some(new_hash);

        // Prune old blocks beyond k.
        if block_no > self.security_param_k {
            self.chain_tree
                .prune_below(block_no - self.security_param_k);
        }

        // Inject into chain store so we serve it to downstream peers.
        let _ = self
            .commands
            .send(NetworkCommand::InjectBlock {
                point,
                header: Box::new(header),
                body,
                block_no,
            })
            .await;

        rolled_back
    }

    /// A peer announced a new tip.
    async fn on_tip_advanced(&mut self, tip: &Tip, header: &WrappedHeader) {
        let point = &tip.point;

        // Check if this tip is better than our current best BEFORE inserting.
        let dominated = match self.chain_tree.best_tip() {
            None => true,
            Some((_, best_bn)) => tip.block_no > best_bn,
        };

        // Insert into chain tree if we have header info.
        if let Some(info) = header.parsed.as_ref() {
            if let Point::Specific { hash, .. } = point {
                self.chain_tree.insert(
                    *hash,
                    point.clone(),
                    info.block_number,
                    info.slot,
                    info.prev_hash,
                );
            }
        }

        if !dominated {
            return;
        }

        // Don't fetch our own blocks.
        if self.self_produced.contains(point) {
            info!(
                node_id = %self.node_id,
                %tip,
                "adopting self-produced tip"
            );
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

        let _ = self
            .commands
            .send(NetworkCommand::InjectRollback {
                point: point.clone(),
            })
            .await;
    }

    /// Current local tip as a `Tip`, derived from the chain tree.
    #[allow(dead_code)]
    pub fn local_tip(&self) -> Option<Tip> {
        self.chain_tree.best_tip().map(|(point, block_no)| Tip {
            point: point.clone(),
            block_no,
        })
    }

    /// Hash of the current best tip, for passing as prev_hash to block production.
    pub fn tip_hash(&self) -> Option<[u8; 32]> {
        self.chain_tree.best_tip_hash()
    }

    /// Next block number (best tip + 1), for setting in produced block headers.
    pub fn next_block_number(&self) -> u64 {
        self.chain_tree.best_tip().map_or(1, |(_, bn)| bn + 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a fake Shelley+ header with proper CBOR so WrappedHeader::new
    /// parses it into HeaderInfo with block_number, slot, and prev_hash.
    fn make_header(slot: u64, block_number: u64, prev_hash: Option<[u8; 32]>) -> WrappedHeader {
        let issuer_vkey = [0u8; 32];
        let body_hash = [slot as u8; 32];

        let mut header_body = Vec::new();
        let mut hb = minicbor::Encoder::new(&mut header_body);
        let _ = hb
            .array(10)
            .and_then(|e| e.u64(block_number))
            .and_then(|e| e.u64(slot))
            .and_then(|e| match prev_hash {
                Some(h) => e.bytes(&h),
                None => e.null(),
            })
            .and_then(|e| e.bytes(&issuer_vkey))
            .and_then(|e| e.bytes(&[0u8; 32])) // vrf_vkey
            .and_then(|e| e.array(2))
            .and_then(|e| e.bytes(&[0u8; 32]))
            .and_then(|e| e.bytes(&[0u8; 64]))
            .and_then(|e| e.u32(0))
            .and_then(|e| e.bytes(&body_hash))
            .and_then(|e| e.array(4))
            .and_then(|e| e.bytes(&[0u8; 32]))
            .and_then(|e| e.u64(0))
            .and_then(|e| e.u64(0))
            .and_then(|e| e.bytes(&[0u8; 64]))
            .and_then(|e| e.array(2))
            .and_then(|e| e.u32(10))
            .and_then(|e| e.u32(0));

        let mut header_inner = Vec::new();
        let mut hi = minicbor::Encoder::new(&mut header_inner);
        let _ = hi.array(2);
        header_inner.extend_from_slice(&header_body);
        let _ = minicbor::Encoder::new(&mut header_inner).bytes(&[0u8; 64]);

        let mut header_cbor = Vec::new();
        let mut he = minicbor::Encoder::new(&mut header_cbor);
        let _ = he
            .array(2)
            .and_then(|e| e.u32(7))
            .and_then(|e| e.tag(minicbor::data::Tag::new(24)))
            .and_then(|e| e.bytes(&header_inner));

        WrappedHeader::new(header_cbor)
    }

    /// Build a tip + header pair. Returns (tip, header, hash).
    fn make_tip(slot: u64, block_no: u64, prev_hash: Option<[u8; 32]>) -> (Tip, WrappedHeader) {
        let header = make_header(slot, block_no, prev_hash);
        let point = header.point().expect("test header must parse");
        let tip = Tip { point, block_no };
        (tip, header)
    }

    fn make_consensus() -> (Consensus, mpsc::Receiver<NetworkCommand>) {
        let (cmd_tx, cmd_rx) = mpsc::channel(16);
        let config = crate::config::ValidationConfig::default();
        let (validator, _val_rx) = Validator::new(config);
        let consensus = Consensus::new("test".into(), cmd_tx, validator, 2160);
        (consensus, cmd_rx)
    }

    #[tokio::test]
    async fn skips_self_produced_blocks() {
        let (mut consensus, mut cmd_rx) = make_consensus();

        let (tip, header) = make_tip(1, 1, None);
        consensus.register_self_produced(&tip.point, &header);

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
        let (mut consensus, mut cmd_rx) = make_consensus();

        let (tip, header) = make_tip(1, 1, None);
        let event = NetworkEvent::TipAdvanced { tip, header };
        consensus.handle_event(&event).await;

        // Should issue a FetchBlock command.
        let cmd = cmd_rx.recv().await.unwrap();
        assert!(matches!(cmd, NetworkCommand::FetchBlock { .. }));
    }

    #[tokio::test]
    async fn ignores_shorter_chain() {
        let (mut consensus, mut cmd_rx) = make_consensus();

        // Set local tip to block 5.
        let (tip5, header5) = make_tip(5, 5, None);
        consensus.register_self_produced(&tip5.point, &header5);
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip5,
                header: header5.clone(),
            })
            .await;

        // Announce block 3 — should be ignored.
        let (tip3, header3) = make_tip(3, 3, None);
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
        let (mut consensus, mut cmd_rx) = make_consensus();

        let (tip, header) = make_tip(1, 1, None);

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

    #[tokio::test]
    async fn tip_hash_for_production() {
        let (mut consensus, _cmd_rx) = make_consensus();

        assert!(consensus.tip_hash().is_none());

        let (tip, header) = make_tip(1, 1, None);
        let expected_hash = match &tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!("expected specific"),
        };
        consensus.register_self_produced(&tip.point, &header);

        assert_eq!(consensus.tip_hash(), Some(expected_hash));
    }

    #[tokio::test]
    async fn fork_switch_issues_rollback() {
        let (cmd_tx, mut cmd_rx) = mpsc::channel(32);
        let config = crate::config::ValidationConfig::default();
        let (validator, _val_rx) = Validator::new(config);
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator, 2160);

        // Build chain A: blocks 1, 2, 3 (self-produced, so they're in the tree).
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1);

        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip2.point, &hdr2);

        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));
        consensus.register_self_produced(&tip3.point, &hdr3);

        assert_eq!(consensus.local_tip().unwrap().block_no, 3);

        // Now announce a competing fork B: fork from block 1.
        // B2 at slot 21, B3 at slot 31, B4 at slot 41 (longer than A).
        let (tipb2, hdrb2) = make_tip(21, 2, Some(hash1));
        let hashb2 = match &tipb2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };

        let (tipb3, hdrb3) = make_tip(31, 3, Some(hashb2));
        let hashb3 = match &tipb3.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };

        let (tipb4, hdrb4) = make_tip(41, 4, Some(hashb3));

        // Insert B2 and B3 into tree (as if we received headers via TipAdvanced).
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tipb2,
                header: hdrb2,
            })
            .await;
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tipb3,
                header: hdrb3,
            })
            .await;
        // B4 is the one that overtakes — announce and fetch it.
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tipb4.clone(),
                header: hdrb4.clone(),
            })
            .await;

        // Drain fetch command.
        let cmd = cmd_rx.recv().await.unwrap();
        assert!(matches!(cmd, NetworkCommand::FetchBlock { .. }));

        // Simulate: block B4 was fetched and validated.
        // Build a minimal block body that produces the same header.
        // We need to go through the validator to get on_validation_complete called.
        // Instead, call on_validation_complete directly with a fake body.
        let fake_body = BlockBody::new(hdrb4.raw.clone()); // won't parse as block, but that's OK
        let result = ValidationComplete {
            point: tipb4.point.clone(),
            body: fake_body,
        };
        consensus.on_validation_complete(result).await;

        // Drain commands: we expect InjectRollback then InjectBlock.
        let mut got_rollback = false;
        let mut got_inject = false;
        while let Ok(cmd) = cmd_rx.try_recv() {
            match cmd {
                NetworkCommand::InjectRollback { .. } => got_rollback = true,
                NetworkCommand::InjectBlock { .. } => got_inject = true,
                _ => {}
            }
        }

        assert!(got_rollback, "fork switch should issue InjectRollback");
        assert!(got_inject, "fork switch should inject the new block");
    }
}
