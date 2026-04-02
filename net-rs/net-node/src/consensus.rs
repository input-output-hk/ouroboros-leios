//! Longest-chain consensus with fork tracking.

use std::collections::{HashMap, HashSet};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::{BlockBody, Point, Tip, WrappedHeader};
use tokio::sync::mpsc;
use tracing::info;

use crate::chain_tree::{is_better_tip, ChainTree, ChainTreeEntry};
use crate::validation::{ValidationComplete, Validator};

/// A block body cached after fetch or self-production.
struct CachedBlock {
    point: Point,
    header: WrappedHeader,
    body: BlockBody,
    block_no: u64,
    prev_hash: Option<[u8; 32]>,
}

/// Consensus state with fork-tracking chain tree.
pub struct Consensus {
    node_id: String,
    chain_tree: ChainTree,
    /// Hash of the last block we actually injected into the chain store.
    adopted_tip_hash: Option<[u8; 32]>,
    /// Points of blocks we produced (skip re-fetching).
    self_produced: HashSet<Point>,
    /// All block bodies we possess (fetched or self-produced). Pruned beyond k.
    block_cache: HashMap<[u8; 32], CachedBlock>,
    /// Which cached blocks have passed validation.
    validated: HashSet<[u8; 32]>,
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
            block_cache: HashMap::new(),
            validated: HashSet::new(),
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
            self.block_cache.entry(hash).or_insert(CachedBlock {
                point: point.clone(),
                header: header.clone(),
                body: BlockBody::opaque(Vec::new()),
                block_no: info.block_number,
                prev_hash: info.prev_hash,
            });
            self.validated.insert(hash);
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
                if from != to {
                    // Range fetch failed (peer doesn't have the `from` block,
                    // likely on a different fork). Retry fetching just the tip.
                    info!(
                        node_id = %self.node_id,
                        from = %from,
                        to = %to,
                        "range fetch failed, retrying tip only"
                    );
                    self.in_flight.insert(to.clone());
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchBlockRange {
                            from: to.clone(),
                            to: to.clone(),
                        })
                        .await;
                } else {
                    info!(
                        node_id = %self.node_id,
                        from = %from,
                        to = %to,
                        "block fetch failed"
                    );
                }
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

    /// Handle a completed validation: mark validated, inject if contiguous,
    /// check fork switches, fetch missing ancestors.
    /// Returns `true` if a fork switch rollback was issued.
    pub async fn on_validation_complete(&mut self, result: ValidationComplete) -> bool {
        let ValidationComplete { point } = result;
        self.in_flight.remove(&point);

        let new_hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return false,
        };

        if !self.block_cache.contains_key(&new_hash) {
            tracing::warn!(
                node_id = %self.node_id,
                %point,
                "validation complete for block not in cache — ignoring"
            );
            return false;
        }

        self.validated.insert(new_hash);

        // If contiguous with adopted tip, inject immediately + drain forward.
        let prev_hash = self
            .block_cache
            .get(&new_hash)
            .and_then(|cb| cb.prev_hash)
            .or_else(|| self.chain_tree.prev_hash(&new_hash));
        let contiguous = match (self.adopted_tip_hash, prev_hash) {
            (None, None) => true,
            (Some(a), Some(p)) => a == p,
            _ => false,
        };
        if contiguous {
            self.inject_block(new_hash).await;
            self.drain_validated_blocks().await;
        }

        // Check if any validated block enables a better fork switch.
        let rolled_back = self.try_fork_switch().await;
        self.drain_validated_blocks().await;
        self.fetch_unvalidated_ancestors().await;

        // Prune old blocks beyond k.
        if let Some(adopted) = self.adopted_tip_hash {
            if let Some(bn) = self.chain_tree.block_number(&adopted) {
                if bn > self.security_param_k {
                    let min = bn - self.security_param_k;
                    self.chain_tree.prune_below(min);
                    self.block_cache.retain(|_, cb| cb.block_no >= min);
                    self.validated.retain(|h| self.block_cache.contains_key(h));
                }
            }
        }

        rolled_back
    }

    /// A peer announced a new tip.
    async fn on_tip_advanced(&mut self, tip: &Tip, header: &WrappedHeader) {
        let point = &tip.point;

        // Check if this tip is better than our current best BEFORE inserting.
        let tip_hash = match point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        let dominated = match self.chain_tree.best_tip() {
            None => true,
            Some((_, best_bn)) => {
                let best_hash = self.chain_tree.best_tip_hash().unwrap_or([0xFF; 32]);
                is_better_tip(tip.block_no, &tip_hash, best_bn, &best_hash)
            }
        };

        // Insert the announced header into the chain tree.
        // When catching up, the header may be an intermediate block (different
        // from tip), so use the header's own point. When current, use tip's
        // point to avoid rehashing.
        if let Some(info) = header.parsed.as_ref() {
            let (insert_hash, insert_point) = if info.block_number == tip.block_no {
                // Header IS the tip — use tip's pre-computed hash.
                match point {
                    Point::Specific { hash, .. } => (*hash, point.clone()),
                    _ => return,
                }
            } else {
                // Header is an intermediate block — compute its own hash.
                match header.point() {
                    Some(hp) => match &hp {
                        Point::Specific { hash, .. } => (*hash, hp),
                        _ => return,
                    },
                    None => return,
                }
            };
            self.chain_tree.insert(
                insert_hash,
                insert_point,
                info.block_number,
                info.slot,
                info.prev_hash,
            );
        }

        if !dominated {
            // Even though we're not fetching this tip, the newly inserted
            // header may have filled a gap in the adopted tip's ancestry.
            // Check and fetch any unvalidated ancestors that are now reachable.
            self.fetch_unvalidated_ancestors().await;
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

        // Walk chain_tree ancestors from tip to find the earliest unvalidated
        // block — issue a range fetch from there to the tip so we get all
        // intermediate blocks on a fork in one request.
        let tip_hash = match point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        let ancestors = self.chain_tree.ancestors(tip_hash);
        let mut fetch_from = point.clone();
        for &hash in &ancestors {
            if self.block_cache.contains_key(&hash) {
                break; // we already have this block
            }
            if let Some(p) = self.chain_tree.point(&hash) {
                if self.self_produced.contains(p) {
                    break;
                }
                fetch_from = p.clone();
            }
        }

        info!(
            node_id = %self.node_id,
            %tip,
            from = %fetch_from,
            "fetching blocks for longer chain"
        );

        self.in_flight.insert(point.clone());
        let _ = self
            .commands
            .send(NetworkCommand::FetchBlockRange {
                from: fetch_from,
                to: point.clone(),
            })
            .await;
    }

    /// A fetched block arrived — cache it and submit to validation.
    fn on_block_received(&mut self, point: &Point, body: &BlockBody) {
        let hash = match point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        if self.block_cache.contains_key(&hash) {
            return; // duplicate
        }
        let header = body
            .header()
            .unwrap_or_else(|| WrappedHeader::opaque(Vec::new()));
        let block_no = header
            .parsed
            .as_ref()
            .map(|i| i.block_number)
            .or_else(|| self.chain_tree.block_number(&hash))
            .unwrap_or(0);
        let prev_hash = header
            .parsed
            .as_ref()
            .and_then(|i| i.prev_hash)
            .or_else(|| self.chain_tree.prev_hash(&hash));
        self.block_cache.insert(
            hash,
            CachedBlock {
                point: point.clone(),
                header,
                body: body.clone(),
                block_no,
                prev_hash,
            },
        );
        info!(
            node_id = %self.node_id,
            %point,
            body_len = body.raw.len(),
            "block received, validating"
        );
        self.validator.validate_block(point.clone(), body.clone());
    }

    /// Inject a block into the chain store and update adopted tip.
    async fn inject_block(&mut self, hash: [u8; 32]) {
        let cb = match self.block_cache.get(&hash) {
            Some(cb) => cb,
            None => return,
        };
        info!(
            node_id = %self.node_id,
            point = %cb.point,
            block_no = cb.block_no,
            "block validated, adopting"
        );
        self.adopted_tip_hash = Some(hash);
        self.validated.insert(hash);
        let _ = self
            .commands
            .send(NetworkCommand::InjectBlock {
                point: cb.point.clone(),
                header: Box::new(cb.header.clone()),
                body: cb.body.clone(),
                block_no: cb.block_no,
            })
            .await;
    }

    /// Check if any validated block forms a better chain than the adopted tip,
    /// with ALL blocks from the common ancestor validated and cached.
    /// If so, rollback and replay the winning chain.
    async fn try_fork_switch(&mut self) -> bool {
        let adopted_hash = match self.adopted_tip_hash {
            Some(h) => h,
            None => return false,
        };
        let adopted_bn = self.chain_tree.block_number(&adopted_hash).unwrap_or(0);

        // Find the best validated block that's better than adopted tip.
        let best = self
            .block_cache
            .iter()
            .filter(|(&h, cb)| {
                self.validated.contains(&h)
                    && is_better_tip(cb.block_no, &h, adopted_bn, &adopted_hash)
            })
            .max_by_key(|(_, cb)| cb.block_no)
            .map(|(h, _)| *h);

        let best_hash = match best {
            Some(h) => h,
            None => return false,
        };

        // Find common ancestor.
        let ancestor = match self
            .chain_tree
            .find_common_ancestor(adopted_hash, best_hash)
        {
            Some(a) => a,
            None => return false,
        };

        // Walk from best backward to ancestor, collecting the exact chain.
        // All blocks must be in validated_blocks (no gaps).
        let mut chain = Vec::new();
        let mut cur = best_hash;
        loop {
            if cur == ancestor {
                break;
            }
            if !self.validated.contains(&cur) {
                let in_cache = self.block_cache.contains_key(&cur);
                let bn = self.chain_tree.block_number(&cur);
                info!(
                    node_id = %self.node_id,
                    hash = format!("{:02x}{:02x}", cur[30], cur[31]),
                    block_no = ?bn,
                    in_cache,
                    "fork switch blocked: block not validated"
                );
                return false;
            }
            chain.push(cur);
            match self.chain_tree.prev_hash(&cur) {
                Some(prev) => cur = prev,
                None => return false,
            }
        }
        chain.reverse(); // now ancestor→tip order

        let ancestor_point = match self.chain_tree.point(&ancestor) {
            Some(p) => p.clone(),
            None => return false,
        };

        info!(
            node_id = %self.node_id,
            ancestor = %ancestor_point,
            chain_len = chain.len(),
            new_tip_block_no = self.block_cache.get(&best_hash).map(|cb| cb.block_no).unwrap_or(0),
            "fork switch: rolling back and replaying winning chain"
        );

        let _ = self
            .commands
            .send(NetworkCommand::InjectRollback {
                point: ancestor_point,
            })
            .await;
        self.adopted_tip_hash = Some(ancestor);

        // Inject the winning chain in order.
        for hash in chain {
            self.inject_block(hash).await;
        }
        true
    }

    /// Drain validated blocks forward from adopted tip, injecting each
    /// contiguous block.
    async fn drain_validated_blocks(&mut self) {
        loop {
            let adopted_hash = match self.adopted_tip_hash {
                Some(h) => h,
                None => return,
            };
            let next = self
                .block_cache
                .iter()
                .find(|(&h, cb)| cb.prev_hash == Some(adopted_hash) && self.validated.contains(&h))
                .map(|(h, _)| *h);
            match next {
                Some(h) => self.inject_block(h).await,
                None => return,
            }
        }
    }

    /// Fetch ancestors we don't have yet for the adopted tip and the best
    /// unadopted validated block (to enable fork switches).
    async fn fetch_unvalidated_ancestors(&mut self) {
        let mut roots: Vec<[u8; 32]> = Vec::new();
        if let Some(h) = self.adopted_tip_hash {
            roots.push(h);
        }
        // Walk from the best validated block that isn't the adopted tip.
        // This traces the chain the fork switch needs, finding gaps where
        // intermediate blocks haven't been fetched yet.
        let best_unadopted = self
            .block_cache
            .iter()
            .filter(|(&h, _)| self.validated.contains(&h) && !roots.contains(&h))
            .max_by_key(|(_, cb)| cb.block_no)
            .map(|(h, _)| *h);
        if let Some(h) = best_unadopted {
            roots.push(h);
        }

        for root in roots {
            let ancestors = self.chain_tree.ancestors(root);
            let mut gap_start: Option<Point> = None;
            let mut gap_end: Option<Point> = None;
            let adopted_set: HashSet<_> = self
                .adopted_tip_hash
                .map(|h| self.chain_tree.ancestors(h).into_iter().collect())
                .unwrap_or_default();
            for &hash in ancestors.iter().skip(1) {
                if adopted_set.contains(&hash) {
                    break; // reached the adopted chain — stop
                }
                if self.block_cache.contains_key(&hash) {
                    continue; // have this block — keep looking deeper
                }
                if let Some(p) = self.chain_tree.point(&hash) {
                    if self.self_produced.contains(p) || self.in_flight.contains(p) {
                        break;
                    }
                    gap_start = Some(p.clone());
                    if gap_end.is_none() {
                        gap_end = Some(p.clone());
                    }
                }
            }
            if let (Some(from), Some(to)) = (gap_start, gap_end) {
                info!(
                    node_id = %self.node_id,
                    %from,
                    %to,
                    "fetching missing ancestors"
                );
                let _ = self
                    .commands
                    .send(NetworkCommand::FetchBlockRange { from, to })
                    .await;
            }
        }
    }

    /// Peer chain rolled back (ChainSync MsgRollBackward).
    ///
    /// We only log this — actual chain store rollbacks are handled by
    /// `on_validation_complete` when a fork switch is triggered. Blindly
    /// rolling back the chain store here would destroy state when a single
    /// peer diverges while others are still on the longer chain.
    async fn on_rolled_back(&mut self, point: &Point, tip: &Tip) {
        info!(
            node_id = %self.node_id,
            to = %point,
            %tip,
            "peer chain rolled back (no local rollback)"
        );
    }

    /// Current local tip as a `Tip`, derived from the chain tree.
    #[allow(dead_code)]
    pub fn local_tip(&self) -> Option<Tip> {
        self.chain_tree.best_tip().map(|(point, block_no)| Tip {
            point: point.clone(),
            block_no,
        })
    }

    /// Snapshot the recent chain tree for UI display.
    /// Uses the adopted tip (last validated block) rather than the speculative
    /// best tip, so the prev_hash chain is always connected.
    /// Returns (chain_tree_entries, tip_block_no, tip_hash_suffix).
    pub fn chain_tree_snapshot(&self) -> (Vec<ChainTreeEntry>, Option<u64>, Option<String>) {
        match self.adopted_tip_hash {
            Some(hash) => {
                let block_no = self.chain_tree.block_number(&hash);
                let entries = self.chain_tree.snapshot(hash, 10, block_no);
                let tip_hash = Some(format!("{:02x}{:02x}", hash[30], hash[31]));
                (entries, block_no, tip_hash)
            }
            None => (Vec::new(), None, None),
        }
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

        // Should issue a FetchBlockRange command.
        let cmd = cmd_rx.recv().await.unwrap();
        assert!(matches!(cmd, NetworkCommand::FetchBlockRange { .. }));
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

        // Only one FetchBlockRange command.
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
                tip: tipb2.clone(),
                header: hdrb2.clone(),
            })
            .await;
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tipb3.clone(),
                header: hdrb3.clone(),
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
        assert!(matches!(cmd, NetworkCommand::FetchBlockRange { .. }));

        // Simulate: blocks B2, B3, B4 were fetched and validated in order.
        // The fork switch only happens once the full chain is available.
        for (tip, hdr) in [
            (tipb2, hdrb2),
            (tipb3, hdrb3),
            (tipb4.clone(), hdrb4.clone()),
        ] {
            consensus.on_block_received(&tip.point, &BlockBody::new(hdr.raw.clone()));
            consensus
                .on_validation_complete(ValidationComplete {
                    point: tip.point.clone(),
                })
                .await;
        }

        // Run deferred fork switch check.

        // Drain commands: we expect InjectRollback + InjectBlocks for B2,B3,B4.
        let mut got_rollback = false;
        let mut inject_count = 0;
        while let Ok(cmd) = cmd_rx.try_recv() {
            match cmd {
                NetworkCommand::InjectRollback { .. } => got_rollback = true,
                NetworkCommand::InjectBlock { .. } => inject_count += 1,
                _ => {}
            }
        }

        assert!(got_rollback, "fork switch should issue InjectRollback");
        assert!(
            inject_count >= 3,
            "should inject B2, B3, B4: got {inject_count}"
        );
    }

    #[tokio::test]
    async fn fork_switch_no_regression() {
        // Verify that adopted_tip doesn't regress when a lower fork block
        // validates before a higher one.
        let (cmd_tx, mut cmd_rx) = mpsc::channel(256);
        let config = crate::config::ValidationConfig::default();
        let (validator, _val_rx) = Validator::new(config);
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator, 2160);

        // Build chain A: blocks 1..5 (self-produced).
        let mut prev: Option<[u8; 32]> = None;
        let mut hashes = Vec::new();
        for i in 1..=5u64 {
            let (tip, hdr) = make_tip(i * 10, i, prev);
            let hash = match &tip.point {
                Point::Specific { hash, .. } => *hash,
                _ => panic!(),
            };
            consensus.register_self_produced(&tip.point, &hdr);
            hashes.push(hash);
            prev = Some(hash);
        }
        assert_eq!(consensus.local_tip().unwrap().block_no, 5);

        // Fork B diverges after block 2.
        // B3 at slot 31, B4 at slot 41, ..., B6 at slot 61.
        let fork_base = hashes[1]; // hash of block 2
        let (tipb3, hdrb3) = make_tip(31, 3, Some(fork_base));
        let hashb3 = match &tipb3.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tipb4, hdrb4) = make_tip(41, 4, Some(hashb3));
        let hashb4 = match &tipb4.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tipb5, hdrb5) = make_tip(51, 5, Some(hashb4));
        let hashb5 = match &tipb5.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tipb6, hdrb6) = make_tip(61, 6, Some(hashb5));

        // Insert fork headers into chain tree (as if received via TipAdvanced).
        for (tip, hdr) in [
            (tipb3.clone(), hdrb3.clone()),
            (tipb4.clone(), hdrb4.clone()),
            (tipb5.clone(), hdrb5.clone()),
            (tipb6.clone(), hdrb6.clone()),
        ] {
            consensus
                .handle_event(&NetworkEvent::TipAdvanced { tip, header: hdr })
                .await;
        }
        // Drain any fetch commands from TipAdvanced.
        while cmd_rx.try_recv().is_ok() {}

        // Simulate fetching + validating B3..B6 in order.
        for (tip, hdr) in [
            (tipb3.clone(), hdrb3.clone()),
            (tipb4.clone(), hdrb4.clone()),
            (tipb5.clone(), hdrb5.clone()),
            (tipb6.clone(), hdrb6.clone()),
        ] {
            consensus.on_block_received(&tip.point, &BlockBody::new(hdr.raw.clone()));
            consensus
                .on_validation_complete(ValidationComplete {
                    point: tip.point.clone(),
                })
                .await;
        }
        // Run deferred fork switch check.

        // Drain all commands.
        while cmd_rx.try_recv().is_ok() {}

        // adopted_tip should now be block 6.
        assert_eq!(
            consensus
                .chain_tree
                .block_number(&consensus.adopted_tip_hash.unwrap()),
            Some(6),
            "adopted tip should be 6 after fork switch"
        );

        // All fork blocks should have been adopted (drained from validated_blocks
        // into the chain store). The bodies remain in validated_blocks for
        // future replay, so we just verify the tip is correct above.
    }
}
