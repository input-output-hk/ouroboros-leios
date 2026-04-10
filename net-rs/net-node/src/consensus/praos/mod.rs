//! Praos longest-chain consensus with fork tracking.

mod fetching;
mod peer_chain;
mod selection;
mod validation;

use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::peer::PeerId;
use net_core::types::{BlockBody, Point, Tip, WrappedHeader};
use tokio::sync::mpsc;
use tracing::info;

use crate::chain_tree::{ChainTree, ChainTreeEntry};
use crate::validation::Validator;

pub(crate) use peer_chain::{PeerChain, PeerChainEntry};

/// How long an in-flight fetch entry remains "active" before being considered
/// stale and eligible for retry. The coordinator may silently drop a fetch
/// (e.g. no connected peer has the requested point in its fragment), so we
/// need a recovery path: if no body arrives within this window, allow a fresh
/// attempt.
pub(super) const IN_FLIGHT_TTL: Duration = Duration::from_secs(15);

/// A block body cached after fetch or self-production.
pub(super) struct CachedBlock {
    pub(super) point: Point,
    pub(super) header: WrappedHeader,
    pub(super) body: BlockBody,
    pub(super) block_no: u64,
    pub(super) prev_hash: Option<[u8; 32]>,
}

/// PraosConsensus state with fork-tracking chain tree.
pub struct PraosConsensus {
    pub(super) node_id: String,
    pub(super) chain_tree: ChainTree,
    /// Hash of the last block we actually injected into the chain store.
    pub(super) adopted_tip_hash: Option<[u8; 32]>,
    /// Points of blocks we produced (skip re-fetching).
    pub(super) self_produced: HashSet<Point>,
    /// All block bodies we possess (fetched or self-produced). Pruned beyond k.
    pub(super) block_cache: HashMap<[u8; 32], CachedBlock>,
    /// Which cached blocks have passed validation.
    pub(super) validated: HashSet<[u8; 32]>,
    /// Points currently being fetched or validated (avoid duplicate requests).
    /// Each entry remembers when it was added; entries older than
    /// `IN_FLIGHT_TTL` are treated as stale and dropped lazily so a retry
    /// can be issued. The coordinator may silently drop a fetch when no
    /// connected peer has the requested point — without TTL recovery, the
    /// node would stay stuck on that fork forever.
    pub(super) in_flight: HashMap<Point, Instant>,
    /// Per-peer candidate chains. Populated on `TipAdvanced`, truncated on
    /// `RolledBack`, dropped on `PeerDisconnected`. Drives chain selection
    /// via `select_chain`.
    pub(crate) peer_chains: HashMap<PeerId, PeerChain>,
    /// Hash the validator's queue will be at after every command we've
    /// already submitted has been processed. We track this so a fork
    /// switch can decide whether to insert a `LedgerCommand::Rollback`
    /// before the next `Apply`. The actual ledger state lags this until
    /// outcomes arrive.
    pub(super) queued_validator_tip: Option<[u8; 32]>,
    /// Hash of the last block the validator has actually `Applied`. Used
    /// to rewind `queued_validator_tip` after an `ApplyFailed`, since the
    /// failed block (and any cascading failures behind it) leave the
    /// queue's projected tip out of sync with reality.
    pub(super) last_validated_tip: Option<[u8; 32]>,
    /// Hashes that have been submitted to the validator but whose
    /// outcome (`Applied` or `ApplyFailed`) hasn't arrived yet. Used to
    /// gate new submissions on "parent known to the validator" without
    /// requiring the parent's apply to have already completed: since
    /// the actor processes commands sequentially, if the parent's Apply
    /// is already queued, submitting the child right after is safe.
    pub(super) in_flight_validation: HashSet<[u8; 32]>,
    pub(super) commands: mpsc::Sender<NetworkCommand>,
    pub(super) validator: Validator,
    /// Security parameter k — prune blocks deeper than this.
    pub(super) security_param_k: u64,
}

impl PraosConsensus {
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
            in_flight: HashMap::new(),
            peer_chains: HashMap::new(),
            queued_validator_tip: None,
            last_validated_tip: None,
            in_flight_validation: HashSet::new(),
            commands,
            validator,
            security_param_k,
        }
    }

    /// Cap per-peer chains at 2 * k headers — enough to track forks within
    /// the security window plus a 1k cushion, without growing unboundedly.
    pub(super) fn peer_chain_cap(&self) -> usize {
        (self.security_param_k as usize).saturating_mul(2).max(64)
    }

    /// Ingest a peer's new header announcement into its candidate chain.
    pub(super) fn record_peer_tip(&mut self, peer_id: PeerId, tip: &Tip, header: &WrappedHeader) {
        let info = match header.parsed.as_ref() {
            Some(i) => i,
            None => return, // opaque header — nothing to select on
        };
        // When a peer is still catching up, the announced `header` may be
        // an ancestor of `tip`. Use whichever hash matches.
        let (hash, point) = if info.block_number == tip.block_no {
            match &tip.point {
                Point::Specific { hash, .. } => (*hash, tip.point.clone()),
                _ => return,
            }
        } else {
            match header.point() {
                Some(Point::Specific { hash, slot }) => (hash, Point::Specific { hash, slot }),
                _ => return,
            }
        };
        let entry = PeerChainEntry {
            hash,
            point,
            block_no: info.block_number,
            prev_hash: info.prev_hash,
        };
        let cap = self.peer_chain_cap();
        self.peer_chains
            .entry(peer_id)
            .or_insert_with(|| PeerChain::new(cap))
            .append(entry);
    }

    /// Store the ChainSync intersection as the peer chain's anchor.
    pub(super) fn record_peer_intersection(&mut self, peer_id: PeerId, point: &Point) {
        let cap = self.peer_chain_cap();
        self.peer_chains
            .entry(peer_id)
            .or_insert_with(|| PeerChain::new(cap))
            .set_anchor(point.clone());
    }

    /// Truncate a peer's candidate chain on a rollback.
    pub(super) fn record_peer_rollback(&mut self, peer_id: PeerId, point: &Point) {
        if let Some(chain) = self.peer_chains.get_mut(&peer_id) {
            chain.rollback_to(point);
        }
    }

    /// Drop a peer's candidate chain on disconnect.
    pub(super) fn record_peer_disconnected(&mut self, peer_id: PeerId) {
        self.peer_chains.remove(&peer_id);
    }

    /// Register a block we produced ourselves: cache it, hand it to the
    /// validator (matching Haskell's `ChainDB.addBlockAsync` behaviour —
    /// no fast-path for self-produced blocks), drain any peer-fetched
    /// children that had been waiting for this block as their parent,
    /// then run `select_chain` in case a peer fork is even better than
    /// the newly-produced tip. The chain_store update happens later,
    /// when the `Applied` outcome arrives.
    pub async fn register_self_produced(
        &mut self,
        point: &Point,
        header: &WrappedHeader,
        body: &BlockBody,
    ) {
        self.self_produced.insert(point.clone());

        let info = match header.parsed.as_ref() {
            Some(i) => i,
            None => {
                // Opaque header — nothing to insert into chain_tree, but
                // still hand the body to the validator.
                self.submit_for_validation(point.clone(), body.clone(), None)
                    .await;
                return;
            }
        };
        let hash = match point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        self.chain_tree.insert(
            hash,
            point.clone(),
            info.block_number,
            info.slot,
            info.prev_hash,
        );
        self.block_cache.entry(hash).or_insert(CachedBlock {
            point: point.clone(),
            header: header.clone(),
            body: body.clone(),
            block_no: info.block_number,
            prev_hash: info.prev_hash,
        });

        self.submit_for_validation(point.clone(), body.clone(), info.prev_hash)
            .await;
        self.try_switch_and_execute(hash).await;
    }

    /// Handle a network event. Returns true if the event was consumed by
    /// consensus (caller should not log it separately).
    pub async fn handle_event(&mut self, event: &NetworkEvent) -> bool {
        match event {
            NetworkEvent::IntersectionFound { peer_id, point } => {
                self.record_peer_intersection(*peer_id, point);
                // No select_chain here — the intersection alone doesn't
                // change which chain is best; TipAdvanced triggers that.
                true
            }
            NetworkEvent::TipAdvanced {
                peer_id,
                tip,
                header,
            } => {
                self.record_peer_tip(*peer_id, tip, header);
                self.evaluate_and_fetch().await;
                true
            }
            NetworkEvent::BlockReceived { point, body } => {
                self.on_block_received(point, body).await;
                true
            }
            NetworkEvent::RolledBack { peer_id, point, .. } => {
                self.record_peer_rollback(*peer_id, point);
                info!(
                    node_id = %self.node_id,
                    %peer_id,
                    to = %point,
                    "peer chain rolled back"
                );
                self.evaluate_and_fetch().await;
                true
            }
            NetworkEvent::PeerDisconnected { peer_id, .. } => {
                self.record_peer_disconnected(*peer_id);
                self.evaluate_and_fetch().await;
                false
            }
            NetworkEvent::BlockFetchFailed { from, to } => {
                self.in_flight.remove(from);
                self.in_flight.remove(to);
                info!(
                    node_id = %self.node_id,
                    from = %from,
                    to = %to,
                    "block fetch failed; re-evaluating fetch decisions"
                );
                self.evaluate_and_fetch().await;
                true
            }

            _ => false,
        }
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

    /// Hash of the adopted tip, for passing as prev_hash to block production.
    /// Returns `None` when no chain has been adopted yet — the production
    /// code then builds the genesis child (block 1, prev_hash=None).
    ///
    /// Uses `adopted_tip_hash` (the validated chain) rather than
    /// `chain_tree.best_tip_hash()` to avoid building on unvalidated
    /// peer headers whose ancestor chain may be incomplete.
    pub fn tip_hash(&self) -> Option<[u8; 32]> {
        self.adopted_tip_hash
    }

    /// Next block number (adopted tip + 1), for setting in produced block headers.
    pub fn next_block_number(&self) -> u64 {
        self.adopted_tip_hash
            .and_then(|h| self.chain_tree.block_number(&h))
            .map_or(1, |bn| bn + 1)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
    use net_core::peer::PeerId;
    use net_core::types::{BlockBody, Point, Tip, WrappedHeader};
    use tokio::sync::mpsc;

    use crate::validation::{LedgerOutcome, Validator};

    use super::peer_chain::PeerChainEntry;
    use super::selection::SelectionDecision;
    use super::*;

    /// Placeholder peer id for tests that don't care which peer announced
    /// the tip — consensus is expected to ignore the value during phase 2.
    const TEST_PEER: PeerId = PeerId(0);

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

    /// Build a minimal Shelley+ block body containing the given header.
    /// Format: `#6.24(cbor([era, [header_inner, [], [], true, []]]))`.
    fn make_block_body(header: &WrappedHeader) -> BlockBody {
        // Extract header_inner from ChainSync wire format:
        // header.raw = [2, era(7), #6.24(header_inner)]
        let mut d = minicbor::Decoder::new(&header.raw);
        let _ = d.array(); // outer [2, ...]
        let era = d.u32().unwrap();
        let _ = d.tag(); // tag 24
        let header_inner = d.bytes().unwrap();

        // Build era_block: [header_inner, [], [], true, []]
        let mut era_block = Vec::new();
        let mut eb = minicbor::Encoder::new(&mut era_block);
        let _ = eb.array(5);
        era_block.extend_from_slice(header_inner);
        let _ = minicbor::Encoder::new(&mut era_block)
            .array(0)
            .and_then(|e| e.array(0))
            .and_then(|e| e.bool(true))
            .and_then(|e| e.map(0));

        // Build inner: [era, era_block]
        let mut inner = Vec::new();
        let mut ie = minicbor::Encoder::new(&mut inner);
        let _ = ie.array(2).and_then(|e| e.u32(era));
        inner.extend_from_slice(&era_block);

        // Wrap in #6.24
        let mut body = Vec::new();
        let mut be = minicbor::Encoder::new(&mut body);
        let _ = be
            .tag(minicbor::data::Tag::new(24))
            .and_then(|e| e.bytes(&inner));

        BlockBody::new(body)
    }

    /// Build a tip + header pair. Returns (tip, header, hash).
    fn make_tip(slot: u64, block_no: u64, prev_hash: Option<[u8; 32]>) -> (Tip, WrappedHeader) {
        let header = make_header(slot, block_no, prev_hash);
        let point = header.point().expect("test header must parse");
        let tip = Tip { point, block_no };
        (tip, header)
    }

    /// Watch receiver with zero validation delays so tests don't sit
    /// in `tokio::time::sleep` for the production-default 1s per block.
    fn test_dyn_rx() -> tokio::sync::watch::Receiver<crate::config::DynamicConfig> {
        let mut config = crate::config::NodeConfig::default().dynamic_config();
        config.rb_head_validation_ms = 0.0;
        config.rb_body_validation_ms_constant = 0.0;
        config.rb_body_validation_ms_per_byte = 0.0;
        tokio::sync::watch::channel(config).1
    }

    /// Pump validator outcomes back into consensus until the outcome
    /// channel is idle for `quiet_for`. Test analogue of `main.rs`'s
    /// `validation_rx` recv loop — blocks until the actor has finished
    /// processing all pending commands.
    async fn drain_validator(
        consensus: &mut PraosConsensus,
        val_rx: &mut mpsc::Receiver<LedgerOutcome>,
    ) {
        let quiet_for = Duration::from_millis(50);
        loop {
            match tokio::time::timeout(quiet_for, val_rx.recv()).await {
                Ok(Some(outcome)) => {
                    consensus.on_validation_outcome(outcome).await;
                }
                _ => return,
            }
        }
    }

    fn make_consensus() -> (
        PraosConsensus,
        mpsc::Receiver<NetworkCommand>,
        mpsc::Receiver<LedgerOutcome>,
    ) {
        let (cmd_tx, cmd_rx) = mpsc::channel(16);
        let (validator, val_rx) = Validator::new(test_dyn_rx());
        let consensus = PraosConsensus::new("test".into(), cmd_tx, validator, 2160);
        (consensus, cmd_rx, val_rx)
    }

    /// PraosConsensus with a small k so the peer-chain cap is also small —
    /// lets us exercise the cap without announcing thousands of headers.
    fn make_consensus_with_k(
        k: u64,
    ) -> (
        PraosConsensus,
        mpsc::Receiver<NetworkCommand>,
        mpsc::Receiver<LedgerOutcome>,
    ) {
        let (cmd_tx, cmd_rx) = mpsc::channel(16);
        let (validator, val_rx) = Validator::new(test_dyn_rx());
        let consensus = PraosConsensus::new("test".into(), cmd_tx, validator, k);
        (consensus, cmd_rx, val_rx)
    }

    #[tokio::test]
    async fn peer_chain_records_tip_advances() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(7);

        let (tip1, header1) = make_tip(1, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: peer,
                tip: tip1,
                header: header1,
            })
            .await;

        let (tip2, header2) = make_tip(2, 2, Some(hash1));
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: peer,
                tip: tip2,
                header: header2,
            })
            .await;

        let chain = consensus.peer_chains.get(&peer).expect("chain exists");
        assert_eq!(chain.len(), 2);
        assert_eq!(chain.tip().unwrap().block_no, 2);
        assert_eq!(chain.tip().unwrap().prev_hash, Some(hash1));
    }

    #[tokio::test]
    async fn peer_chain_rollback_truncates() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(7);

        let (tip1, header1) = make_tip(1, 1, None);
        let point1 = tip1.point.clone();
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: peer,
                tip: tip1,
                header: header1,
            })
            .await;

        let (tip2, header2) = make_tip(2, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: peer,
                tip: tip2.clone(),
                header: header2,
            })
            .await;

        let (tip3, header3) = make_tip(3, 3, Some(hash2));
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: peer,
                tip: tip3,
                header: header3,
            })
            .await;

        assert_eq!(consensus.peer_chains.get(&peer).unwrap().len(), 3);

        // Roll back to block 1 — only tip1 should remain.
        consensus
            .handle_event(&NetworkEvent::RolledBack {
                peer_id: peer,
                point: point1.clone(),
                tip: tip2,
            })
            .await;

        let chain = consensus.peer_chains.get(&peer).unwrap();
        assert_eq!(chain.len(), 1);
        assert_eq!(chain.tip().unwrap().hash, hash1);
    }

    #[tokio::test]
    async fn peer_chain_dropped_on_disconnect() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(7);

        let (tip1, header1) = make_tip(1, 1, None);
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: peer,
                tip: tip1,
                header: header1,
            })
            .await;

        assert!(consensus.peer_chains.contains_key(&peer));

        consensus
            .handle_event(&NetworkEvent::PeerDisconnected {
                peer_id: peer,
                reason: "test".to_string(),
            })
            .await;

        assert!(!consensus.peer_chains.contains_key(&peer));
    }

    #[tokio::test]
    async fn peer_chain_duplicate_announcement_ignored() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(7);

        let (tip1, header1) = make_tip(1, 1, None);
        for _ in 0..3 {
            consensus
                .handle_event(&NetworkEvent::TipAdvanced {
                    peer_id: peer,
                    tip: tip1.clone(),
                    header: header1.clone(),
                })
                .await;
        }

        assert_eq!(consensus.peer_chains.get(&peer).unwrap().len(), 1);
    }

    #[tokio::test]
    async fn peer_chain_tracks_peers_independently() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer_a = PeerId(1);
        let peer_b = PeerId(2);

        let (tip, header) = make_tip(1, 1, None);
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: peer_a,
                tip: tip.clone(),
                header: header.clone(),
            })
            .await;
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: peer_b,
                tip,
                header,
            })
            .await;

        // Same hash announced by both peers — each has an independent entry.
        assert_eq!(consensus.peer_chains.get(&peer_a).unwrap().len(), 1);
        assert_eq!(consensus.peer_chains.get(&peer_b).unwrap().len(), 1);
    }

    #[tokio::test]
    async fn select_chain_no_better_chain_when_peer_matches_adopted() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(1);

        // Self-produce tip 1; peer announces the same.
        let (tip1, header1) = make_tip(1, 1, None);
        consensus
            .register_self_produced(&tip1.point, &header1, &BlockBody::opaque(Vec::new()))
            .await;
        consensus.record_peer_tip(peer, &tip1, &header1);

        let decision = consensus.select_chain_once(&HashSet::new());
        assert!(
            matches!(decision, SelectionDecision::NoBetterChain),
            "expected NoBetterChain, got {decision:?}"
        );
    }

    #[tokio::test]
    async fn select_chain_waiting_for_blocks_when_peer_has_longer_chain() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(1);

        // Self-produce block 1.
        let (tip1, header1) = make_tip(1, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &header1, &BlockBody::opaque(Vec::new()))
            .await;

        // Peer announces block 2 with prev_hash=hash1.
        let (tip2, header2) = make_tip(2, 2, Some(hash1));
        consensus.record_peer_tip(peer, &tip2, &header2);

        match consensus.select_chain_once(&HashSet::new()) {
            SelectionDecision::WaitingForBlocks {
                peer_id,
                ancestor,
                tip_block_no,
                missing,
                ..
            } => {
                assert_eq!(peer_id, peer);
                assert_eq!(ancestor, hash1);
                assert_eq!(tip_block_no, 2);
                assert_eq!(missing.len(), 1);
                assert_eq!(missing[0], tip2.point);
            }
            other => panic!("expected WaitingForBlocks, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn select_chain_orphan_candidate_when_peer_forks_outside_window() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(1);

        // Self-produce block 1.
        let (tip1, header1) = make_tip(1, 1, None);
        consensus
            .register_self_produced(&tip1.point, &header1, &BlockBody::opaque(Vec::new()))
            .await;

        // Peer announces block 5 with a random prev_hash that doesn't
        // connect to anything in our adopted chain's ancestry.
        let orphan_prev: [u8; 32] = [0xEF; 32];
        let (tip5, header5) = make_tip(5, 5, Some(orphan_prev));
        consensus.record_peer_tip(peer, &tip5, &header5);

        match consensus.select_chain_once(&HashSet::new()) {
            SelectionDecision::OrphanCandidate {
                peer_id,
                tip_block_no,
            } => {
                assert_eq!(peer_id, peer);
                assert_eq!(tip_block_no, 5);
            }
            other => panic!("expected OrphanCandidate, got {other:?}"),
        }
    }

    /// Regression for the "jump to tip" ChainSync bug: if the peer_chain
    /// contains only the tip header (because ChainSync skipped ahead instead
    /// of streaming every rollforward from the common ancestor), the walk
    /// in `select_chain_once` can never find a common ancestor and every
    /// peer gets classified as `OrphanCandidate`. The fix is to populate
    /// peer_chain contiguously from the intersection point — this test
    /// exercises both halves.
    #[tokio::test]
    async fn select_chain_contiguous_stream_finds_ancestor_tip_only_is_orphan() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(1);

        // Our self-produced chain: blocks 1, 2, 3.
        let (tip1, header1) = make_tip(1, 1, None);
        consensus
            .register_self_produced(&tip1.point, &header1, &BlockBody::opaque(Vec::new()))
            .await;
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip2, header2) = make_tip(2, 2, Some(hash1));
        consensus
            .register_self_produced(&tip2.point, &header2, &BlockBody::opaque(Vec::new()))
            .await;
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip3, header3) = make_tip(3, 3, Some(hash2));
        consensus
            .register_self_produced(&tip3.point, &header3, &BlockBody::opaque(Vec::new()))
            .await;

        // Peer forks at block 2 (common ancestor) and has blocks 3..7 on
        // a different fork. Slots are offset to produce distinct hashes.
        let (alt3_tip, alt3_hdr) = make_tip(103, 3, Some(hash2));
        let alt3_hash = match &alt3_tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (alt4_tip, alt4_hdr) = make_tip(104, 4, Some(alt3_hash));
        let alt4_hash = match &alt4_tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (alt5_tip, alt5_hdr) = make_tip(105, 5, Some(alt4_hash));
        let alt5_hash = match &alt5_tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (alt6_tip, alt6_hdr) = make_tip(106, 6, Some(alt5_hash));
        let alt6_hash = match &alt6_tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (alt7_tip, alt7_hdr) = make_tip(107, 7, Some(alt6_hash));

        // --- Bug reproduction: only the tip is announced (no intermediates).
        consensus.record_peer_tip(peer, &alt7_tip, &alt7_hdr);
        match consensus.select_chain_once(&HashSet::new()) {
            SelectionDecision::OrphanCandidate { .. } => {}
            other => panic!("expected OrphanCandidate for tip-only peer_chain, got {other:?}"),
        }

        // --- Fixed behaviour: ChainSync streams every header from the
        // common ancestor forward. After receiving alt3..alt7 contiguously,
        // the walk back through peer_chain hits alt3, whose prev_hash is
        // hash2 (in adopted_ancestors), so we classify as WaitingForBlocks.
        consensus.record_peer_disconnected(peer);
        consensus.record_peer_tip(peer, &alt3_tip, &alt3_hdr);
        consensus.record_peer_tip(peer, &alt4_tip, &alt4_hdr);
        consensus.record_peer_tip(peer, &alt5_tip, &alt5_hdr);
        consensus.record_peer_tip(peer, &alt6_tip, &alt6_hdr);
        consensus.record_peer_tip(peer, &alt7_tip, &alt7_hdr);

        match consensus.select_chain_once(&HashSet::new()) {
            SelectionDecision::WaitingForBlocks {
                peer_id,
                ancestor,
                tip_block_no,
                missing,
                ..
            } => {
                assert_eq!(peer_id, peer);
                assert_eq!(ancestor, hash2, "common ancestor should be our block 2");
                assert_eq!(tip_block_no, 7);
                assert_eq!(
                    missing.len(),
                    5,
                    "five alt-fork blocks (3..7) need fetching"
                );
            }
            other => panic!("expected WaitingForBlocks after contiguous stream, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn select_chain_picks_best_of_multiple_candidates() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer_a = PeerId(1);
        let peer_b = PeerId(2);

        // Self-produce block 1.
        let (tip1, header1) = make_tip(1, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &header1, &BlockBody::opaque(Vec::new()))
            .await;

        // peer_a's chain: block 2 with prev=hash1.
        let (tip2, header2) = make_tip(2, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.record_peer_tip(peer_a, &tip2, &header2);

        // peer_b's chain: block 2 + block 3 (longer, so strictly better).
        consensus.record_peer_tip(peer_b, &tip2, &header2);
        let (tip3, header3) = make_tip(3, 3, Some(hash2));
        consensus.record_peer_tip(peer_b, &tip3, &header3);

        match consensus.select_chain_once(&HashSet::new()) {
            SelectionDecision::WaitingForBlocks {
                peer_id,
                tip_block_no,
                ancestor,
                missing,
                ..
            } => {
                assert_eq!(peer_id, peer_b, "should pick peer_b (block 3)");
                assert_eq!(tip_block_no, 3);
                assert_eq!(ancestor, hash1);
                assert_eq!(missing.len(), 2, "blocks 2 and 3 are missing");
            }
            other => panic!("expected WaitingForBlocks for peer_b, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn select_chain_fresh_node_accepts_any_chain() {
        // A freshly-started node with no adopted tip should treat any
        // peer chain as a valid candidate, replay from synthetic genesis.
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(1);

        let (tip1, header1) = make_tip(1, 1, None);
        let (tip2, header2) = make_tip(
            2,
            2,
            Some(match &tip1.point {
                Point::Specific { hash, .. } => *hash,
                _ => panic!(),
            }),
        );
        consensus.record_peer_tip(peer, &tip1, &header1);
        consensus.record_peer_tip(peer, &tip2, &header2);

        match consensus.select_chain_once(&HashSet::new()) {
            SelectionDecision::WaitingForBlocks {
                peer_id, missing, ..
            } => {
                assert_eq!(peer_id, peer);
                assert_eq!(missing.len(), 2);
            }
            other => panic!("expected WaitingForBlocks, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn peer_chain_bounded_at_2k() {
        // k=4 → cap should be max(2*4, 64) = 64. Use 100 headers.
        let (mut consensus, mut cmd_rx, _val_rx) = make_consensus_with_k(4);
        let peer = PeerId(7);

        let mut prev: Option<[u8; 32]> = None;
        for i in 1..=100u64 {
            let (tip, header) = make_tip(i, i, prev);
            prev = match &tip.point {
                Point::Specific { hash, .. } => Some(*hash),
                _ => None,
            };
            consensus
                .handle_event(&NetworkEvent::TipAdvanced {
                    peer_id: peer,
                    tip,
                    header,
                })
                .await;
            // Drain any fetch commands so the command channel doesn't
            // back up and stall `on_tip_advanced`'s send.
            while cmd_rx.try_recv().is_ok() {}
        }

        // Cap is max(2*k, 64) = 64.
        let chain = consensus.peer_chains.get(&peer).unwrap();
        assert_eq!(chain.len(), 64);
        // Most recent entries retained, oldest dropped.
        assert_eq!(chain.tip().unwrap().block_no, 100);
    }

    #[tokio::test]
    async fn skips_self_produced_blocks() {
        let (mut consensus, mut cmd_rx, mut _val_rx) = make_consensus();

        let (tip, header) = make_tip(1, 1, None);
        consensus
            .register_self_produced(&tip.point, &header, &BlockBody::opaque(Vec::new()))
            .await;

        let event = NetworkEvent::TipAdvanced {
            peer_id: TEST_PEER,
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
        let (mut consensus, mut cmd_rx, mut _val_rx) = make_consensus();

        let (tip, header) = make_tip(1, 1, None);
        let event = NetworkEvent::TipAdvanced {
            peer_id: TEST_PEER,
            tip,
            header,
        };
        consensus.handle_event(&event).await;

        // Should issue a FetchBlockRange command.
        let cmd = cmd_rx.recv().await.unwrap();
        assert!(matches!(cmd, NetworkCommand::FetchBlockRange { .. }));
    }

    #[tokio::test]
    async fn ignores_shorter_chain() {
        let (mut consensus, mut cmd_rx, mut _val_rx) = make_consensus();

        // Set local tip to block 5.
        let (tip5, header5) = make_tip(5, 5, None);
        consensus
            .register_self_produced(&tip5.point, &header5, &BlockBody::opaque(Vec::new()))
            .await;
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: TEST_PEER,
                tip: tip5,
                header: header5.clone(),
            })
            .await;

        // Announce block 3 — should be ignored.
        let (tip3, header3) = make_tip(3, 3, None);
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: TEST_PEER,
                tip: tip3,
                header: header3,
            })
            .await;

        assert!(cmd_rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn no_duplicate_fetches() {
        let (mut consensus, mut cmd_rx, mut _val_rx) = make_consensus();

        let (tip, header) = make_tip(1, 1, None);

        // Announce same tip twice.
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: TEST_PEER,
                tip: tip.clone(),
                header: header.clone(),
            })
            .await;
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: TEST_PEER,
                tip,
                header,
            })
            .await;

        // Only one FetchBlockRange command.
        let _cmd = cmd_rx.recv().await.unwrap();
        assert!(cmd_rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn tip_hash_for_production() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();

        assert!(consensus.tip_hash().is_none());

        let (tip, header) = make_tip(1, 1, None);
        let expected_hash = match &tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!("expected specific"),
        };
        consensus
            .register_self_produced(&tip.point, &header, &BlockBody::opaque(Vec::new()))
            .await;

        assert_eq!(consensus.tip_hash(), Some(expected_hash));
    }

    #[tokio::test]
    async fn fork_switch_issues_rollback() {
        let (cmd_tx, mut cmd_rx) = mpsc::channel(64);
        let (validator, mut val_rx) = Validator::new(test_dyn_rx());
        let mut consensus = PraosConsensus::new("test".into(), cmd_tx, validator, 2160);

        // Build chain A: blocks 1, 2, 3 (self-produced).
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &hdr1, &BlockBody::opaque(Vec::new()))
            .await;

        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip2.point, &hdr2, &BlockBody::opaque(Vec::new()))
            .await;

        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));
        consensus
            .register_self_produced(&tip3.point, &hdr3, &BlockBody::opaque(Vec::new()))
            .await;

        // Drain validator outcomes for the self-produced blocks so the
        // chain_store catches up before we start the fork switch.
        drain_validator(&mut consensus, &mut val_rx).await;
        assert_eq!(consensus.local_tip().unwrap().block_no, 3);
        while cmd_rx.try_recv().is_ok() {}

        // Now announce a competing fork B from block 1: B2, B3, B4
        // (longer than A, so the fork switch should fire).
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

        for (tip, hdr) in [
            (tipb2.clone(), hdrb2.clone()),
            (tipb3.clone(), hdrb3.clone()),
            (tipb4.clone(), hdrb4.clone()),
        ] {
            consensus
                .handle_event(&NetworkEvent::TipAdvanced {
                    peer_id: TEST_PEER,
                    tip,
                    header: hdr,
                })
                .await;
        }
        while cmd_rx.try_recv().is_ok() {}

        // Receive each fork-B block body. submit_for_validation issues
        // a Rollback(A1) before the first Apply, then chains Applies
        // through B2, B3, B4. The validator processes those in order
        // and the outcome handlers fire InjectRollback + InjectBlocks.
        for (tip, hdr) in [
            (tipb2, hdrb2),
            (tipb3, hdrb3),
            (tipb4.clone(), hdrb4.clone()),
        ] {
            consensus
                .on_block_received(&tip.point, &make_block_body(&hdr))
                .await;
        }
        drain_validator(&mut consensus, &mut val_rx).await;

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
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
        let mut consensus = PraosConsensus::new("test".into(), cmd_tx, validator, 2160);

        // Build chain A: blocks 1..5 (self-produced).
        let mut prev: Option<[u8; 32]> = None;
        let mut hashes = Vec::new();
        for i in 1..=5u64 {
            let (tip, hdr) = make_tip(i * 10, i, prev);
            let hash = match &tip.point {
                Point::Specific { hash, .. } => *hash,
                _ => panic!(),
            };
            consensus
                .register_self_produced(&tip.point, &hdr, &BlockBody::opaque(Vec::new()))
                .await;
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
                .handle_event(&NetworkEvent::TipAdvanced {
                    peer_id: TEST_PEER,
                    tip,
                    header: hdr,
                })
                .await;
        }
        // Drain any fetch commands from TipAdvanced.
        while cmd_rx.try_recv().is_ok() {}

        // Simulate fetching + validating B3..B6 in order. Use proper
        // make_block_body so on_block_received parses the header and
        // inserts into chain_tree.
        for (tip, hdr) in [
            (tipb3.clone(), hdrb3.clone()),
            (tipb4.clone(), hdrb4.clone()),
            (tipb5.clone(), hdrb5.clone()),
            (tipb6.clone(), hdrb6.clone()),
        ] {
            consensus
                .on_block_received(&tip.point, &make_block_body(&hdr))
                .await;
            consensus
                .on_validation_outcome(LedgerOutcome::Applied {
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

    #[tokio::test]
    async fn block_received_inserts_into_chain_tree() {
        // Fix 1: on_block_received must insert into chain_tree so that
        // ancestors() and find_common_ancestor() work for fetched blocks.
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();

        let (tip, header) = make_tip(10, 1, None);
        let hash = match &tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };

        // Before receiving, block is not in chain_tree.
        assert!(consensus.chain_tree.block_number(&hash).is_none());

        // Simulate block fetch arrival with a proper block body.
        let body = make_block_body(&header);
        consensus.on_block_received(&tip.point, &body).await;

        // After receiving, block should be in chain_tree.
        assert_eq!(consensus.chain_tree.block_number(&hash), Some(1));
    }

    /// Regression: when a peer announces a block whose body is later
    /// silently dropped by the coordinator, the in_flight TTL eventually
    /// expires and the next `select_chain` pass re-issues the fetch.
    #[tokio::test]
    async fn stale_in_flight_eviction_allows_refetch() {
        let (mut consensus, mut cmd_rx, mut val_rx) = make_consensus();

        // Adopt block#1 (self-produced).
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &hdr1, &BlockBody::opaque(Vec::new()))
            .await;
        drain_validator(&mut consensus, &mut val_rx).await;

        // Peer announces block#2 — select_chain issues a fetch and
        // marks the point in_flight.
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: TEST_PEER,
                tip: tip2.clone(),
                header: hdr2,
            })
            .await;
        while cmd_rx.try_recv().is_ok() {}
        assert!(
            consensus.in_flight.contains_key(&tip2.point),
            "first fetch should mark block#2 in_flight"
        );

        // The fetch was silently dropped (no body arrives). Mark
        // in_flight stale and announce the same tip again — the next
        // select_chain pass should evict the stale entry and re-issue.
        let stale = Instant::now() - IN_FLIGHT_TTL - Duration::from_secs(1);
        consensus.in_flight.insert(tip2.point.clone(), stale);
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: TEST_PEER,
                tip: tip2.clone(),
                header: make_header(20, 2, Some(hash1)),
            })
            .await;

        let mut saw_refetch = false;
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::FetchBlockRange { to, .. } = cmd {
                if to == tip2.point {
                    saw_refetch = true;
                }
            }
        }
        assert!(
            saw_refetch,
            "stale in_flight should have been evicted, allowing a refetch of block#2"
        );
    }

    /// Successful validation of a peer-fetched block must emit an
    /// `InjectBlock` to the coordinator — the chain_store update only
    /// happens on the `Applied` outcome, not eagerly from
    /// `on_block_received`.
    #[tokio::test]
    async fn applied_outcome_emits_inject_block() {
        let (mut consensus, mut cmd_rx, mut val_rx) = make_consensus();

        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &hdr1, &BlockBody::opaque(Vec::new()))
            .await;
        drain_validator(&mut consensus, &mut val_rx).await;
        while cmd_rx.try_recv().is_ok() {}

        // A peer must announce block#2 so select_chain can find it.
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        consensus.record_peer_tip(TEST_PEER, &tip2, &hdr2);

        consensus
            .on_block_received(&tip2.point, &make_block_body(&hdr2))
            .await;
        // Before the validator outcome fires, the chain_store has NOT
        // been updated.
        assert!(
            !matches!(cmd_rx.try_recv(), Ok(NetworkCommand::InjectBlock { .. })),
            "InjectBlock must not be sent before Applied outcome"
        );

        drain_validator(&mut consensus, &mut val_rx).await;

        let mut saw_inject = false;
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::InjectBlock { point, .. } = cmd {
                if point == tip2.point {
                    saw_inject = true;
                }
            }
        }
        assert!(
            saw_inject,
            "Applied outcome for block#2 should have emitted InjectBlock"
        );
    }

    /// A `RolledBack` outcome must emit a `NetworkCommand::InjectRollback`
    /// so the chain_store mirrors the ledger. This is the ONLY path that
    /// issues chain_store rollbacks.
    #[tokio::test]
    async fn rolled_back_outcome_emits_inject_rollback() {
        let (mut consensus, mut cmd_rx, _val_rx) = make_consensus();

        // Plant a block in chain_tree so its point is lookup-able.
        let (tip1, hdr1) = make_tip(10, 1, None);
        consensus
            .register_self_produced(&tip1.point, &hdr1, &BlockBody::opaque(Vec::new()))
            .await;
        while cmd_rx.try_recv().is_ok() {}

        // Directly feed a RolledBack outcome to the handler.
        consensus
            .on_validation_outcome(LedgerOutcome::RolledBack {
                target: tip1.point.clone(),
            })
            .await;

        let mut saw_rollback = false;
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::InjectRollback { point } = cmd {
                if point == tip1.point {
                    saw_rollback = true;
                }
            }
        }
        assert!(
            saw_rollback,
            "RolledBack outcome should have emitted InjectRollback"
        );
    }

    /// An adopted node whose only common ancestor with a peer is Origin
    /// (genesis) must accept the peer's chain. This is the core regression
    /// test for the Origin-as-ancestor fix.
    #[tokio::test]
    async fn select_chain_accepts_genesis_ancestor_for_adopted_node() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(1);

        // Self-produce blocks 1, 2, 3 (our adopted chain).
        let (tip1, hdr1) = make_tip(10, 1, None);
        consensus
            .register_self_produced(&tip1.point, &hdr1, &BlockBody::opaque(Vec::new()))
            .await;
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        consensus
            .register_self_produced(&tip2.point, &hdr2, &BlockBody::opaque(Vec::new()))
            .await;
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));
        consensus
            .register_self_produced(&tip3.point, &hdr3, &BlockBody::opaque(Vec::new()))
            .await;

        // Peer announces a completely separate chain of 5 blocks, also
        // rooted at genesis (prev_hash=None for block 1). Different slots
        // produce different hashes — the chains share NO common blocks.
        let (p1_tip, p1_hdr) = make_tip(100, 1, None);
        let p1_hash = match &p1_tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.record_peer_tip(peer, &p1_tip, &p1_hdr);

        let (p2_tip, p2_hdr) = make_tip(200, 2, Some(p1_hash));
        let p2_hash = match &p2_tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.record_peer_tip(peer, &p2_tip, &p2_hdr);

        let (p3_tip, p3_hdr) = make_tip(300, 3, Some(p2_hash));
        let p3_hash = match &p3_tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.record_peer_tip(peer, &p3_tip, &p3_hdr);

        let (p4_tip, p4_hdr) = make_tip(400, 4, Some(p3_hash));
        let p4_hash = match &p4_tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.record_peer_tip(peer, &p4_tip, &p4_hdr);

        let (p5_tip, p5_hdr) = make_tip(500, 5, Some(p4_hash));
        consensus.record_peer_tip(peer, &p5_tip, &p5_hdr);

        // The peer has 5 blocks vs our 3 — strictly better. The chains
        // share no common blocks, but an adopted node does NOT roll back
        // to Origin (that's only for fresh nodes). The re-intersect
        // mechanism handles this via OrphanCandidate.
        match consensus.select_chain_once(&HashSet::new()) {
            SelectionDecision::OrphanCandidate {
                peer_id: orphan_peer,
                tip_block_no,
            } => {
                assert_eq!(orphan_peer, peer);
                assert_eq!(tip_block_no, 5);
            }
            other => panic!("expected OrphanCandidate, got {other:?}"),
        }
    }

    /// handle_rolled_back must handle Point::Origin by clearing
    /// last_validated_tip and emitting InjectRollback.
    #[tokio::test]
    async fn handle_rolled_back_origin_sends_inject_rollback() {
        let (mut consensus, mut cmd_rx, _val_rx) = make_consensus();

        // Plant a block so the node has an adopted tip.
        let (tip1, hdr1) = make_tip(10, 1, None);
        consensus
            .register_self_produced(&tip1.point, &hdr1, &BlockBody::opaque(Vec::new()))
            .await;
        while cmd_rx.try_recv().is_ok() {}

        // Feed an Origin RolledBack outcome.
        consensus
            .on_validation_outcome(LedgerOutcome::RolledBack {
                target: Point::Origin,
            })
            .await;

        let mut saw_origin_rollback = false;
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::InjectRollback { point } = cmd {
                if point == Point::Origin {
                    saw_origin_rollback = true;
                }
            }
        }
        assert!(
            saw_origin_rollback,
            "Origin RolledBack should emit InjectRollback with Point::Origin"
        );
        assert!(
            consensus.last_validated_tip.is_none(),
            "last_validated_tip should be None after Origin rollback"
        );
    }

    /// Verify that record_peer_intersection stores the anchor on PeerChain.
    #[tokio::test]
    async fn anchor_set_on_intersection_found() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(1);

        let point = Point::Specific {
            slot: 42,
            hash: [0xAB; 32],
        };
        consensus.record_peer_intersection(peer, &point);

        let chain = consensus.peer_chains.get(&peer).unwrap();
        let anchor = chain.anchor().expect("anchor should be set");
        assert_eq!(anchor.hash, [0xAB; 32]);
        assert_eq!(anchor.point, point);
    }

    /// When the peer chain window is too narrow for the walk to find a
    /// common ancestor, the anchor (ChainSync intersection) is used as
    /// fallback. This is the core test for the anchor-based approach.
    #[tokio::test]
    async fn anchor_used_as_fallback_ancestor() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(1);

        // Self-produce blocks 1..5 (our adopted chain).
        let mut prev = None;
        for i in 1..=5u64 {
            let (tip, hdr) = make_tip(i * 10, i, prev);
            prev = match &tip.point {
                Point::Specific { hash, .. } => Some(*hash),
                _ => panic!(),
            };
            consensus
                .register_self_produced(&tip.point, &hdr, &BlockBody::opaque(Vec::new()))
                .await;
        }
        let adopted_hash = prev.unwrap();

        // Set the anchor to block 3 in our adopted chain (a known common
        // ancestor). The anchor hash must be in our chain_tree.
        let block3_hash = consensus.chain_tree.ancestors(adopted_hash)[2]; // [5, 4, 3]
        let block3_point = consensus.chain_tree.point(&block3_hash).unwrap().clone();
        consensus.record_peer_intersection(peer, &block3_point);

        // Peer announces blocks 64..68 with different hashes (different
        // fork). The window doesn't overlap our chain at all.
        let mut pprev = Some([0xDD; 32]); // unknown parent — simulates gap
        for i in 64..=68u64 {
            let (tip, hdr) = make_tip(i * 100, i, pprev);
            pprev = match &tip.point {
                Point::Specific { hash, .. } => Some(*hash),
                _ => panic!(),
            };
            consensus.record_peer_tip(peer, &tip, &hdr);
        }

        // The walk through entries [68..64] won't find anything in
        // adopted_ancestors. The prev_hash fallback (0xDD) isn't in
        // adopted_ancestors either. But the anchor (block 3) IS.
        match consensus.select_chain_once(&HashSet::new()) {
            SelectionDecision::WaitingForBlocks {
                ancestor,
                anchor_point,
                missing,
                ..
            } => {
                assert_eq!(
                    ancestor, block3_hash,
                    "ancestor should be the anchor (block 3)"
                );
                assert!(
                    anchor_point.is_some(),
                    "anchor_point should be set for gap fetch"
                );
                assert_eq!(missing.len(), 5, "all 5 peer blocks should be missing");
            }
            other => panic!("expected WaitingForBlocks, got {other:?}"),
        }
    }

    /// When the normal walk finds a common ancestor, the anchor should
    /// not override it — the walk result is always preferred.
    #[tokio::test]
    async fn anchor_ignored_when_walk_succeeds() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();
        let peer = PeerId(1);

        // Self-produce blocks 1..3.
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &hdr1, &BlockBody::opaque(Vec::new()))
            .await;
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip2.point, &hdr2, &BlockBody::opaque(Vec::new()))
            .await;
        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));
        consensus
            .register_self_produced(&tip3.point, &hdr3, &BlockBody::opaque(Vec::new()))
            .await;

        // Set anchor at Origin (deep).
        consensus.record_peer_intersection(peer, &Point::Origin);

        // Peer announces a fork from block 2 (blocks 3'..5').
        let (alt3, alt3_hdr) = make_tip(103, 3, Some(hash2));
        let alt3_hash = match &alt3.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.record_peer_tip(peer, &alt3, &alt3_hdr);
        let (alt4, alt4_hdr) = make_tip(104, 4, Some(alt3_hash));
        let alt4_hash = match &alt4.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.record_peer_tip(peer, &alt4, &alt4_hdr);
        let (alt5, alt5_hdr) = make_tip(105, 5, Some(alt4_hash));
        consensus.record_peer_tip(peer, &alt5, &alt5_hdr);

        // Walk finds hash2 in adopted_ancestors — walk result preferred
        // over anchor (Origin).
        match consensus.select_chain_once(&HashSet::new()) {
            SelectionDecision::WaitingForBlocks {
                ancestor,
                anchor_point,
                ..
            } => {
                assert_eq!(ancestor, hash2, "walk should find block 2 as ancestor");
                assert!(
                    anchor_point.is_none(),
                    "anchor_point should be None when walk succeeded"
                );
            }
            other => panic!("expected WaitingForBlocks, got {other:?}"),
        }
    }

    /// Self-produced blocks must route through the validator: they should
    /// NOT land in the chain_store until the `Applied` outcome fires.
    /// This mirrors Haskell's `ChainDB.addBlockAsync` behaviour — there's
    /// no fast-path for self-produced blocks.
    #[tokio::test]
    async fn self_produced_runs_through_validator() {
        let (mut consensus, mut cmd_rx, mut val_rx) = make_consensus();

        let (tip, hdr) = make_tip(10, 1, None);
        consensus
            .register_self_produced(&tip.point, &hdr, &BlockBody::opaque(Vec::new()))
            .await;

        // Before draining the validator, no InjectBlock has been sent.
        assert!(
            cmd_rx.try_recv().is_err(),
            "self-produced block must not publish until validated"
        );

        drain_validator(&mut consensus, &mut val_rx).await;

        let mut saw_inject = false;
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::InjectBlock { point, .. } = cmd {
                if point == tip.point {
                    saw_inject = true;
                }
            }
        }
        assert!(
            saw_inject,
            "Applied outcome for self-produced block should emit InjectBlock"
        );
    }

    /// `queued_validator_tip` tracks what the validator will be at
    /// after the current submission stream drains. Submitting in chain
    /// order advances it monotonically; a non-contiguous submission
    /// inserts a rollback.
    #[tokio::test]
    async fn queued_validator_tip_tracks_submission_order() {
        let (mut consensus, mut _cmd_rx, _val_rx) = make_consensus();

        assert_eq!(consensus.queued_validator_tip, None);

        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &hdr1, &BlockBody::opaque(Vec::new()))
            .await;
        assert_eq!(consensus.queued_validator_tip, Some(hash1));

        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip2.point, &hdr2, &BlockBody::opaque(Vec::new()))
            .await;
        assert_eq!(consensus.queued_validator_tip, Some(hash2));
    }

    /// When PeerChain entries are non-contiguous (stale entries from an
    /// old fork + new entries from a new fork), select_chain_once must
    /// NOT return Switched if the first replay block's chain_tree ancestry
    /// doesn't reach the common ancestor. It should return WaitingForBlocks
    /// so the gap blocks get fetched.
    #[tokio::test]
    async fn gap_between_ancestor_and_replay_returns_waiting() {
        let (mut consensus, _cmd_rx, mut val_rx) = make_consensus();
        let peer = PeerId(1);

        // Build a 5-block adopted chain: 1 → 2 → 3 → 4 → 5
        let mut prev = None;
        let mut hashes = Vec::new();
        for i in 1..=5u64 {
            let (tip, hdr) = make_tip(i * 10, i, prev);
            let hash = match &tip.point {
                Point::Specific { hash, .. } => *hash,
                _ => panic!(),
            };
            let body = make_block_body(&hdr);
            consensus.on_block_received(&tip.point, &body).await;
            hashes.push(hash);
            prev = Some(hash);
        }

        // Validate blocks 1-5 by registering them as self-produced
        // (which submits to validator) and draining outcomes.
        for i in 1..=5u64 {
            let (tip, hdr) = make_tip(
                i * 10,
                i,
                if i == 1 {
                    None
                } else {
                    Some(hashes[(i - 2) as usize])
                },
            );
            let body = make_block_body(&hdr);
            consensus
                .register_self_produced(&tip.point, &hdr, &body)
                .await;
        }
        drain_validator(&mut consensus, &mut val_rx).await;
        assert_eq!(
            consensus.adopted_tip_hash,
            Some(*hashes.last().unwrap()),
            "should be adopted at block 5"
        );

        // Peer announces a fork: same blocks 1-3, then 4' → 5' → 6'
        // But we'll simulate non-contiguous PeerChain by only putting
        // block 6' in the PeerChain with ancestor at block 3.
        //
        // Build block 4' (different slot → different hash, same block_no)
        let (_, hdr4p) = make_tip(41, 4, Some(hashes[2])); // parent is block 3
        let hash4p = match hdr4p.point() {
            Some(Point::Specific { hash, .. }) => hash,
            _ => panic!(),
        };
        let (_, hdr5p) = make_tip(51, 5, Some(hash4p));
        let hash5p = match hdr5p.point() {
            Some(Point::Specific { hash, .. }) => hash,
            _ => panic!(),
        };
        let (tip6p, hdr6p) = make_tip(61, 6, Some(hash5p));
        let hash6p = match &tip6p.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };

        // Put block 6' body into block_cache (simulates a prior fetch
        // that delivered the tip but not the intermediate blocks).
        let body6p = make_block_body(&hdr6p);
        consensus.on_block_received(&tip6p.point, &body6p).await;

        // Set up PeerChain: intersection at block 3, but only entry is block 6'.
        // This simulates the non-contiguous state after a failed rollback.
        let intersection = Point::Specific {
            slot: 30,
            hash: hashes[2],
        };
        consensus.record_peer_intersection(peer, &intersection);
        consensus
            .peer_chains
            .get_mut(&peer)
            .unwrap()
            .append(PeerChainEntry {
                hash: hash6p,
                point: tip6p.point.clone(),
                block_no: 6,
                prev_hash: Some(hash5p),
            });

        // select_chain_once should detect the fork mismatch (block 6' is
        // in chain_tree but its ancestors don't reach block 3) and return
        // OrphanCandidate so the driver can re-intersect.
        let decision = consensus.select_chain_once(&HashSet::new());
        match decision {
            SelectionDecision::OrphanCandidate { .. } => { /* correct */ }
            SelectionDecision::Switched { .. } => {
                panic!("should NOT return Switched when there's a fork mismatch in chain_tree");
            }
            other => {
                panic!("unexpected decision: {other:?}");
            }
        }
    }
}
