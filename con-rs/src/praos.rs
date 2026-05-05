//! Praos longest-chain consensus state machine.
//!
//! `PraosState` owns this node's view of the chain world: its adopted
//! chain tree, block cache, per-peer announced fragments, validator-
//! queue projection, and orphan / in-flight tracking.  It is sans-IO:
//! every public method either mutates state and returns a
//! `Vec<PraosEffect>` describing what the caller's I/O layer should
//! dispatch — fetch a block range, re-intersect with a peer, hand a
//! block to the validator, inject into the chain store — or returns a
//! pure query result.
//!
//! Block bodies and headers are carried as opaque `Vec<u8>`.  CBOR
//! parsing happens at the I/O boundary; con-rs never interprets the
//! bytes.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::time::{Duration, Instant};

use tracing::{info, warn};

use crate::chain_tree::{is_better_tip, ChainTree, ChainTreeEntry};
use crate::peer::PeerId;
use crate::peer_chain::{PeerChain, PeerChainEntry};
use crate::types::Point;

/// How long an in-flight fetch entry remains "active" before being
/// considered stale and eligible for retry.  The coordinator may
/// silently drop a fetch (e.g. no connected peer has the requested
/// point), so we need a recovery path: if no body arrives within this
/// window, allow a fresh fetch.
pub const IN_FLIGHT_TTL: Duration = Duration::from_secs(15);

/// After a peer is classified as `OrphanCandidate`, this much time must
/// pass before it is reconsidered for chain selection.  Caps the
/// orphan-cascade rate at 1/sec per peer even when re-intersection
/// round-trips are millisecond-scale.
pub const ORPHAN_COOLDOWN: Duration = Duration::from_secs(1);

// ---------------------------------------------------------------------------
// Effect type
// ---------------------------------------------------------------------------

/// Logical action that the I/O wrapper should perform.  PraosState emits
/// these as a side-channel to its mutations; the wrapper drains and
/// dispatches each to the appropriate channel (network commands,
/// validator submissions).  Header / body bodies are opaque bytes; the
/// wrapper rehydrates them into wire types as it dispatches.
#[derive(Debug, Clone)]
pub enum PraosEffect {
    /// Request a contiguous block range from the network.  When
    /// `peer_id` is `Some`, the coordinator should prefer that peer.
    FetchBlockRange {
        from: Point,
        to: Point,
        peer_id: Option<PeerId>,
    },
    /// Ask the coordinator to re-run the ChainSync intersection
    /// negotiation with this peer.
    ReIntersect { peer_id: PeerId },
    /// Publish a validated block to the network's responder-side
    /// chain store (so peers fetching from us can get it).
    InjectBlock {
        point: Point,
        header: Vec<u8>,
        body: Vec<u8>,
        block_no: u64,
    },
    /// Roll the chain store back to `target`.  `Origin` clears it.
    InjectRollback { target: Point },
    /// Submit a block to the ledger validator (`LedgerCommand::Apply`).
    ValidatorApply {
        point: Point,
        body: Vec<u8>,
        prev_hash: Option<[u8; 32]>,
    },
    /// Submit a rollback to the ledger validator
    /// (`LedgerCommand::Rollback`).
    ValidatorRollback { target: Point },
}

// ---------------------------------------------------------------------------
// Cached block
// ---------------------------------------------------------------------------

/// A block we possess (fetched from a peer or self-produced).  Header
/// and body are raw CBOR bytes — the wire types live in net-core and
/// are reconstructed by the I/O wrapper when an effect dispatches them.
#[derive(Debug, Clone)]
pub struct CachedBlock {
    pub point: Point,
    pub block_no: u64,
    pub prev_hash: Option<[u8; 32]>,
    pub header: Vec<u8>,
    pub body: Vec<u8>,
}

// ---------------------------------------------------------------------------
// Selection result types
// ---------------------------------------------------------------------------

/// Result of a hybrid ancestor walk that uses `chain_tree` first and
/// falls back to `block_cache` when chain_tree is missing a link.
#[derive(Debug, Clone)]
pub struct HybridWalk {
    /// Hashes from start_hash (index 0) back to the terminating block.
    pub chain: Vec<[u8; 32]>,
    /// True if the walk terminated at a block with `prev_hash = None`
    /// (i.e. genesis child); false if it terminated at a missing parent
    /// or the start block was unknown.
    pub reached_origin: bool,
}

/// Result of a single pass of the Haskell-aligned chain selection.
#[derive(Debug, Clone)]
pub enum SelectionDecision {
    /// No peer has a chain strictly better than the adopted tip.
    NoBetterChain,
    /// A peer has a better tip but its chain doesn't connect to the
    /// adopted chain within the visibility window.
    OrphanCandidate { peer_id: PeerId, tip_block_no: u64 },
    /// A peer has a better tip and all blocks from the common ancestor
    /// to its tip are already validated — a fork switch can happen
    /// immediately.
    Switched {
        peer_id: PeerId,
        ancestor: [u8; 32],
        replay: Vec<[u8; 32]>,
        tip_block_no: u64,
    },
    /// A peer has a better tip but some replay blocks aren't fetched.
    WaitingForBlocks {
        peer_id: PeerId,
        ancestor: [u8; 32],
        anchor_point: Option<Point>,
        missing: Vec<Point>,
        tip_block_no: u64,
    },
}

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// Praos consensus state for one node.
///
/// Fields are `pub` so adapter code can read and selectively
/// manipulate them.  Treat them as state-machine internals: prefer the
/// public methods, which preserve invariants and emit the right
/// effects.
pub struct PraosState {
    pub node_id: String,
    pub security_param_k: u64,

    pub chain_tree: ChainTree,
    pub adopted_tip_hash: Option<[u8; 32]>,

    /// Points of blocks this node produced.
    pub self_produced: BTreeSet<Point>,
    /// All block bodies we possess.  Pruned beyond k.
    pub block_cache: BTreeMap<[u8; 32], CachedBlock>,
    /// Hashes of cached blocks that have passed validation.
    pub validated: BTreeSet<[u8; 32]>,

    /// Per-peer announced chains.  Drives chain selection.
    pub peer_chains: BTreeMap<PeerId, PeerChain>,
    /// Peers on cooldown after being classified as `OrphanCandidate`.
    pub orphan_cooldown: BTreeMap<PeerId, Instant>,

    /// Points currently being fetched (avoid duplicate requests).
    pub in_flight: BTreeMap<Point, Instant>,
    /// Hashes already submitted to the validator but not yet
    /// `Applied` / `ApplyFailed`.
    pub in_flight_validation: BTreeSet<[u8; 32]>,

    /// Hash the validator's queue will be at after every command we've
    /// already submitted has been processed.
    pub queued_validator_tip: Option<[u8; 32]>,
    /// Hash of the last block the validator has actually `Applied`.
    pub last_validated_tip: Option<[u8; 32]>,
}

impl PraosState {
    pub fn new(node_id: String, security_param_k: u64) -> Self {
        Self {
            node_id,
            security_param_k,
            chain_tree: ChainTree::new(),
            adopted_tip_hash: None,
            self_produced: BTreeSet::new(),
            block_cache: BTreeMap::new(),
            validated: BTreeSet::new(),
            peer_chains: BTreeMap::new(),
            orphan_cooldown: BTreeMap::new(),
            in_flight: BTreeMap::new(),
            in_flight_validation: BTreeSet::new(),
            queued_validator_tip: None,
            last_validated_tip: None,
        }
    }

    // -- Queries ------------------------------------------------------------

    /// Cap per-peer chain fragments at `2 * k` headers.
    pub fn peer_chain_cap(&self) -> usize {
        (self.security_param_k as usize).saturating_mul(2).max(64)
    }

    /// Hash of the currently adopted tip, if any.
    pub fn tip_hash(&self) -> Option<[u8; 32]> {
        self.adopted_tip_hash
    }

    /// Block number to assign to the next self-produced block.
    pub fn next_block_number(&self) -> u64 {
        self.adopted_tip_hash
            .and_then(|h| self.chain_tree.block_number(&h))
            .map_or(1, |bn| bn + 1)
    }

    /// `(point, block_no)` of the adopted tip, if any.  Used by the I/O
    /// wrapper to construct a wire-format `Tip`.
    pub fn local_tip(&self) -> Option<(Point, u64)> {
        self.chain_tree
            .best_tip()
            .map(|(point, block_no)| (point.clone(), block_no))
    }

    /// Snapshot the recent chain tree for UI display.
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

    // -- Peer-event mutations (no effects) ----------------------------------

    /// Append a peer's announced header to its candidate chain.  The
    /// caller has already extracted the header's `block_no`, `slot`,
    /// `prev_hash`, and the announced `tip` from the wire types.
    #[allow(clippy::too_many_arguments)]
    pub fn record_peer_tip(
        &mut self,
        peer_id: PeerId,
        tip_point: Point,
        tip_block_no: u64,
        header_block_no: u64,
        header_hash: [u8; 32],
        header_slot: u64,
        header_prev_hash: Option<[u8; 32]>,
    ) {
        // The announced header may be an ancestor of `tip` while a peer
        // catches up.  Use whichever pair matches.
        let (hash, point) = if header_block_no == tip_block_no {
            match &tip_point {
                Point::Specific { hash, .. } => (*hash, tip_point.clone()),
                _ => return,
            }
        } else {
            (
                header_hash,
                Point::Specific {
                    hash: header_hash,
                    slot: header_slot,
                },
            )
        };
        let entry = PeerChainEntry {
            hash,
            point,
            block_no: header_block_no,
            prev_hash: header_prev_hash,
        };
        let cap = self.peer_chain_cap();
        self.peer_chains
            .entry(peer_id)
            .or_insert_with(|| PeerChain::new(cap))
            .append(entry);
    }

    /// Store the ChainSync intersection as the peer chain's anchor.
    pub fn record_peer_intersection(&mut self, peer_id: PeerId, point: Point) {
        let cap = self.peer_chain_cap();
        self.peer_chains
            .entry(peer_id)
            .or_insert_with(|| PeerChain::new(cap))
            .set_anchor(point);
    }

    /// Truncate a peer's candidate chain on a rollback.
    pub fn record_peer_rollback(&mut self, peer_id: PeerId, point: &Point) {
        if let Some(chain) = self.peer_chains.get_mut(&peer_id) {
            chain.rollback_to(point);
        }
    }

    /// Drop a peer's candidate chain on disconnect.  Also clears any
    /// orphan cooldown entry for that peer.
    pub fn record_peer_disconnected(&mut self, peer_id: PeerId) {
        self.peer_chains.remove(&peer_id);
        self.orphan_cooldown.remove(&peer_id);
    }

    // -- High-level event handlers (effect-emitting) ------------------------

    /// A peer announced a new tip.  Records it and runs chain selection.
    #[allow(clippy::too_many_arguments)]
    pub fn on_tip_advanced(
        &mut self,
        peer_id: PeerId,
        tip_point: Point,
        tip_block_no: u64,
        header_block_no: u64,
        header_hash: [u8; 32],
        header_slot: u64,
        header_prev_hash: Option<[u8; 32]>,
        now: Instant,
    ) -> Vec<PraosEffect> {
        self.record_peer_tip(
            peer_id,
            tip_point,
            tip_block_no,
            header_block_no,
            header_hash,
            header_slot,
            header_prev_hash,
        );
        let mut fx = Vec::new();
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx
    }

    /// A fetched block arrived.  Caches it and tries a fork switch
    /// targeting this specific block.  `parsed_header` is `Some` when
    /// the wrapper successfully parsed the header into block-no /
    /// slot / prev-hash; `None` for opaque headers.
    #[allow(clippy::too_many_arguments)]
    pub fn on_block_received(
        &mut self,
        point: Point,
        header_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
        parsed_header: Option<ParsedHeaderInfo>,
    ) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return fx,
        };
        // Dedup.
        if self.block_cache.contains_key(&hash)
            || self.validated.contains(&hash)
            || self.in_flight_validation.contains(&hash)
        {
            return fx;
        }
        let header_was_parsed = parsed_header.is_some();
        let (block_no, slot, prev_hash) = match parsed_header {
            Some(info) => (info.block_number, info.slot, info.prev_hash),
            None => (
                self.chain_tree.block_number(&hash).unwrap_or(0),
                match &point {
                    Point::Specific { slot, .. } => *slot,
                    _ => 0,
                },
                self.chain_tree.prev_hash(&hash),
            ),
        };
        // Insert into chain_tree only when we have a real block_no
        // (parsed header) or, for opaque headers, when fallback metadata
        // is non-default.  Inserting block_no=0 confuses pruning.
        if header_was_parsed || block_no > 0 {
            self.chain_tree
                .insert(hash, point.clone(), block_no, slot, prev_hash);
        }
        self.block_cache.insert(
            hash,
            CachedBlock {
                point: point.clone(),
                block_no,
                prev_hash,
                header: header_bytes,
                body: body_bytes,
            },
        );
        info!(
            node_id = %self.node_id,
            %point,
            block_no,
            "block received and cached"
        );
        self.try_switch_and_execute_internal(hash, &mut fx);
        fx
    }

    /// A `BlockFetch` failed for the requested range.  Drop the
    /// in-flight markers so a retry can be issued.
    pub fn on_block_fetch_failed(
        &mut self,
        from: &Point,
        to: &Point,
        now: Instant,
    ) -> Vec<PraosEffect> {
        self.in_flight.remove(from);
        self.in_flight.remove(to);
        info!(
            node_id = %self.node_id,
            %from, %to,
            "block fetch failed; re-evaluating fetch decisions"
        );
        let mut fx = Vec::new();
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx
    }

    /// A peer rolled its chain back; truncate its fragment and re-run
    /// chain selection.
    pub fn on_peer_rolled_back(
        &mut self,
        peer_id: PeerId,
        point: &Point,
        now: Instant,
    ) -> Vec<PraosEffect> {
        self.record_peer_rollback(peer_id, point);
        info!(
            node_id = %self.node_id,
            %peer_id,
            to = %point,
            "peer chain rolled back"
        );
        let mut fx = Vec::new();
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx
    }

    /// A peer disconnected; drop its fragment and re-run selection in
    /// case its absence frees up a different peer.
    pub fn on_peer_disconnected(
        &mut self,
        peer_id: PeerId,
        now: Instant,
    ) -> Vec<PraosEffect> {
        self.record_peer_disconnected(peer_id);
        let mut fx = Vec::new();
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx
    }

    // -- Self-production ----------------------------------------------------

    /// Register a block we produced ourselves.  Caches it, hands it to
    /// the validator, and runs a fork-switch attempt.
    pub fn register_self_produced(
        &mut self,
        point: Point,
        header_bytes: Vec<u8>,
        body_bytes: Vec<u8>,
        parsed_header: Option<ParsedHeaderInfo>,
    ) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        self.self_produced.insert(point.clone());
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return fx,
        };
        match parsed_header {
            Some(info) => {
                self.chain_tree.insert(
                    hash,
                    point.clone(),
                    info.block_number,
                    info.slot,
                    info.prev_hash,
                );
                self.block_cache
                    .entry(hash)
                    .or_insert(CachedBlock {
                        point: point.clone(),
                        block_no: info.block_number,
                        prev_hash: info.prev_hash,
                        header: header_bytes,
                        body: body_bytes.clone(),
                    });
                self.submit_for_validation_internal(point, body_bytes, info.prev_hash, &mut fx);
                self.try_switch_and_execute_internal(hash, &mut fx);
            }
            None => {
                // Opaque header — submit body to validator, skip
                // chain_tree insertion.
                self.submit_for_validation_internal(point, body_bytes, None, &mut fx);
            }
        }
        fx
    }

    // -- Validation outcomes ------------------------------------------------

    /// Validator reported a successful Apply.  Publish the block to the
    /// chain store, update last-validated tip, prune below k, and re-
    /// run chain selection.
    pub fn on_block_applied(&mut self, point: Point, now: Instant) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return fx,
        };
        self.in_flight.remove(&point);
        self.in_flight_validation.remove(&hash);
        let inject = match self.block_cache.get(&hash) {
            Some(cb) => PraosEffect::InjectBlock {
                point: cb.point.clone(),
                header: cb.header.clone(),
                body: cb.body.clone(),
                block_no: cb.block_no,
            },
            None => {
                warn!(
                    node_id = %self.node_id,
                    %point,
                    "applied outcome for block not in cache — ignoring"
                );
                return fx;
            }
        };
        self.validated.insert(hash);
        self.last_validated_tip = Some(hash);
        info!(
            node_id = %self.node_id,
            %point,
            "block validated, publishing to chain store"
        );
        fx.push(inject);
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
        // Try switching to chain_tree's best tip, then evaluate peers.
        if let Some(best) = self.chain_tree.best_tip_hash() {
            self.try_switch_and_execute_internal(best, &mut fx);
        }
        self.evaluate_and_fetch_internal(now, &mut fx);
        fx
    }

    /// Validator reported an Apply failure.  Rewind the queue
    /// projection so the next submission realigns with the ledger.
    pub fn on_block_apply_failed(&mut self, point: Point, error: String) {
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        self.in_flight.remove(&point);
        self.in_flight_validation.remove(&hash);
        warn!(
            node_id = %self.node_id,
            %point,
            %error,
            "ledger apply failed; rewinding to last validated tip"
        );
        self.queued_validator_tip = self.last_validated_tip;
        self.adopted_tip_hash = self.last_validated_tip;
        self.validated.remove(&hash);
    }

    /// Validator reported a successful Rollback.  Mirror it in the
    /// chain store.
    pub fn on_block_rolled_back(&mut self, target: Point) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        if target == Point::Origin {
            self.last_validated_tip = None;
            info!(
                node_id = %self.node_id,
                "ledger rolled back to Origin, clearing chain store"
            );
            fx.push(PraosEffect::InjectRollback {
                target: Point::Origin,
            });
            return fx;
        }
        let hash = match &target {
            Point::Specific { hash, .. } => *hash,
            _ => return fx,
        };
        self.last_validated_tip = Some(hash);
        info!(
            node_id = %self.node_id,
            %target,
            "ledger rolled back, rolling chain store"
        );
        fx.push(PraosEffect::InjectRollback { target });
        fx
    }

    // -- Periodic retry -----------------------------------------------------

    /// Periodic slot-driven retry: evict stale in-flight fetches and
    /// re-run chain selection.  Bridges chain_tree gaps when needed.
    pub fn retry_select_chain(&mut self, now: Instant) -> Vec<PraosEffect> {
        let mut fx = Vec::new();
        let before = self.in_flight.len();
        self.evict_stale_in_flight(now);
        let evicted = before - self.in_flight.len();

        if let Some(best) = self.chain_tree.best_tip_hash() {
            self.try_switch_and_execute_internal(best, &mut fx);
        }
        if evicted > 0 || !self.in_flight.is_empty() {
            self.evaluate_and_fetch_internal(now, &mut fx);
        }
        // Bridge a chain_tree gap between best_tip and adopted, if any.
        if let Some(best) = self.chain_tree.best_tip_hash() {
            if let Err(Some(gap_point)) = self.try_switch_to(best) {
                let from = self
                    .adopted_tip_hash
                    .and_then(|h| self.chain_tree.point(&h).cloned())
                    .unwrap_or(Point::Origin);
                let from_slot = match &from {
                    Point::Specific { slot, .. } => *slot,
                    _ => 0,
                };
                let to_slot = match &gap_point {
                    Point::Specific { slot, .. } => *slot,
                    _ => 0,
                };
                if to_slot > from_slot && !self.in_flight.contains_key(&gap_point) {
                    info!(
                        node_id = %self.node_id,
                        %from,
                        to = %gap_point,
                        "retry: fetching gap to bridge chain_tree"
                    );
                    self.in_flight.insert(gap_point.clone(), now);
                    fx.push(PraosEffect::FetchBlockRange {
                        from,
                        to: gap_point,
                        peer_id: None,
                    });
                }
            }
        }
        fx
    }

    // -- Pure algorithm queries (also used by tests) ------------------------

    /// Walk backward from `start_hash` following `prev_hash` links,
    /// using `chain_tree` first and falling back to `block_cache` when
    /// a block is cached but not yet in chain_tree.
    pub fn walk_ancestors_hybrid(&self, start_hash: [u8; 32]) -> HybridWalk {
        let mut chain = vec![start_hash];
        let mut current = start_hash;
        let reached_origin;
        loop {
            let parent_opt = if self.chain_tree.block_number(&current).is_some() {
                self.chain_tree.prev_hash(&current)
            } else if let Some(cached) = self.block_cache.get(&current) {
                cached.prev_hash
            } else {
                reached_origin = false;
                break;
            };
            match parent_opt {
                None => {
                    reached_origin = true;
                    break;
                }
                Some(parent) => {
                    let in_tree = self.chain_tree.block_number(&parent).is_some();
                    let in_cache = self.block_cache.contains_key(&parent);
                    if !in_tree && !in_cache {
                        reached_origin = false;
                        break;
                    }
                    chain.push(parent);
                    current = parent;
                }
            }
        }
        HybridWalk {
            chain,
            reached_origin,
        }
    }

    /// One pass of Haskell-aligned chain selection.  Pure: does not
    /// mutate state.  Tests call this directly to assert classification.
    pub fn select_chain_once(&self, skip: &HashSet<PeerId>) -> SelectionDecision {
        let (adopted_hash, adopted_bn) = match self.adopted_tip_hash {
            Some(h) => (h, self.chain_tree.block_number(&h).unwrap_or(0)),
            None => ([0u8; 32], 0),
        };
        let best = self
            .peer_chains
            .iter()
            .filter(|(peer_id, _)| !skip.contains(peer_id))
            .filter_map(|(peer_id, chain)| {
                let tip = chain.tip()?;
                if self.adopted_tip_hash.is_none()
                    || is_better_tip(tip.block_no, &tip.hash, adopted_bn, &adopted_hash)
                {
                    Some((*peer_id, chain, tip.clone()))
                } else {
                    None
                }
            })
            .max_by(|a, b| {
                a.2.block_no
                    .cmp(&b.2.block_no)
                    .then_with(|| b.2.hash.cmp(&a.2.hash))
            });

        let (peer_id, candidate, candidate_tip) = match best {
            Some(b) => b,
            None => return SelectionDecision::NoBetterChain,
        };

        let adopted_ancestors: HashSet<[u8; 32]> = self
            .adopted_tip_hash
            .map(|h| self.chain_tree.ancestors(h).into_iter().collect())
            .unwrap_or_default();

        let mut replay_rev: Vec<&PeerChainEntry> = Vec::new();
        let mut ancestor: Option<[u8; 32]> = None;
        for entry in candidate.iter().rev() {
            if adopted_ancestors.contains(&entry.hash) {
                ancestor = Some(entry.hash);
                break;
            }
            replay_rev.push(entry);
        }
        if ancestor.is_none() {
            if let Some(oldest) = candidate.iter().next() {
                match oldest.prev_hash {
                    None => {
                        if self.adopted_tip_hash.is_none() {
                            ancestor = Some([0u8; 32]);
                        }
                    }
                    Some(parent) => {
                        // Two paths to accept the parent as ancestor:
                        // either it's already in the adopted chain's
                        // ancestry, or we have no adopted chain (fresh
                        // node) so any parent is acceptable.
                        if adopted_ancestors.contains(&parent)
                            || self.adopted_tip_hash.is_none()
                        {
                            ancestor = Some(parent);
                        }
                    }
                }
            }
        }
        if ancestor.is_none() {
            if let Some(anchor) = candidate.anchor() {
                if anchor.hash == [0u8; 32] && self.adopted_tip_hash.is_none() {
                    ancestor = Some([0u8; 32]);
                } else if adopted_ancestors.contains(&anchor.hash) {
                    ancestor = Some(anchor.hash);
                }
            }
        }
        let ancestor = match ancestor {
            Some(a) => a,
            None => {
                let hex_tail = |h: &[u8; 32]| format!("{:02x}{:02x}", h[30], h[31]);
                let hex_tail_opt = |h: &Option<[u8; 32]>| {
                    h.as_ref().map(hex_tail).unwrap_or_else(|| "<none>".into())
                };
                let oldest = candidate.iter().next();
                let newest = candidate.iter().next_back();
                let oldest_prev_in_ancestors = oldest
                    .and_then(|e| e.prev_hash)
                    .map(|p| adopted_ancestors.contains(&p))
                    .unwrap_or(false);
                info!(
                    node_id = %self.node_id,
                    %peer_id,
                    peer_tip_block_no = candidate_tip.block_no,
                    adopted_block_no = adopted_bn,
                    adopted_hash = hex_tail(&adopted_hash),
                    peer_chain_len = candidate.len(),
                    adopted_ancestors_len = adopted_ancestors.len(),
                    oldest_block_no = oldest.map(|e| e.block_no),
                    oldest_hash = oldest.map(|e| hex_tail(&e.hash)),
                    oldest_prev_hash = hex_tail_opt(&oldest.and_then(|e| e.prev_hash)),
                    oldest_prev_in_ancestors,
                    newest_block_no = newest.map(|e| e.block_no),
                    newest_hash = newest.map(|e| hex_tail(&e.hash)),
                    newest_prev_hash = hex_tail_opt(&newest.and_then(|e| e.prev_hash)),
                    "select_chain: orphan — no common ancestor found"
                );
                return SelectionDecision::OrphanCandidate {
                    peer_id,
                    tip_block_no: candidate_tip.block_no,
                };
            }
        };

        let replay: Vec<(Point, [u8; 32])> = replay_rev
            .into_iter()
            .rev()
            .map(|e| (e.point.clone(), e.hash))
            .collect();

        let missing: Vec<Point> = replay
            .iter()
            .filter(|(_, h)| !self.validated.contains(h) && !self.block_cache.contains_key(h))
            .map(|(p, _)| p.clone())
            .collect();

        let anchor_point = candidate.anchor().and_then(|a| {
            let oldest_prev = candidate.iter().next().and_then(|e| e.prev_hash);
            if a.hash == ancestor && oldest_prev != Some(ancestor) {
                Some(a.point.clone())
            } else {
                None
            }
        });

        if missing.is_empty() {
            let replay_hashes: Vec<[u8; 32]> = replay.iter().map(|(_, h)| *h).collect();
            if let Some(&last_hash) = replay_hashes.last() {
                let walk_result = self.walk_ancestors_hybrid(last_hash);
                let walk: HashSet<[u8; 32]> = walk_result.chain.iter().copied().collect();
                let all_on_chain = replay_hashes.iter().all(|h| walk.contains(h));
                if !all_on_chain {
                    tracing::debug!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no = candidate_tip.block_no,
                        replay_len = replay_hashes.len(),
                        "select_chain: non-contiguous replay (mixed forks); skipping peer"
                    );
                    return SelectionDecision::OrphanCandidate {
                        peer_id,
                        tip_block_no: candidate_tip.block_no,
                    };
                }
                let reaches_ancestor = if ancestor == [0u8; 32] {
                    walk_result.reached_origin
                } else {
                    walk.contains(&ancestor)
                };
                if !reaches_ancestor {
                    info!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no = candidate_tip.block_no,
                        ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                        "select_chain: fork mismatch (replay doesn't reach ancestor); skipping peer"
                    );
                    return SelectionDecision::OrphanCandidate {
                        peer_id,
                        tip_block_no: candidate_tip.block_no,
                    };
                }
            }
            SelectionDecision::Switched {
                peer_id,
                ancestor,
                replay: replay_hashes,
                tip_block_no: candidate_tip.block_no,
            }
        } else {
            SelectionDecision::WaitingForBlocks {
                peer_id,
                ancestor,
                anchor_point,
                missing,
                tip_block_no: candidate_tip.block_no,
            }
        }
    }

    /// Try to switch to a specific block as chain tip.  Walks back
    /// through chain_tree from `tip_hash` to `adopted_tip` and returns
    /// the contiguous prefix of cached blocks as a replay sequence.
    #[allow(clippy::type_complexity)]
    pub fn try_switch_to(
        &self,
        tip_hash: [u8; 32],
    ) -> Result<([u8; 32], Vec<[u8; 32]>), Option<Point>> {
        let adopted = self.adopted_tip_hash.unwrap_or([0u8; 32]);
        if tip_hash == adopted {
            return Err(None);
        }
        let tip_bn = match self.chain_tree.block_number(&tip_hash) {
            Some(bn) => bn,
            None => return Err(None),
        };
        let adopted_bn = self
            .adopted_tip_hash
            .and_then(|h| self.chain_tree.block_number(&h))
            .unwrap_or(0);
        if !is_better_tip(tip_bn, &tip_hash, adopted_bn, &adopted) {
            return Err(None);
        }
        let walk = self.chain_tree.ancestors(tip_hash);
        let adopted_ancestors: HashSet<[u8; 32]> = self
            .adopted_tip_hash
            .map(|h| self.chain_tree.ancestors(h).into_iter().collect())
            .unwrap_or_default();
        let ancestor_pos = walk
            .iter()
            .position(|h| *h == adopted || adopted_ancestors.contains(h));
        let ancestor_pos = match ancestor_pos {
            Some(p) => p,
            None if self.adopted_tip_hash.is_none() => match walk.last() {
                Some(h) if self.chain_tree.prev_hash(h).is_none() => walk.len(),
                _ => {
                    let gap_hash = walk.last().copied();
                    let gap_point = gap_hash.and_then(|h| self.chain_tree.point(&h).cloned());
                    return Err(gap_point);
                }
            },
            None => {
                let gap_hash = walk.last().copied();
                let gap_point = gap_hash.and_then(|h| self.chain_tree.point(&h).cloned());
                return Err(gap_point);
            }
        };
        let ancestor = if ancestor_pos < walk.len() {
            walk[ancestor_pos]
        } else {
            [0u8; 32]
        };
        let replay: Vec<[u8; 32]> = walk[..ancestor_pos].iter().rev().copied().collect();
        if replay.is_empty() {
            return Err(None);
        }
        let prefix: Vec<[u8; 32]> = replay
            .into_iter()
            .take_while(|h| {
                !self.in_flight_validation.contains(h)
                    && (self.validated.contains(h) || self.block_cache.contains_key(h))
            })
            .collect();
        if prefix.is_empty() {
            return Err(None);
        }
        Ok((ancestor, prefix))
    }

    // -- Internal effect-emitting helpers -----------------------------------

    fn evict_stale_in_flight(&mut self, now: Instant) {
        self.in_flight
            .retain(|_, started| now.duration_since(*started) < IN_FLIGHT_TTL);
    }

    fn evaluate_and_fetch_internal(&mut self, now: Instant, fx: &mut Vec<PraosEffect>) {
        let mut skip: HashSet<PeerId> = self
            .orphan_cooldown
            .iter()
            .filter(|(_, until)| **until > now)
            .map(|(p, _)| *p)
            .collect();
        self.orphan_cooldown.retain(|_, until| *until > now);

        loop {
            match self.select_chain_once(&skip) {
                SelectionDecision::NoBetterChain => return,
                SelectionDecision::OrphanCandidate {
                    peer_id,
                    tip_block_no,
                } => {
                    if let Some(chain) = self.peer_chains.get_mut(&peer_id) {
                        chain.clear_entries();
                    }
                    let already_cooling = self.orphan_cooldown.contains_key(&peer_id);
                    self.orphan_cooldown.insert(peer_id, now + ORPHAN_COOLDOWN);
                    skip.insert(peer_id);
                    if !already_cooling {
                        info!(
                            node_id = %self.node_id,
                            %peer_id,
                            tip_block_no,
                            "select_chain: orphan, clearing entries and requesting re-intersection"
                        );
                        fx.push(PraosEffect::ReIntersect { peer_id });
                    }
                    continue;
                }
                SelectionDecision::Switched {
                    peer_id,
                    ancestor,
                    replay,
                    tip_block_no,
                } => {
                    info!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no,
                        replay_len = replay.len(),
                        ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                        "select_chain: fork switch"
                    );
                    self.execute_switch_internal(ancestor, replay, fx);
                    return;
                }
                SelectionDecision::WaitingForBlocks {
                    peer_id,
                    ancestor,
                    anchor_point,
                    missing,
                    tip_block_no,
                    ..
                } => {
                    info!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no,
                        missing_len = missing.len(),
                        has_anchor_gap = anchor_point.is_some(),
                        ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                        "select_chain: fetching missing blocks"
                    );
                    let now2 = now;
                    self.issue_fetch_internal(missing, anchor_point, Some(peer_id), now2, fx);
                    return;
                }
            }
        }
    }

    fn try_switch_and_execute_internal(
        &mut self,
        tip_hash: [u8; 32],
        fx: &mut Vec<PraosEffect>,
    ) -> bool {
        if let Ok((ancestor, replay)) = self.try_switch_to(tip_hash) {
            info!(
                node_id = %self.node_id,
                replay_len = replay.len(),
                ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                "chain selection: switching to stored blocks"
            );
            self.execute_switch_internal(ancestor, replay, fx);
            true
        } else {
            false
        }
    }

    fn execute_switch_internal(
        &mut self,
        ancestor: [u8; 32],
        replay: Vec<[u8; 32]>,
        fx: &mut Vec<PraosEffect>,
    ) {
        let needs_rollback = ancestor != [0u8; 32] || self.adopted_tip_hash.is_some();
        if needs_rollback && self.queued_validator_tip != Some(ancestor) {
            if ancestor == [0u8; 32] {
                fx.push(PraosEffect::ValidatorRollback {
                    target: Point::Origin,
                });
                self.queued_validator_tip = None;
                self.adopted_tip_hash = None;
            } else {
                let ancestor_point = match self.chain_tree.point(&ancestor) {
                    Some(p) => p.clone(),
                    None => {
                        warn!(
                            node_id = %self.node_id,
                            ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                            "select_chain: ancestor point not in chain_tree; aborting switch"
                        );
                        return;
                    }
                };
                fx.push(PraosEffect::ValidatorRollback {
                    target: ancestor_point,
                });
                self.queued_validator_tip = Some(ancestor);
                self.adopted_tip_hash = Some(ancestor);
            }
        }
        for hash in replay {
            let (point, body, prev_hash) = match self.block_cache.get(&hash) {
                Some(cb) => (cb.point.clone(), cb.body.clone(), cb.prev_hash),
                None => {
                    warn!(
                        node_id = %self.node_id,
                        hash = format!("{:02x}{:02x}", hash[30], hash[31]),
                        "select_chain: replay block not in cache; aborting switch"
                    );
                    return;
                }
            };
            self.submit_for_validation_internal(point, body, prev_hash, fx);
        }
    }

    fn submit_for_validation_internal(
        &mut self,
        point: Point,
        body: Vec<u8>,
        prev_hash: Option<[u8; 32]>,
        fx: &mut Vec<PraosEffect>,
    ) {
        let new_hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        if prev_hash != self.queued_validator_tip {
            if let Some(parent_hash) = prev_hash {
                if let Some(parent_point) = self.chain_tree.point(&parent_hash).cloned() {
                    fx.push(PraosEffect::ValidatorRollback {
                        target: parent_point,
                    });
                    self.queued_validator_tip = Some(parent_hash);
                } else {
                    let hex = |h: &[u8; 32]| format!("{:02x}{:02x}", h[30], h[31]);
                    tracing::debug!(
                        node_id = %self.node_id,
                        parent = hex(&parent_hash),
                        queued_tip = self
                            .queued_validator_tip
                            .as_ref()
                            .map(|h| format!("{:02x}{:02x}", h[30], h[31]))
                            .as_deref()
                            .unwrap_or("<none>"),
                        block = format!("{}", point),
                        "parent not in chain_tree — skipping rollback"
                    );
                }
            }
        }
        fx.push(PraosEffect::ValidatorApply {
            point: point.clone(),
            body,
            prev_hash,
        });
        self.queued_validator_tip = Some(new_hash);
        self.adopted_tip_hash = Some(new_hash);
        self.in_flight_validation.insert(new_hash);
    }

    fn issue_fetch_internal(
        &mut self,
        missing: Vec<Point>,
        anchor_point: Option<Point>,
        peer_id: Option<PeerId>,
        now: Instant,
        fx: &mut Vec<PraosEffect>,
    ) {
        if missing.is_empty() {
            return;
        }
        self.evict_stale_in_flight(now);
        let from = anchor_point.unwrap_or_else(|| missing.first().unwrap().clone());
        let to = missing.last().unwrap().clone();
        if self.in_flight.contains_key(&to) {
            return;
        }
        self.in_flight.insert(to.clone(), now);
        info!(
            node_id = %self.node_id,
            %from,
            %to,
            "fetching missing chain blocks"
        );
        fx.push(PraosEffect::FetchBlockRange { from, to, peer_id });
    }
}

// ---------------------------------------------------------------------------
// Logical header info passed in by the I/O wrapper
// ---------------------------------------------------------------------------

/// Header metadata extracted from a wire-format header by the I/O
/// wrapper.  con-rs never parses headers itself.
#[derive(Debug, Clone)]
pub struct ParsedHeaderInfo {
    pub block_number: u64,
    pub slot: u64,
    pub prev_hash: Option<[u8; 32]>,
}
