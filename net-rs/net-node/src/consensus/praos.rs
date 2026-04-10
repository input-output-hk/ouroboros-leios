//! Praos longest-chain consensus with fork tracking.

use std::collections::{HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::peer::PeerId;
use net_core::types::{BlockBody, Point, Tip, WrappedHeader};
use tokio::sync::mpsc;
use tracing::info;

use crate::chain_tree::{is_better_tip, ChainTree, ChainTreeEntry};
use crate::validation::{LedgerCommand, LedgerOutcome, Validator};

/// How long an in-flight fetch entry remains "active" before being considered
/// stale and eligible for retry. The coordinator may silently drop a fetch
/// (e.g. no connected peer has the requested point in its fragment), so we
/// need a recovery path: if no body arrives within this window, allow a fresh
/// attempt.
const IN_FLIGHT_TTL: Duration = Duration::from_secs(15);

/// A block body cached after fetch or self-production.
struct CachedBlock {
    point: Point,
    header: WrappedHeader,
    body: BlockBody,
    block_no: u64,
    prev_hash: Option<[u8; 32]>,
}

/// One header in a per-peer candidate chain.
#[derive(Debug, Clone)]
pub(crate) struct PeerChainEntry {
    pub hash: [u8; 32],
    pub point: Point,
    pub block_no: u64,
    pub prev_hash: Option<[u8; 32]>,
}

/// Ordered list of headers a single peer has announced to us.
///
/// Mirrors the Haskell `AnchoredFragment Header`: the queue holds entries
/// from the oldest known header (anchor) to the peer's current tip, in
/// announcement order. `append` adds the new tip; `rollback_to` truncates
/// after a rollback point; the whole structure is dropped on peer disconnect.
///
/// Bounded at `cap` to avoid unbounded memory growth — when the queue would
/// exceed the cap, the oldest entries are dropped (effectively the anchor
/// slides forward). A proper Haskell-style immutable-point anchor is a
/// future refinement; for now the cap is a blunt safety rail.
///
/// # Maintained invariants
///
/// - **Bounded size**: `len() <= cap` after every `append()`.
/// - **No duplicate hashes**: `append()` scans for existing hash (O(n)).
/// - **Announcement order**: entries are push_back in ChainSync order.
/// - **Conservative rollback**: unknown points in `rollback_to()` are no-ops.
///
/// # Known gaps
///
/// - **No contiguity enforcement**: nothing checks that
///   `entries[i+1].prev_hash == entries[i].hash`. If ChainSync skips
///   headers, the chain can have logical gaps.
/// - **Sliding window loses anchor**: when oldest entries are evicted on
///   cap overflow, the only link to the pre-window chain is
///   `oldest().prev_hash`. The explicit `anchor` field (set from the
///   ChainSync intersection) provides a fallback — `select_chain_once`
///   can use it as a guaranteed common ancestor even when the entry
///   window is too narrow.
#[derive(Debug)]
pub(crate) struct PeerChain {
    entries: VecDeque<PeerChainEntry>,
    cap: usize,
    /// The ChainSync intersection point — a guaranteed common ancestor
    /// between the local chain and this peer's chain. Set when
    /// `IntersectionFound` arrives, persists through rollbacks, replaced
    /// on reconnect (new intersection), dropped on disconnect.
    anchor: Option<PeerChainAnchor>,
}

/// The ChainSync intersection point stored as a peer chain anchor.
#[derive(Debug, Clone)]
pub(crate) struct PeerChainAnchor {
    pub hash: [u8; 32],
    pub point: Point,
}

impl PeerChain {
    pub fn new(cap: usize) -> Self {
        Self {
            entries: VecDeque::new(),
            cap,
            anchor: None,
        }
    }

    /// Set the anchor (ChainSync intersection point).
    pub fn set_anchor(&mut self, point: Point) {
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            Point::Origin => [0u8; 32],
        };
        self.anchor = Some(PeerChainAnchor { hash, point });
    }

    /// The anchor (ChainSync intersection), if set.
    pub fn anchor(&self) -> Option<&PeerChainAnchor> {
        self.anchor.as_ref()
    }

    /// Append a new header. If the queue would exceed `cap`, drop oldest.
    /// Idempotent on the same hash — a duplicate announcement is a no-op.
    pub fn append(&mut self, entry: PeerChainEntry) {
        if self.entries.iter().any(|e| e.hash == entry.hash) {
            return;
        }
        self.entries.push_back(entry);
        while self.entries.len() > self.cap {
            self.entries.pop_front();
        }
    }

    /// Truncate the chain to the given point (inclusive). If the point
    /// matches the anchor (ChainSync intersection), clear all entries —
    /// the rollback goes before any announced header. If the point is
    /// not in entries and doesn't match the anchor, leave unchanged.
    pub fn rollback_to(&mut self, point: &Point) {
        if let Some(pos) = self.entries.iter().position(|e| &e.point == point) {
            self.entries.truncate(pos + 1);
        } else if self.anchor.as_ref().is_some_and(|a| &a.point == point) {
            // Rolling back to the intersection — everything after it
            // is from a fork the peer abandoned.
            self.entries.clear();
        }
    }

    /// Clear all entries but preserve the anchor. Used when requesting
    /// re-intersection — stale entries are discarded and ChainSync will
    /// re-fill from the new intersection point.
    pub fn clear_entries(&mut self) {
        self.entries.clear();
    }

    /// Last entry in the chain (the peer's current tip), if any.
    pub fn tip(&self) -> Option<&PeerChainEntry> {
        self.entries.back()
    }

    /// Number of entries currently held.
    #[allow(dead_code)] // used in tests
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Iterate entries from oldest to newest.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &PeerChainEntry> {
        self.entries.iter()
    }
}

/// Result of a single pass of the Haskell-aligned chain selection.
#[derive(Debug, Clone)]
pub(crate) enum SelectionDecision {
    /// No peer has a chain strictly better than the adopted tip.
    NoBetterChain,
    /// A peer has a better tip but its chain doesn't connect to the
    /// adopted chain within the visibility window — the peer has
    /// forked beyond k or we haven't seen enough of its history yet.
    OrphanCandidate { peer_id: PeerId, tip_block_no: u64 },
    /// A peer has a better tip and all blocks from the common ancestor
    /// to its tip are already validated — a fork switch can happen
    /// immediately. `replay` is the sequence of block hashes from the
    /// ancestor exclusive to the peer's tip inclusive, in oldest→newest
    /// order.
    Switched {
        peer_id: PeerId,
        ancestor: [u8; 32],
        replay: Vec<[u8; 32]>,
        tip_block_no: u64,
    },
    /// A peer has a better tip but some blocks between the common
    /// ancestor and its tip haven't been fetched + validated yet.
    /// `missing` carries their points in oldest→newest order so the
    /// driver can issue a contiguous `FetchBlockRange`.
    ///
    /// `anchor_point` is set when the ancestor came from the peer chain's
    /// anchor (ChainSync intersection) rather than from a direct hash
    /// match. When set, `issue_fetch` uses it as the range start to
    /// fill the gap between the anchor and the oldest PeerChain entry.
    WaitingForBlocks {
        peer_id: PeerId,
        ancestor: [u8; 32],
        anchor_point: Option<Point>,
        missing: Vec<Point>,
        tip_block_no: u64,
    },
}

/// PraosConsensus state with fork-tracking chain tree.
pub struct PraosConsensus {
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
    /// Each entry remembers when it was added; entries older than
    /// `IN_FLIGHT_TTL` are treated as stale and dropped lazily so a retry
    /// can be issued. The coordinator may silently drop a fetch when no
    /// connected peer has the requested point — without TTL recovery, the
    /// node would stay stuck on that fork forever.
    in_flight: HashMap<Point, Instant>,
    /// Per-peer candidate chains. Populated on `TipAdvanced`, truncated on
    /// `RolledBack`, dropped on `PeerDisconnected`. Drives chain selection
    /// via `select_chain`.
    pub(crate) peer_chains: HashMap<PeerId, PeerChain>,
    /// Hash the validator's queue will be at after every command we've
    /// already submitted has been processed. We track this so a fork
    /// switch can decide whether to insert a `LedgerCommand::Rollback`
    /// before the next `Apply`. The actual ledger state lags this until
    /// outcomes arrive.
    queued_validator_tip: Option<[u8; 32]>,
    /// Hash of the last block the validator has actually `Applied`. Used
    /// to rewind `queued_validator_tip` after an `ApplyFailed`, since the
    /// failed block (and any cascading failures behind it) leave the
    /// queue's projected tip out of sync with reality.
    last_validated_tip: Option<[u8; 32]>,
    /// Hashes that have been submitted to the validator but whose
    /// outcome (`Applied` or `ApplyFailed`) hasn't arrived yet. Used to
    /// gate new submissions on "parent known to the validator" without
    /// requiring the parent's apply to have already completed: since
    /// the actor processes commands sequentially, if the parent's Apply
    /// is already queued, submitting the child right after is safe.
    in_flight_validation: HashSet<[u8; 32]>,
    commands: mpsc::Sender<NetworkCommand>,
    validator: Validator,
    /// Security parameter k — prune blocks deeper than this.
    security_param_k: u64,
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
    fn peer_chain_cap(&self) -> usize {
        (self.security_param_k as usize).saturating_mul(2).max(64)
    }

    /// Ingest a peer's new header announcement into its candidate chain.
    fn record_peer_tip(&mut self, peer_id: PeerId, tip: &Tip, header: &WrappedHeader) {
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
    fn record_peer_intersection(&mut self, peer_id: PeerId, point: &Point) {
        let cap = self.peer_chain_cap();
        self.peer_chains
            .entry(peer_id)
            .or_insert_with(|| PeerChain::new(cap))
            .set_anchor(point.clone());
    }

    /// Truncate a peer's candidate chain on a rollback.
    fn record_peer_rollback(&mut self, peer_id: PeerId, point: &Point) {
        if let Some(chain) = self.peer_chains.get_mut(&peer_id) {
            chain.rollback_to(point);
        }
    }

    /// Drop a peer's candidate chain on disconnect.
    fn record_peer_disconnected(&mut self, peer_id: PeerId) {
        self.peer_chains.remove(&peer_id);
    }

    /// One pass of Haskell-aligned chain selection: pick the best peer
    /// chain whose tip is strictly better than the adopted tip (and not
    /// already tried this pass), walk it backward to find the common
    /// ancestor with the adopted chain, and classify the result (orphan,
    /// switch-ready, or waiting for blocks).
    ///
    /// This is pure — it does not mutate state. The async driver
    /// `select_chain` consumes its output.
    ///
    /// # Cross-structure dependencies
    ///
    /// Correctness depends on invariants spanning multiple structures:
    ///
    /// 1. **`adopted_ancestors` completeness requires `ChainTree` contiguity.**
    ///    `chain_tree.ancestors(adopted_hash)` returns only the connected
    ///    prefix — if there's a gap (intermediate block never inserted into
    ///    `chain_tree`), the ancestry is truncated. Peer chain entries whose
    ///    common ancestor falls beyond the gap will never match, causing
    ///    false `OrphanCandidate` classification.
    ///
    /// 2. **`PeerChain` must overlap with `adopted_ancestors`.** The walk
    ///    finds a common ancestor only if some entry in the peer chain has
    ///    a hash that appears in `adopted_ancestors`. If the peer chain's
    ///    sliding window (bounded by `cap`) has evicted the overlapping
    ///    region, or if `adopted_ancestors` is truncated by a gap, no
    ///    ancestor is found.
    ///
    /// 3. **Origin fallback is fresh-node only.** When
    ///    `oldest.prev_hash` is `None` (peer chain contains genesis
    ///    child), Origin is accepted as ancestor only when
    ///    `adopted_tip_hash` is `None` (fresh node). An adopted node
    ///    seeing `prev_hash=None` means stale PeerChain entries from
    ///    block 1 survived a rollback — the re-intersect mechanism
    ///    handles this via `OrphanCandidate`.
    fn select_chain_once(&self, skip: &HashSet<PeerId>) -> SelectionDecision {
        // Pick the best peer candidate: strictly better tip, ties broken by lower hash.
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

        // Compute the adopted chain's ancestry (bounded by k). This is
        // the set of hashes a rollback can legitimately target.
        let adopted_ancestors: HashSet<[u8; 32]> = self
            .adopted_tip_hash
            .map(|h| self.chain_tree.ancestors(h).into_iter().collect())
            .unwrap_or_default();

        // Walk the peer chain newest→oldest. Any entry NOT in the adopted
        // ancestry belongs to the replay chain; the first entry that IS
        // in the adopted ancestry is the common ancestor.
        let mut replay_rev: Vec<&PeerChainEntry> = Vec::new();
        let mut ancestor: Option<[u8; 32]> = None;
        for entry in candidate.iter().rev() {
            if adopted_ancestors.contains(&entry.hash) {
                ancestor = Some(entry.hash);
                break;
            }
            replay_rev.push(entry);
        }
        // Fallback: if we walked off the end of the peer chain without hitting
        // the adopted chain, check the oldest entry's prev_hash — it may point
        // directly at the intersection block.
        if ancestor.is_none() {
            if let Some(oldest) = candidate.iter().next() {
                match oldest.prev_hash {
                    None => {
                        // Peer's oldest entry has no parent (genesis child).
                        // Only accept Origin as ancestor for a fresh node
                        // with no adopted chain. An adopted node seeing
                        // prev_hash=None means stale PeerChain entries from
                        // block 1 survived a rollback — not a genuine
                        // genesis-diverged fork. The re-intersect mechanism
                        // handles stale state via OrphanCandidate.
                        if self.adopted_tip_hash.is_none() {
                            ancestor = Some([0u8; 32]);
                        }
                    }
                    Some(parent) => {
                        if adopted_ancestors.contains(&parent) {
                            ancestor = Some(parent);
                        } else if self.adopted_tip_hash.is_none() {
                            // No adopted chain at all — accept any parent.
                            ancestor = Some(parent);
                        }
                    }
                }
            }
        }
        // Anchor fallback: the ChainSync intersection is a guaranteed
        // common ancestor. Use it when the walk through entries and the
        // prev_hash fallback both failed (e.g., peer chain window too
        // narrow after reconnection).
        if ancestor.is_none() {
            if let Some(anchor) = candidate.anchor() {
                if anchor.hash == [0u8; 32] && self.adopted_tip_hash.is_none() {
                    // Origin anchor only for fresh nodes.
                    ancestor = Some([0u8; 32]);
                } else if adopted_ancestors.contains(&anchor.hash) {
                    ancestor = Some(anchor.hash);
                }
            }
        }
        let ancestor = match ancestor {
            Some(a) => a,
            None => {
                // Diagnostic: common-ancestor walk failed. Dump enough state
                // to distinguish (a) peer_chain window too short to reach our
                // ancestry from (b) stale entries from an abandoned fork.
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
                tracing::info!(
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

        // Oldest→newest replay order.
        let replay: Vec<(Point, [u8; 32])> = replay_rev
            .into_iter()
            .rev()
            .map(|e| (e.point.clone(), e.hash))
            .collect();

        // Which replay blocks lack a validated body?
        let missing: Vec<Point> = replay
            .iter()
            .filter(|(_, h)| !self.validated.contains(h) && !self.block_cache.contains_key(h))
            .map(|(p, _)| p.clone())
            .collect();

        // Detect gap between anchor and oldest PeerChain entry. When
        // the anchor was used as the common ancestor, the PeerChain
        // window may not start right after the anchor — there could be
        // blocks between the anchor and the oldest entry that need
        // fetching. Record the anchor point so issue_fetch can request
        // the full range.
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
            // Verify chain_tree contiguity before switching. Walk
            // backward from the LAST replay block and check:
            //   (a) every replay hash lies on that chain
            //   (b) the chain reaches the common ancestor (or genesis)
            //
            // Two distinct failure modes:
            //   1. !all_on_chain: PeerChain entries span multiple forks
            //      (stale entries survived a failed rollback). Fetching
            //      can't fix this — skip the peer so re-intersect can
            //      clean up the stale state.
            //   2. !reaches_ancestor: genuine gap between ancestor and
            //      first replay block (unfetched blocks). Fetchable.
            if let Some(&last_hash) = replay_hashes.last() {
                let walk_vec = self.chain_tree.ancestors(last_hash);
                let walk: HashSet<[u8; 32]> = walk_vec.iter().copied().collect();
                let all_on_chain = replay_hashes.iter().all(|h| walk.contains(h));

                if !all_on_chain {
                    // Replay entries from mixed forks — skip this peer.
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
                    // Genesis: the walk must reach a block whose
                    // prev_hash is None (the genesis child).
                    walk_vec
                        .last()
                        .is_some_and(|h| self.chain_tree.prev_hash(h).is_none())
                } else {
                    walk.contains(&ancestor)
                };

                if !reaches_ancestor {
                    // All replay blocks have bodies but the chain_tree
                    // walk doesn't reach the ancestor — the replay
                    // goes through a different fork. This happens when
                    // the PeerChain has stale entries from an old fork
                    // mixed with new fork entries.
                    tracing::info!(
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

    /// Find the longest switchable chain using only stored blocks.
    /// Walks back from chain_tree's best tip to the adopted tip and
    /// returns the contiguous cached prefix as a replay sequence.
    /// Finds chains from ANY source — blocks from multiple peers that
    /// form a contiguous path through chain_tree.
    fn try_stored_switch(&self) -> Option<([u8; 32], Vec<[u8; 32]>)> {
        let best_hash = self.chain_tree.best_tip_hash()?;
        let adopted = self.adopted_tip_hash.unwrap_or([0u8; 32]);
        if best_hash == adopted {
            return None;
        }

        let walk = self.chain_tree.ancestors(best_hash);
        let adopted_pos = walk.iter().position(|h| *h == adopted)?;

        // Blocks from adopted (exclusive) to best_tip (inclusive), oldest first.
        let replay: Vec<[u8; 32]> = walk[..adopted_pos].iter().rev().copied().collect();
        if replay.is_empty() {
            return None;
        }

        // Longest contiguous prefix where we have the block body and
        // it isn't already queued to the validator.
        let prefix: Vec<[u8; 32]> = replay
            .into_iter()
            .take_while(|h| {
                !self.in_flight_validation.contains(h)
                    && (self.validated.contains(h) || self.block_cache.contains_key(h))
            })
            .collect();

        if prefix.is_empty() {
            return None;
        }
        Some((adopted, prefix))
    }

    /// Drive chain selection to completion. First tries switching using
    /// stored blocks (chain_tree walk), then falls through to peer-chain
    /// based selection for fetching decisions.
    async fn select_chain(&mut self) {
        // Try switching using blocks we already have, regardless of
        // which peer announced them.
        if let Some((ancestor, replay)) = self.try_stored_switch() {
            info!(
                node_id = %self.node_id,
                replay_len = replay.len(),
                ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                "select_chain: stored-block switch"
            );
            self.execute_switch(ancestor, replay).await;
            return;
        }

        let mut tried: HashSet<PeerId> = HashSet::new();
        loop {
            match self.select_chain_once(&tried) {
                SelectionDecision::NoBetterChain => return,
                SelectionDecision::OrphanCandidate {
                    peer_id,
                    tip_block_no,
                } => {
                    // Clear stale entries and request re-intersection.
                    // Stale entries (from an old fork mixed with new
                    // announcements) cause persistent fork mismatches
                    // in the contiguity guard. Clearing forces ChainSync
                    // to rebuild from a fresh intersection.
                    if let Some(chain) = self.peer_chains.get_mut(&peer_id) {
                        chain.clear_entries();
                    }
                    info!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no,
                        "select_chain: orphan, clearing entries and requesting re-intersection"
                    );
                    let _ = self
                        .commands
                        .send(NetworkCommand::ReIntersect { peer_id })
                        .await;
                    tried.insert(peer_id);
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
                    self.execute_switch(ancestor, replay).await;
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
                    self.issue_fetch(missing, anchor_point, Some(peer_id)).await;
                    return;
                }
            }
        }
    }

    /// Execute a fork switch decided by `select_chain`: enqueue a
    /// `Rollback` to `ancestor` (if needed) followed by an `Apply` for
    /// each block in `replay` (oldest→newest). The validator processes
    /// the sequence in order, and `RolledBack`/`Applied` outcomes drive
    /// the chain_store updates and `adopted_tip_hash` advancement.
    async fn execute_switch(&mut self, ancestor: [u8; 32], replay: Vec<[u8; 32]>) {
        // Fresh node starting from synthetic genesis: no rollback to
        // issue, just apply forward.
        let needs_rollback = ancestor != [0u8; 32] || self.adopted_tip_hash.is_some();

        if needs_rollback && self.queued_validator_tip != Some(ancestor) {
            if ancestor == [0u8; 32] {
                // Origin rollback: the peer chain starts at genesis and
                // shares no blocks with our adopted chain. Roll back to
                // genesis and reset to fresh-node state so the first
                // replay block (prev_hash=None) aligns correctly in
                // submit_for_validation.
                self.validator
                    .submit(LedgerCommand::Rollback {
                        target: Point::Origin,
                    })
                    .await;
                self.queued_validator_tip = None;
                self.adopted_tip_hash = None;
            } else {
                let ancestor_point = match self.chain_tree.point(&ancestor) {
                    Some(p) => p.clone(),
                    None => {
                        tracing::warn!(
                            node_id = %self.node_id,
                            ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                            "select_chain: ancestor point not in chain_tree; aborting switch"
                        );
                        return;
                    }
                };
                self.validator
                    .submit(LedgerCommand::Rollback {
                        target: ancestor_point,
                    })
                    .await;
                self.queued_validator_tip = Some(ancestor);
                self.adopted_tip_hash = Some(ancestor);
            }
        }

        // Submit each replay block. submit_for_validation updates
        // queued_validator_tip on each call so we don't insert
        // redundant Rollbacks.
        for hash in replay {
            let (point, body, prev_hash) = match self.block_cache.get(&hash) {
                Some(cb) => (cb.point.clone(), cb.body.clone(), cb.prev_hash),
                None => {
                    tracing::warn!(
                        node_id = %self.node_id,
                        hash = format!("{:02x}{:02x}", hash[30], hash[31]),
                        "select_chain: replay block not in cache; aborting switch"
                    );
                    return;
                }
            };
            self.submit_for_validation(point, body, prev_hash).await;
        }
    }

    /// Issue a `FetchBlockRange` covering the missing replay blocks,
    /// skipping blocks already in flight.
    ///
    /// When `anchor_point` is set, the range starts from the anchor
    /// (ChainSync intersection) instead of the first missing entry.
    /// This fills the gap between the anchor and the oldest PeerChain
    /// entry — blocks that aren't in the PeerChain but are needed for
    /// the chain to be contiguous from the common ancestor to the tip.
    async fn issue_fetch(
        &mut self,
        missing: Vec<Point>,
        anchor_point: Option<Point>,
        peer_id: Option<PeerId>,
    ) {
        if missing.is_empty() {
            return;
        }
        self.evict_stale_in_flight();

        // Single range from oldest to newest missing block. When the
        // anchor provided the common ancestor and there's a gap, use
        // the anchor as `from` so BlockFetch fills the gap.
        let from = anchor_point.unwrap_or_else(|| missing.first().unwrap().clone());
        let to = missing.last().unwrap().clone();
        if self.in_flight.contains_key(&to) {
            return;
        }
        self.mark_in_flight(to.clone());
        info!(
            node_id = %self.node_id,
            %from,
            %to,
            "fetching missing chain blocks"
        );
        let _ = self
            .commands
            .send(NetworkCommand::FetchBlockRange { from, to, peer_id })
            .await;
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
                self.select_chain().await;
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
        self.select_chain().await;
    }

    /// Drop stale `in_flight` entries (older than `IN_FLIGHT_TTL`). Called
    /// at the start of fetch-issuing flows so a silently-dropped fetch can
    /// be retried.
    fn evict_stale_in_flight(&mut self) {
        let now = Instant::now();
        self.in_flight
            .retain(|_, started| now.duration_since(*started) < IN_FLIGHT_TTL);
    }

    fn mark_in_flight(&mut self, point: Point) {
        self.in_flight.insert(point, Instant::now());
    }

    /// Periodic retry: evict stale in-flight entries and re-run chain
    /// selection. Called from the slot tick in the main loop to ensure
    /// lagging nodes retry fetches even when no new network events arrive
    /// (e.g., after block production stops).
    pub async fn retry_select_chain(&mut self) {
        let before = self.in_flight.len();
        self.evict_stale_in_flight();
        let evicted = before - self.in_flight.len();
        if evicted > 0 || !self.in_flight.is_empty() {
            self.select_chain().await;
        }
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
                self.select_chain().await;
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
                self.select_chain().await;
                true
            }
            NetworkEvent::PeerDisconnected { peer_id, .. } => {
                self.record_peer_disconnected(*peer_id);
                self.select_chain().await;
                // Don't consume the event — the upstream log handler
                // still wants to see it.
                false
            }
            NetworkEvent::BlockFetchFailed { from, to } => {
                // Clear both endpoints' in_flight entries so select_chain
                // can reissue. The per-peer chains are the source of
                // truth for what's still reachable — if no peer still
                // claims these blocks, select_chain will pick a
                // different candidate next pass.
                self.in_flight.remove(from);
                self.in_flight.remove(to);
                info!(
                    node_id = %self.node_id,
                    from = %from,
                    to = %to,
                    "block fetch failed; re-evaluating chain selection"
                );
                self.select_chain().await;
                true
            }

            _ => false,
        }
    }

    /// Handle one outcome from the validator actor.
    ///
    /// Returns `true` if the chain_store rolled back as a result (so the
    /// telemetry layer can record the rollback event).
    pub async fn on_validation_outcome(&mut self, outcome: LedgerOutcome) -> bool {
        match outcome {
            LedgerOutcome::Applied { point } => {
                self.handle_applied(point).await;
                false
            }
            LedgerOutcome::RolledBack { target } => {
                self.handle_rolled_back(target).await;
                true
            }
            LedgerOutcome::ApplyFailed { point, error } => {
                self.handle_apply_failed(point, error);
                false
            }
            LedgerOutcome::RollbackFailed { target, error } => {
                tracing::error!(
                    node_id = %self.node_id,
                    %target,
                    %error,
                    "ledger rollback failed; consensus state may be inconsistent"
                );
                false
            }
        }
    }

    /// Apply succeeded: publish the block to the chain_store, update the
    /// last-validated tip, prune below k, and re-run `select_chain` so any
    /// peer chain that became actionable while we were validating gets
    /// picked up.
    async fn handle_applied(&mut self, point: Point) {
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        self.in_flight.remove(&point);
        self.in_flight_validation.remove(&hash);

        let inject = match self.block_cache.get(&hash) {
            Some(cb) => NetworkCommand::InjectBlock {
                point: cb.point.clone(),
                header: Box::new(cb.header.clone()),
                body: cb.body.clone(),
                block_no: cb.block_no,
            },
            None => {
                tracing::warn!(
                    node_id = %self.node_id,
                    %point,
                    "applied outcome for block not in cache — ignoring"
                );
                return;
            }
        };
        self.validated.insert(hash);
        self.last_validated_tip = Some(hash);

        info!(
            node_id = %self.node_id,
            %point,
            "block validated, publishing to chain store"
        );
        let _ = self.commands.send(inject).await;

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

        // A newly-validated block can unblock a fork switch we couldn't
        // execute earlier (e.g. waiting for the last replay block).
        self.select_chain().await;
    }

    /// Rollback succeeded: the ledger is now back at `target`, so the
    /// chain store should mirror that.
    async fn handle_rolled_back(&mut self, target: Point) {
        if target == Point::Origin {
            self.last_validated_tip = None;
            info!(
                node_id = %self.node_id,
                "ledger rolled back to Origin, clearing chain store"
            );
            let _ = self
                .commands
                .send(NetworkCommand::InjectRollback {
                    point: Point::Origin,
                })
                .await;
            return;
        }
        let hash = match &target {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        self.last_validated_tip = Some(hash);
        info!(
            node_id = %self.node_id,
            %target,
            "ledger rolled back, rolling chain store"
        );
        let _ = self
            .commands
            .send(NetworkCommand::InjectRollback { point: target })
            .await;
    }

    /// Apply failed: the block (and any cascade behind it) is no longer
    /// in the validator's accepted state. Rewind `queued_validator_tip`
    /// and `adopted_tip_hash` so the next submission realigns with what
    /// the ledger has actually accepted, and drop any children waiting
    /// on the failed block.
    fn handle_apply_failed(&mut self, point: Point, error: String) {
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        self.in_flight.remove(&point);
        self.in_flight_validation.remove(&hash);
        tracing::warn!(
            node_id = %self.node_id,
            %point,
            %error,
            "ledger apply failed; rewinding to last validated tip"
        );
        // The queue is no longer aimed at the failed block. Rewind to
        // whatever the last successfully-applied tip was; subsequent
        // submissions will issue a Rollback if needed to realign.
        self.queued_validator_tip = self.last_validated_tip;
        self.adopted_tip_hash = self.last_validated_tip;
        // The failed block stays in the cache but is no longer marked
        // validated. select_chain may pick a different candidate.
        self.validated.remove(&hash);
    }

    /// Submit a block for validation. Issues a `LedgerCommand::Apply`,
    /// preceded by a `Rollback` if the validator queue isn't currently
    /// aimed at the block's parent. Updates `queued_validator_tip` and
    /// `adopted_tip_hash` eagerly so subsequent decisions see the
    /// post-submission view.
    async fn submit_for_validation(
        &mut self,
        point: Point,
        body: BlockBody,
        prev_hash: Option<[u8; 32]>,
    ) {
        let new_hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };

        // If the validator queue isn't currently aimed at this block's
        // parent, queue a Rollback first so the ledger ends up in the
        // right state for the apply.
        if prev_hash != self.queued_validator_tip {
            if let Some(parent_hash) = prev_hash {
                if let Some(parent_point) = self.chain_tree.point(&parent_hash).cloned() {
                    self.validator
                        .submit(LedgerCommand::Rollback {
                            target: parent_point,
                        })
                        .await;
                    self.queued_validator_tip = Some(parent_hash);
                } else {
                    let hex = |h: &[u8; 32]| format!("{:02x}{:02x}", h[30], h[31]);
                    tracing::debug!(
                        node_id = %self.node_id,
                        parent = hex(&parent_hash),
                        queued_tip = self.queued_validator_tip.as_ref().map(|h| format!("{:02x}{:02x}", h[30], h[31])).as_deref().unwrap_or("<none>"),
                        block = format!("{}", point),
                        "parent not in chain_tree — skipping rollback"
                    );
                }
            }
        }

        self.validator
            .submit(LedgerCommand::Apply {
                point: point.clone(),
                body,
            })
            .await;
        self.queued_validator_tip = Some(new_hash);
        self.adopted_tip_hash = Some(new_hash);
        self.in_flight_validation.insert(new_hash);
    }

    /// A fetched block arrived — cache it and run chain selection.
    /// Validation is driven by `select_chain` -> `execute_switch`.
    async fn on_block_received(&mut self, point: &Point, body: &BlockBody) {
        let hash = match point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        // Dedup: skip if already known to the validator or waiting on
        // its parent. `block_cache` covers the "already cached" case;
        // the other checks are belt-and-braces.
        if self.block_cache.contains_key(&hash)
            || self.validated.contains(&hash)
            || self.in_flight_validation.contains(&hash)
        {
            return;
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
        // Insert into chain_tree so ancestors() can walk through fetched
        // blocks — critical for the adopted-chain ancestry lookup in
        // select_chain.
        if let Some(info) = header.parsed.as_ref() {
            self.chain_tree.insert(
                hash,
                point.clone(),
                info.block_number,
                info.slot,
                info.prev_hash,
            );
        } else if block_no > 0 {
            // Opaque header — insert with fallback metadata to avoid gaps
            // in chain_tree that break ancestors() walks. block_no and
            // prev_hash were derived from chain_tree lookups above; guard
            // block_no > 0 to avoid inserting with the default which would
            // confuse pruning and best_tip selection.
            let slot = match point {
                Point::Specific { slot, .. } => *slot,
                _ => 0,
            };
            self.chain_tree
                .insert(hash, point.clone(), block_no, slot, prev_hash);
        }
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
            block_no,
            "block received and cached"
        );
        self.select_chain().await;
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
    use super::*;
    use net_core::peer::PeerId;

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

    #[test]
    fn peer_chain_rollback_to_anchor_clears_entries() {
        let mut chain = PeerChain::new(64);
        let anchor_point = Point::Specific {
            slot: 5,
            hash: [5; 32],
        };
        chain.set_anchor(anchor_point.clone());

        // Add entries after the anchor.
        for i in 6..=10 {
            chain.append(PeerChainEntry {
                hash: [i; 32],
                point: Point::Specific {
                    slot: i as u64,
                    hash: [i; 32],
                },
                block_no: i as u64,
                prev_hash: Some([(i - 1); 32]),
            });
        }
        assert_eq!(chain.len(), 5);

        // Rolling back to the anchor should clear all entries.
        chain.rollback_to(&anchor_point);
        assert_eq!(chain.len(), 0);
        // Anchor preserved.
        assert!(chain.anchor().is_some());
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
