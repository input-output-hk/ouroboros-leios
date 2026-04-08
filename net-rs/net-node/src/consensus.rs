//! Longest-chain consensus with fork tracking.

use std::collections::{HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::peer::PeerId;
use net_core::types::{BlockBody, Point, Tip, WrappedHeader};
use tokio::sync::mpsc;
use tracing::info;

use crate::chain_tree::{is_better_tip, ChainTree, ChainTreeEntry};
use crate::validation::{ValidationComplete, Validator};

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
#[derive(Debug)]
pub(crate) struct PeerChain {
    entries: VecDeque<PeerChainEntry>,
    cap: usize,
}

impl PeerChain {
    pub fn new(cap: usize) -> Self {
        Self {
            entries: VecDeque::new(),
            cap,
        }
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
    /// is not in the chain, leave it unchanged — we can't rewrite history
    /// we never knew.
    pub fn rollback_to(&mut self, point: &Point) {
        if let Some(pos) = self.entries.iter().position(|e| &e.point == point) {
            self.entries.truncate(pos + 1);
        }
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
    WaitingForBlocks {
        peer_id: PeerId,
        ancestor: [u8; 32],
        missing: Vec<Point>,
        tip_block_no: u64,
    },
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
            in_flight: HashMap::new(),
            peer_chains: HashMap::new(),
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
                        // Peer's chain roots at genesis. Only usable as an
                        // ancestor when we have no adopted tip yet — we can't
                        // rewind an adopted chain to "before genesis".
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
        let ancestor = match ancestor {
            Some(a) => a,
            None => {
                return SelectionDecision::OrphanCandidate {
                    peer_id,
                    tip_block_no: candidate_tip.block_no,
                }
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
            .filter(|(_, h)| !self.validated.contains(h))
            .map(|(p, _)| p.clone())
            .collect();

        if missing.is_empty() {
            let replay_hashes: Vec<[u8; 32]> = replay.into_iter().map(|(_, h)| h).collect();
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
                missing,
                tip_block_no: candidate_tip.block_no,
            }
        }
    }

    /// Drive chain selection to completion. Repeatedly calls
    /// `select_chain_once` and executes its decision. An
    /// `OrphanCandidate` skips that peer and tries the next best.
    /// A `Switched` performs the rollback+replay. A `WaitingForBlocks`
    /// issues a range fetch for the missing blocks. `NoBetterChain`
    /// terminates.
    ///
    /// Orphan peers are skipped within this pass via a `tried` set —
    /// the peer's `PeerChain` is NOT mutated. Dropping the chain would
    /// lose all historical announcements; the peer chain is the only
    /// place they're kept, and ChainSync won't re-stream blocks the
    /// peer already acknowledged. If the peer keeps extending, future
    /// `TipAdvanced` events will accumulate enough history for the
    /// walk to eventually find a common ancestor.
    async fn select_chain(&mut self) {
        let mut tried: HashSet<PeerId> = HashSet::new();
        loop {
            match self.select_chain_once(&tried) {
                SelectionDecision::NoBetterChain => return,
                SelectionDecision::OrphanCandidate {
                    peer_id,
                    tip_block_no,
                } => {
                    tracing::debug!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no,
                        "select_chain: skipping orphan candidate"
                    );
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
                    missing,
                    tip_block_no,
                } => {
                    info!(
                        node_id = %self.node_id,
                        %peer_id,
                        tip_block_no,
                        missing_len = missing.len(),
                        ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                        "select_chain: fetching missing blocks"
                    );
                    self.issue_fetch(missing).await;
                    return;
                }
            }
        }
    }

    /// Execute a fork switch decided by `select_chain`: roll back the
    /// chain store to `ancestor`'s point and replay `replay` (oldest→newest).
    async fn execute_switch(&mut self, ancestor: [u8; 32], replay: Vec<[u8; 32]>) {
        // For a fresh node starting from synthetic genesis, there's no
        // rollback to issue — we're building from nothing.
        if ancestor == [0u8; 32] && self.adopted_tip_hash.is_none() {
            for hash in replay {
                self.inject_block(hash).await;
            }
            return;
        }

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

        // Only issue a rollback if we're actually moving off the current tip.
        if self.adopted_tip_hash != Some(ancestor) {
            let _ = self
                .commands
                .send(NetworkCommand::InjectRollback {
                    point: ancestor_point,
                })
                .await;
            self.adopted_tip_hash = Some(ancestor);
        }

        for hash in replay {
            self.inject_block(hash).await;
        }
    }

    /// Issue a `FetchBlockRange` covering the missing replay blocks,
    /// skipping blocks already in flight.
    async fn issue_fetch(&mut self, missing: Vec<Point>) {
        if missing.is_empty() {
            return;
        }
        self.evict_stale_in_flight();

        // Single range from oldest to newest missing block. Any validated
        // blocks interleaved with the missing ones will be re-received
        // harmlessly. The key is the `to` point — if it's already in
        // flight, a prior call already kicked a fetch that hasn't been
        // dropped as stale yet.
        let from = missing.first().unwrap().clone();
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
            .send(NetworkCommand::FetchBlockRange { from, to })
            .await;
    }

    /// Register a block we produced ourselves, so we don't re-fetch it.
    /// Returns the block_no to use for injection. Runs `select_chain`
    /// afterwards so a pending peer fork that's still better than the
    /// newly-produced tip is picked up immediately.
    pub async fn register_self_produced(&mut self, point: &Point, header: &WrappedHeader) -> u64 {
        self.self_produced.insert(point.clone());

        let block_no = if let Some(info) = header.parsed.as_ref() {
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
        };

        self.select_chain().await;
        block_no
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

    /// Handle a network event. Returns true if the event was consumed by
    /// consensus (caller should not log it separately).
    pub async fn handle_event(&mut self, event: &NetworkEvent) -> bool {
        match event {
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
                self.on_block_received(point, body);
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

            // Leios: fetch offered EBs, votes, and txs.
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
                let key = Point::Specific {
                    slot: match point {
                        Point::Specific { slot, .. } => *slot,
                        _ => 0,
                    },
                    hash: [0xFE; 32], // distinct key to avoid collision with block fetch
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

        // Let select_chain decide whether to fork-switch or fetch more.
        let adopted_before = self.adopted_tip_hash;
        self.select_chain().await;
        let rolled_back = adopted_before != self.adopted_tip_hash && adopted_before.is_some();

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

    fn test_dyn_rx() -> tokio::sync::watch::Receiver<crate::config::DynamicConfig> {
        let config = crate::config::NodeConfig::default();
        tokio::sync::watch::channel(config.dynamic_config()).1
    }

    fn make_consensus() -> (Consensus, mpsc::Receiver<NetworkCommand>) {
        let (cmd_tx, cmd_rx) = mpsc::channel(16);
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
        let consensus = Consensus::new("test".into(), cmd_tx, validator, 2160);
        (consensus, cmd_rx)
    }

    /// Consensus with a small k so the peer-chain cap is also small —
    /// lets us exercise the cap without announcing thousands of headers.
    fn make_consensus_with_k(k: u64) -> (Consensus, mpsc::Receiver<NetworkCommand>) {
        let (cmd_tx, cmd_rx) = mpsc::channel(16);
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
        let consensus = Consensus::new("test".into(), cmd_tx, validator, k);
        (consensus, cmd_rx)
    }

    #[tokio::test]
    async fn peer_chain_records_tip_advances() {
        let (mut consensus, _cmd_rx) = make_consensus();
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
        let (mut consensus, _cmd_rx) = make_consensus();
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
        let (mut consensus, _cmd_rx) = make_consensus();
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
        let (mut consensus, _cmd_rx) = make_consensus();
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
        let (mut consensus, _cmd_rx) = make_consensus();
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
        let (mut consensus, _cmd_rx) = make_consensus();
        let peer = PeerId(1);

        // Self-produce tip 1; peer announces the same.
        let (tip1, header1) = make_tip(1, 1, None);
        consensus
            .register_self_produced(&tip1.point, &header1)
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
        let (mut consensus, _cmd_rx) = make_consensus();
        let peer = PeerId(1);

        // Self-produce block 1.
        let (tip1, header1) = make_tip(1, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &header1)
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
        let (mut consensus, _cmd_rx) = make_consensus();
        let peer = PeerId(1);

        // Self-produce block 1.
        let (tip1, header1) = make_tip(1, 1, None);
        consensus
            .register_self_produced(&tip1.point, &header1)
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

    #[tokio::test]
    async fn select_chain_picks_best_of_multiple_candidates() {
        let (mut consensus, _cmd_rx) = make_consensus();
        let peer_a = PeerId(1);
        let peer_b = PeerId(2);

        // Self-produce block 1.
        let (tip1, header1) = make_tip(1, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &header1)
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
        let (mut consensus, _cmd_rx) = make_consensus();
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
        let (mut consensus, mut cmd_rx) = make_consensus_with_k(4);
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
        let (mut consensus, mut cmd_rx) = make_consensus();

        let (tip, header) = make_tip(1, 1, None);
        consensus.register_self_produced(&tip.point, &header).await;

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
        let (mut consensus, mut cmd_rx) = make_consensus();

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
        let (mut consensus, mut cmd_rx) = make_consensus();

        // Set local tip to block 5.
        let (tip5, header5) = make_tip(5, 5, None);
        consensus
            .register_self_produced(&tip5.point, &header5)
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
        let (mut consensus, mut cmd_rx) = make_consensus();

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
        let (mut consensus, _cmd_rx) = make_consensus();

        assert!(consensus.tip_hash().is_none());

        let (tip, header) = make_tip(1, 1, None);
        let expected_hash = match &tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!("expected specific"),
        };
        consensus.register_self_produced(&tip.point, &header).await;

        assert_eq!(consensus.tip_hash(), Some(expected_hash));
    }

    #[tokio::test]
    async fn fork_switch_issues_rollback() {
        let (cmd_tx, mut cmd_rx) = mpsc::channel(32);
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator, 2160);

        // Build chain A: blocks 1, 2, 3 (self-produced, so they're in the tree).
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1).await;

        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip2.point, &hdr2).await;

        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));
        consensus.register_self_produced(&tip3.point, &hdr3).await;

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
                peer_id: TEST_PEER,
                tip: tipb2.clone(),
                header: hdrb2.clone(),
            })
            .await;
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: TEST_PEER,
                tip: tipb3.clone(),
                header: hdrb3.clone(),
            })
            .await;
        // B4 is the one that overtakes — announce and fetch it.
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: TEST_PEER,
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
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
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
            consensus.register_self_produced(&tip.point, &hdr).await;
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
            consensus.on_block_received(&tip.point, &make_block_body(&hdr));
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

    #[tokio::test]
    async fn block_received_inserts_into_chain_tree() {
        // Fix 1: on_block_received must insert into chain_tree so that
        // ancestors() and find_common_ancestor() work for fetched blocks.
        let (mut consensus, _cmd_rx) = make_consensus();

        let (tip, header) = make_tip(10, 1, None);
        let hash = match &tip.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };

        // Before receiving, block is not in chain_tree.
        assert!(consensus.chain_tree.block_number(&hash).is_none());

        // Simulate block fetch arrival with a proper block body.
        let body = make_block_body(&header);
        consensus.on_block_received(&tip.point, &body);

        // After receiving, block should be in chain_tree.
        assert_eq!(consensus.chain_tree.block_number(&hash), Some(1));
    }

    /// Regression: a fetch that the coordinator silently dropped (e.g. no
    /// peer had the requested point in its fragment) must not permanently
    /// block re-fetching. With TTL eviction in `select_chain`'s fetch path,
    /// a later trigger sees the stale entry as expired, removes it, and
    /// emits a retry.
    #[tokio::test]
    async fn stale_in_flight_evicted_so_fetch_retries() {
        let (mut consensus, mut cmd_rx) = make_consensus();

        // Adopt block#1 (self-produced).
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1).await;

        // Peer announces block#2: header inserted into tree, fetch issued,
        // in_flight[block#2] set.
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                peer_id: TEST_PEER,
                tip: tip2.clone(),
                header: hdr2.clone(),
            })
            .await;
        while cmd_rx.try_recv().is_ok() {}
        assert!(consensus.in_flight.contains_key(&tip2.point));

        // The fetch is silently dropped — block#2 body never arrives. Now
        // block#3 arrives directly (e.g. via a different peer's range fetch
        // that reached us with block#3 but not block#2). Validate it.
        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));
        consensus.on_block_received(&tip3.point, &make_block_body(&hdr3));
        consensus
            .on_validation_complete(ValidationComplete {
                point: tip3.point.clone(),
            })
            .await;
        while cmd_rx.try_recv().is_ok() {}

        // Mark block#2's in_flight entry as stale.
        let stale = Instant::now() - IN_FLIGHT_TTL - Duration::from_secs(1);
        consensus.in_flight.insert(tip2.point.clone(), stale);

        // Trigger another `fetch_unvalidated_ancestors` pass via a no-op
        // validation complete. With stale eviction, the walk should now
        // recognise block#2 as fetchable and emit a range fetch covering
        // it. Without the fix, the walk hits `in_flight.contains_key` and
        // breaks, emitting nothing.
        consensus
            .on_validation_complete(ValidationComplete {
                point: tip3.point.clone(),
            })
            .await;

        let mut saw_fetch_for_block2 = false;
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::FetchBlockRange { from, to } = cmd {
                if from == tip2.point || to == tip2.point {
                    saw_fetch_for_block2 = true;
                }
            }
        }
        assert!(
            saw_fetch_for_block2,
            "stale in_flight should have been evicted; expected a fetch for block#2"
        );
    }
}
