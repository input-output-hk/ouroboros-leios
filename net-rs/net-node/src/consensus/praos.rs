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
    /// Bodies waiting for their parent to be known to the validator.
    /// Keyed by the parent hash they're waiting on. When the parent
    /// becomes known (arrives via `on_block_received`, is self-produced,
    /// or reaches `Applied`), the children in its entry are drained and
    /// submitted in chain order.
    pending_validation: HashMap<[u8; 32], Vec<(Point, BlockBody)>>,
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
            pending_validation: HashMap::new(),
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
        self.drain_pending(hash).await;
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
                    // Drop pending_validation entries whose parent has
                    // fallen out of the k-window — the children are
                    // orphaned and will never become valid here.
                    let tree = &self.chain_tree;
                    self.pending_validation
                        .retain(|parent, _| tree.point(parent).is_some());
                }
            }
        }

        // Drain any children that were waiting on this block. Do this
        // after the prune so the prune doesn't sweep children we're
        // about to submit, and before select_chain so newly-submitted
        // children are visible to its in-flight checks.
        self.drain_pending(hash).await;

        // A newly-validated block can unblock a fork switch we couldn't
        // execute earlier (e.g. waiting for the last replay block).
        self.select_chain().await;
    }

    /// Rollback succeeded: the ledger is now back at `target`, so the
    /// chain store should mirror that.
    async fn handle_rolled_back(&mut self, target: Point) {
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
        // Children waiting on this failed block will never become
        // valid via this parent; drop them from the pending queue.
        // (They stay in block_cache until prune_below_k reclaims them.)
        self.pending_validation.remove(&hash);
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

    /// A fetched block arrived — cache it and either submit it to the
    /// validator (if its parent is known) or queue it in
    /// `pending_validation` until the parent arrives.
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

        if self.parent_known_to_validator(prev_hash) {
            info!(
                node_id = %self.node_id,
                %point,
                body_len = body.raw.len(),
                "block received, submitting for validation"
            );
            self.submit_for_validation(point.clone(), body.clone(), prev_hash)
                .await;
            self.drain_pending(hash).await;
        } else {
            info!(
                node_id = %self.node_id,
                %point,
                body_len = body.raw.len(),
                parent = ?prev_hash.map(|h| format!("{:02x}{:02x}", h[30], h[31])),
                "block received, queueing in pending_validation until parent arrives"
            );
            let parent_hash = prev_hash.expect("gate guarantees prev_hash is Some here");
            self.pending_validation
                .entry(parent_hash)
                .or_default()
                .push((point.clone(), body.clone()));
        }
    }

    /// True if a block with the given `prev_hash` can be handed to the
    /// validator directly. The validator's sequential actor will apply
    /// the parent before this block as long as the parent is already in
    /// its queue, so "submitted" is good enough — we don't need the
    /// parent's `Applied` outcome to have arrived first.
    fn parent_known_to_validator(&self, prev_hash: Option<[u8; 32]>) -> bool {
        match prev_hash {
            None => true, // genesis
            Some(parent) => {
                self.validated.contains(&parent)
                    || self.in_flight_validation.contains(&parent)
                    || self.queued_validator_tip == Some(parent)
            }
        }
    }

    /// Drain any pending_validation entries waiting on `parent_hash`.
    /// Each drained child is submitted to the validator via
    /// `submit_for_validation` (which handles Rollback insertion if
    /// needed) and recursively drains its own children. The recursion
    /// is flattened into a worklist to avoid the `Box::pin` dance for
    /// recursive async fns.
    async fn drain_pending(&mut self, parent_hash: [u8; 32]) {
        let mut worklist: VecDeque<[u8; 32]> = VecDeque::new();
        worklist.push_back(parent_hash);

        while let Some(parent) = worklist.pop_front() {
            let children = match self.pending_validation.remove(&parent) {
                Some(c) => c,
                None => continue,
            };
            for (point, body) in children {
                let child_hash = match &point {
                    Point::Specific { hash, .. } => *hash,
                    _ => continue,
                };
                self.submit_for_validation(point, body, Some(parent)).await;
                // submit_for_validation already put child_hash into
                // in_flight_validation; now enqueue it so any of its
                // own waiters get drained on the next loop iteration.
                worklist.push_back(child_hash);
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

        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
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

    /// A block whose parent isn't known to the validator should be
    /// queued in `pending_validation` rather than blindly submitted.
    #[tokio::test]
    async fn child_arriving_before_parent_queued_in_pending() {
        let (mut consensus, mut cmd_rx, mut val_rx) = make_consensus();

        // Fabricate a child whose parent hash is completely unknown.
        let unknown_parent: [u8; 32] = [0xEE; 32];
        let (tip_child, hdr_child) = make_tip(5, 2, Some(unknown_parent));

        consensus
            .on_block_received(&tip_child.point, &make_block_body(&hdr_child))
            .await;

        // The child is sitting in pending_validation, not submitted.
        assert!(
            consensus.pending_validation.contains_key(&unknown_parent),
            "child should be queued under its parent hash"
        );
        assert!(
            consensus.in_flight_validation.is_empty(),
            "nothing should have been submitted to the validator"
        );

        // Draining the validator shouldn't produce any outcomes.
        drain_validator(&mut consensus, &mut val_rx).await;
        assert!(
            cmd_rx.try_recv().is_err(),
            "no InjectBlock should have been emitted"
        );
    }

    /// When the parent finally arrives, the child in `pending_validation`
    /// should be submitted right after it. The validator sees Apply(parent)
    /// then Apply(child), in that order.
    #[tokio::test]
    async fn parent_arrival_drains_pending_in_order() {
        let (mut consensus, mut cmd_rx, mut val_rx) = make_consensus();

        // Build a two-block chain: A1 (genesis) ← A2.
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };

        // Deliver A2 first — parent is unknown, goes to pending.
        consensus
            .on_block_received(&tip2.point, &make_block_body(&hdr2))
            .await;
        assert!(consensus.pending_validation.contains_key(&hash1));
        assert!(!consensus.in_flight_validation.contains(&hash2));

        // Now deliver A1 — it's genesis, submits directly, then the
        // drain cascades A2 into the queue.
        consensus
            .on_block_received(&tip1.point, &make_block_body(&hdr1))
            .await;
        assert!(consensus.pending_validation.is_empty());
        assert!(consensus.in_flight_validation.contains(&hash1));
        assert!(consensus.in_flight_validation.contains(&hash2));

        // Drain outcomes → both should end up validated.
        drain_validator(&mut consensus, &mut val_rx).await;
        assert!(consensus.validated.contains(&hash1));
        assert!(consensus.validated.contains(&hash2));

        // InjectBlock should be sent for both, in chain order.
        let mut injected = Vec::new();
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::InjectBlock { point, .. } = cmd {
                injected.push(point);
            }
        }
        assert_eq!(injected.len(), 2);
        assert_eq!(injected[0], tip1.point);
        assert_eq!(injected[1], tip2.point);
    }

    /// A peer-fetched child can arrive before its parent is self-produced.
    /// When the self-produced block is registered, the drain should pick
    /// up the waiting child and submit it.
    #[tokio::test]
    async fn self_produced_block_drains_pending_children() {
        let (mut consensus, _cmd_rx, mut val_rx) = make_consensus();

        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };

        // Peer delivers the child B2 before we've produced A1.
        consensus
            .on_block_received(&tip2.point, &make_block_body(&hdr2))
            .await;
        assert!(consensus.pending_validation.contains_key(&hash1));

        // Now we self-produce A1 — should drain B2 out of pending.
        consensus
            .register_self_produced(&tip1.point, &hdr1, &make_block_body(&hdr1))
            .await;
        assert!(consensus.pending_validation.is_empty());
        assert!(consensus.in_flight_validation.contains(&hash2));

        drain_validator(&mut consensus, &mut val_rx).await;
        assert!(consensus.validated.contains(&hash1));
        assert!(consensus.validated.contains(&hash2));
    }

    /// Three blocks delivered in reverse (grandchild, child, parent)
    /// should all end up validated in chain order when the parent
    /// finally lands, via a cascading drain.
    #[tokio::test]
    async fn deep_chain_out_of_order_drains_correctly() {
        let (mut consensus, _cmd_rx, mut val_rx) = make_consensus();

        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));
        let hash3 = match &tip3.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };

        // Reverse delivery: A3 first, then A2, then A1.
        consensus
            .on_block_received(&tip3.point, &make_block_body(&hdr3))
            .await;
        consensus
            .on_block_received(&tip2.point, &make_block_body(&hdr2))
            .await;
        // Both should be waiting in pending_validation.
        assert!(consensus.pending_validation.contains_key(&hash1));
        assert!(consensus.pending_validation.contains_key(&hash2));
        assert!(consensus.in_flight_validation.is_empty());

        consensus
            .on_block_received(&tip1.point, &make_block_body(&hdr1))
            .await;
        // Cascade drain should have submitted all three.
        assert!(consensus.pending_validation.is_empty());
        assert!(consensus.in_flight_validation.contains(&hash1));
        assert!(consensus.in_flight_validation.contains(&hash2));
        assert!(consensus.in_flight_validation.contains(&hash3));

        drain_validator(&mut consensus, &mut val_rx).await;
        assert!(consensus.validated.contains(&hash1));
        assert!(consensus.validated.contains(&hash2));
        assert!(consensus.validated.contains(&hash3));
    }

    /// Pending entries whose parent has fallen out of the k-window
    /// should be evicted when `prune_below_k` fires.
    #[tokio::test]
    async fn pending_evicted_when_parent_pruned() {
        let (mut consensus, _cmd_rx, mut val_rx) = make_consensus_with_k(4);

        // Parent A1 at block 1; it'll be pruned once we advance
        // beyond k = 4.
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .register_self_produced(&tip1.point, &hdr1, &make_block_body(&hdr1))
            .await;
        drain_validator(&mut consensus, &mut val_rx).await;

        // Plant an orphan child whose parent is completely unknown
        // (so pending_validation holds it).
        let unknown_parent: [u8; 32] = [0xAB; 32];
        let (tip_orphan, hdr_orphan) = make_tip(25, 2, Some(unknown_parent));
        consensus
            .on_block_received(&tip_orphan.point, &make_block_body(&hdr_orphan))
            .await;
        assert!(consensus.pending_validation.contains_key(&unknown_parent));

        // Advance past the k-window by self-producing enough blocks.
        // k=4 means once we reach block 6+, blocks below 2 get pruned.
        // More importantly, pending entries whose parent isn't in
        // chain_tree get dropped.
        let mut prev = Some(hash1);
        for i in 2..=7u64 {
            let (tip, hdr) = make_tip(i * 10, i, prev);
            prev = match &tip.point {
                Point::Specific { hash, .. } => Some(*hash),
                _ => None,
            };
            consensus
                .register_self_produced(&tip.point, &hdr, &make_block_body(&hdr))
                .await;
            drain_validator(&mut consensus, &mut val_rx).await;
        }

        // The orphan's unknown parent was never in chain_tree, so the
        // prune-time filter should have dropped it.
        assert!(
            !consensus.pending_validation.contains_key(&unknown_parent),
            "orphan pending entry should have been evicted by prune_below_k"
        );
    }

    /// ApplyFailed on a parent should drop any pending children waiting
    /// on it: they'll never become valid via that parent.
    #[tokio::test]
    async fn apply_failed_drops_pending_children() {
        let (mut consensus, _cmd_rx, _val_rx) = make_consensus();

        let (tip1, _hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));

        // Queue a child waiting on hash1.
        consensus
            .on_block_received(&tip2.point, &make_block_body(&hdr2))
            .await;
        assert!(consensus.pending_validation.contains_key(&hash1));

        // Mark the parent as in-flight so handle_apply_failed sees it.
        consensus.in_flight_validation.insert(hash1);

        // Simulate the parent's Apply failing.
        consensus
            .on_validation_outcome(LedgerOutcome::ApplyFailed {
                point: tip1.point.clone(),
                error: "intentional test failure".to_string(),
            })
            .await;

        // The pending entry for hash1 should have been dropped.
        assert!(!consensus.pending_validation.contains_key(&hash1));
        assert!(!consensus.in_flight_validation.contains(&hash1));
    }
}
