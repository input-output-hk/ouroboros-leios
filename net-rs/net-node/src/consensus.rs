//! Longest-chain consensus with fork tracking.

use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
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
    /// Hashes whose body is known to be unfetchable from any current peer.
    /// Set on `BlockFetchFailed` for single-block fetches; cleared when the
    /// same hash is later re-announced via `TipAdvanced` or its body arrives
    /// via `on_block_received` (e.g. a fresh peer with the block connects).
    unfetchable: HashSet<[u8; 32]>,
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
            unfetchable: HashSet::new(),
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

    /// Mark a block hash as unfetchable from any current peer and prune
    /// it together with all of its descendants from the chain tree, the
    /// block cache, the validated set, and the in-flight map. This is the
    /// recovery path for stale fork headers that no peer is willing to
    /// serve any more (e.g. they all rolled back to a different chain).
    /// Without this, `fetch_unvalidated_ancestors` and `try_fork_switch`
    /// keep walking the dead fork forever.
    fn mark_unfetchable_and_prune(&mut self, hash: [u8; 32]) {
        self.unfetchable.insert(hash);
        let removed = self.chain_tree.remove_subtree(hash);
        if removed.is_empty() {
            return;
        }
        // Drop matching entries from cache, validated set, and in-flight.
        for h in &removed {
            self.block_cache.remove(h);
            self.validated.remove(h);
        }
        self.in_flight.retain(|p, _| match p {
            Point::Specific { hash, .. } => !removed.contains(hash),
            _ => true,
        });
        info!(
            node_id = %self.node_id,
            removed_count = removed.len(),
            "pruned unfetchable fork from chain tree"
        );
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
                    self.mark_in_flight(to.clone());
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchBlockRange {
                            from: to.clone(),
                            to: to.clone(),
                        })
                        .await;
                } else {
                    // Single-block fetch failed: no peer has this block in
                    // its current chain (e.g. they all rolled back). Mark
                    // it unfetchable and prune the whole subtree so the
                    // walks stop wasting effort on it.
                    info!(
                        node_id = %self.node_id,
                        from = %from,
                        to = %to,
                        "block fetch failed; pruning subtree"
                    );
                    if let Point::Specific { hash, .. } = from {
                        self.mark_unfetchable_and_prune(*hash);
                    }
                }
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
                    // Drop unfetchable entries that are no longer in the
                    // tree (and thus can't possibly be referenced again).
                    self.unfetchable.retain(|h| self.chain_tree.contains(h));
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
        // Track insert_hash so the fetch range walk can use it when tip_hash
        // isn't in the tree (catch-up mode).
        let mut insert_hash_opt: Option<[u8; 32]> = None;
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
            // A fresh peer announced this header — clear any prior
            // unfetchable marker so we'll try fetching the body again.
            self.unfetchable.remove(&insert_hash);
            insert_hash_opt = Some(insert_hash);
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

        // Drop stale fetches before checking, so a silently-dropped previous
        // attempt doesn't permanently block this tip.
        self.evict_stale_in_flight();
        if self.in_flight.contains_key(point) {
            return;
        }

        // Walk chain_tree ancestors to find the earliest unvalidated block —
        // issue a range fetch from there to the tip. During catch-up the tip
        // hash isn't in chain_tree (only the intermediate header was inserted),
        // so walk from insert_hash instead.
        let walk_hash = if self.chain_tree.block_number(&tip_hash).is_some() {
            tip_hash
        } else if let Some(ih) = insert_hash_opt {
            ih
        } else {
            tip_hash
        };
        let ancestors = self.chain_tree.ancestors(walk_hash);
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

        // If no cached ancestor was found (single-block fetch), fall back to
        // fetching from the adopted tip so the range covers all missing blocks.
        // Only do so if the adopted tip is strictly older than the announced
        // tip (otherwise we'd send a backwards range across a fork).
        if fetch_from == *point {
            if let Some(adopted_hash) = self.adopted_tip_hash {
                if let Some(adopted_point) = self.chain_tree.point(&adopted_hash) {
                    let adopted_slot = match adopted_point {
                        Point::Specific { slot, .. } => *slot,
                        _ => 0,
                    };
                    let tip_slot = match point {
                        Point::Specific { slot, .. } => *slot,
                        _ => 0,
                    };
                    if adopted_slot < tip_slot {
                        fetch_from = adopted_point.clone();
                    }
                }
            }
        }

        info!(
            node_id = %self.node_id,
            %tip,
            from = %fetch_from,
            "fetching blocks for longer chain"
        );

        self.mark_in_flight(point.clone());
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
        // Insert into chain_tree so ancestors()/find_common_ancestor() can
        // walk through fetched blocks — critical for fork switches.
        if let Some(info) = header.parsed.as_ref() {
            self.chain_tree.insert(
                hash,
                point.clone(),
                info.block_number,
                info.slot,
                info.prev_hash,
            );
        }
        // The block actually arrived, so any prior unfetchable marker is
        // stale.
        self.unfetchable.remove(&hash);
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
                // Kick off a single-block fetch for the missing block.
                // It sits between two validated blocks in the tree — a
                // position `fetch_unvalidated_ancestors` can miss when its
                // `best_unadopted` selection lands on a different chain
                // than `try_fork_switch`'s `best`. The fetch will either
                // bring the body in (recovery) or fail with
                // `BlockFetchFailed`, which our handler turns into a
                // `mark_unfetchable_and_prune` call.
                self.evict_stale_in_flight();
                if !in_cache {
                    if let Some(p) = self.chain_tree.point(&cur).cloned() {
                        if !self.in_flight.contains_key(&p) {
                            self.mark_in_flight(p.clone());
                            let _ = self
                                .commands
                                .send(NetworkCommand::FetchBlockRange {
                                    from: p.clone(),
                                    to: p,
                                })
                                .await;
                        }
                    }
                }
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
        self.evict_stale_in_flight();
        let mut roots: Vec<[u8; 32]> = Vec::new();
        if let Some(h) = self.adopted_tip_hash {
            roots.push(h);
        }
        // Walk from the best validated block that isn't the adopted tip.
        // This traces the chain the fork switch needs, finding gaps where
        // intermediate blocks haven't been fetched yet. Only consider forks
        // that are STRICTLY better than the adopted tip — otherwise stale
        // forks below the adopted chain churn here forever.
        let adopted_bn = self
            .adopted_tip_hash
            .and_then(|h| self.chain_tree.block_number(&h))
            .unwrap_or(0);
        let best_unadopted = self
            .block_cache
            .iter()
            .filter(|(&h, cb)| {
                self.validated.contains(&h) && !roots.contains(&h) && cb.block_no > adopted_bn
            })
            .max_by_key(|(_, cb)| cb.block_no)
            .map(|(h, _)| *h);
        if let Some(h) = best_unadopted {
            roots.push(h);
        }

        for root in roots {
            let ancestors = self.chain_tree.ancestors(root);
            // If the deepest known ancestor's parent is unfetchable, the
            // whole fork is dead — every fetch we'd issue here would just
            // bounce off `MsgNoBlocks`. Skip this root entirely.
            if let Some(deepest) = ancestors.last() {
                if let Some(parent) = self.chain_tree.prev_hash(deepest) {
                    if self.unfetchable.contains(&parent) {
                        continue;
                    }
                }
            }
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
                    if self.self_produced.contains(p) || self.in_flight.contains_key(p) {
                        break;
                    }
                    gap_start = Some(p.clone());
                    if gap_end.is_none() {
                        gap_end = Some(p.clone());
                    }
                }
            }
            // If the ancestor walk hit a dead end (parent not in tree),
            // check if the deepest block has a prev_hash pointing to a
            // missing block. If so, fetch from the adopted tip.
            if gap_start.is_none() && !ancestors.is_empty() {
                let deepest = *ancestors.last().unwrap();
                let prev = self
                    .block_cache
                    .get(&deepest)
                    .and_then(|cb| cb.prev_hash)
                    .or_else(|| self.chain_tree.prev_hash(&deepest));
                if let Some(parent_hash) = prev {
                    // If the missing parent is known to be unfetchable,
                    // this entire fork is dead — don't waste a fetch on
                    // it. Without this, the loop spins forever issuing
                    // single-block fetches that nobody can answer.
                    if self.unfetchable.contains(&parent_hash) {
                        continue;
                    }
                    if !self.block_cache.contains_key(&parent_hash)
                        && !adopted_set.contains(&parent_hash)
                    {
                        if let Some(adopted_hash) = self.adopted_tip_hash {
                            if let (Some(adopted_point), Some(deepest_point)) = (
                                self.chain_tree.point(&adopted_hash).cloned(),
                                self.chain_tree.point(&deepest).cloned(),
                            ) {
                                // Only fire if adopted is strictly older than
                                // deepest. Otherwise adopted is on a competing
                                // fork and the range would be backwards (or
                                // span two unrelated chains).
                                let adopted_slot = match &adopted_point {
                                    Point::Specific { slot, .. } => *slot,
                                    _ => 0,
                                };
                                let deepest_slot = match &deepest_point {
                                    Point::Specific { slot, .. } => *slot,
                                    _ => 0,
                                };
                                if adopted_slot < deepest_slot
                                    && !self.in_flight.contains_key(&deepest_point)
                                {
                                    gap_start = Some(adopted_point);
                                    gap_end = Some(deepest_point);
                                }
                            }
                        }
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
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
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

    #[tokio::test]
    async fn catchup_fetch_uses_range_not_single_block() {
        // Fix 2: during catch-up (header != tip), on_tip_advanced should
        // walk from the intermediate header's hash, not the tip hash, to
        // compute a range fetch covering all missing ancestors.
        let (cmd_tx, mut cmd_rx) = mpsc::channel(32);
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator, 2160);

        // Adopt block 1 as our tip.
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1);

        // Insert block 2 header into chain_tree (as if an earlier
        // TipAdvanced intermediate header).
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .chain_tree
            .insert(hash2, tip2.point.clone(), 2, 20, Some(hash1));

        // Now simulate a catch-up TipAdvanced: tip is block 5, but the
        // header is for block 3 (intermediate). Block 5 is NOT in chain_tree.
        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));

        let tip5_header = make_header(50, 5, None);
        let tip5_point = Point::Specific {
            slot: 50,
            hash: [0xAA; 32], // fake hash, won't be in chain_tree
        };
        let tip5 = Tip {
            point: tip5_point.clone(),
            block_no: 5,
        };

        // Send TipAdvanced with tip=block5, header=block3.
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip5,
                header: hdr3,
            })
            .await;

        // Should issue a FetchBlockRange where from != to.
        let cmd = cmd_rx.recv().await.unwrap();
        match cmd {
            NetworkCommand::FetchBlockRange { from, to } => {
                let from_slot = match &from {
                    Point::Specific { slot, .. } => *slot,
                    _ => panic!("expected specific point for from"),
                };
                let to_slot = match &to {
                    Point::Specific { slot, .. } => *slot,
                    _ => panic!("expected specific point for to"),
                };
                // `from` should be block 2 (earliest unfetched ancestor
                // reachable via the intermediate header), not block 5.
                assert_eq!(
                    from_slot, 20,
                    "from should be block 2 (slot 20), not the tip"
                );
                assert_eq!(to_slot, 50, "to should be the tip (slot 50)");
            }
            other => panic!("expected FetchBlockRange, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn fork_switch_works_after_fetch_fills_chain_tree() {
        // With Fix 1, fetched blocks are in chain_tree, so
        // find_common_ancestor succeeds and fork switch fires.
        let (cmd_tx, mut cmd_rx) = mpsc::channel(256);
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator, 2160);

        // Chain A: blocks 1, 2 (self-produced).
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1);

        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        consensus.register_self_produced(&tip2.point, &hdr2);

        assert_eq!(consensus.local_tip().unwrap().block_no, 2);

        // Fork B diverges from block 1: B2 at slot 21, B3 at slot 31.
        let (tipb2, hdrb2) = make_tip(21, 2, Some(hash1));
        let hashb2 = match &tipb2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tipb3, hdrb3) = make_tip(31, 3, Some(hashb2));

        // Simulate fetching B2 and B3 bodies (WITHOUT prior TipAdvanced).
        // With Fix 1, on_block_received inserts them into chain_tree.
        consensus.on_block_received(&tipb2.point, &make_block_body(&hdrb2));
        consensus.on_block_received(&tipb3.point, &make_block_body(&hdrb3));

        // Validate B2 then B3.
        consensus
            .on_validation_complete(ValidationComplete {
                point: tipb2.point.clone(),
            })
            .await;
        consensus
            .on_validation_complete(ValidationComplete {
                point: tipb3.point.clone(),
            })
            .await;

        // Drain commands — should see rollback + inject for fork switch.
        let mut got_rollback = false;
        let mut inject_count = 0;
        while let Ok(cmd) = cmd_rx.try_recv() {
            match cmd {
                NetworkCommand::InjectRollback { .. } => got_rollback = true,
                NetworkCommand::InjectBlock { .. } => inject_count += 1,
                _ => {}
            }
        }

        assert!(
            got_rollback,
            "fork switch should fire now that fetched blocks are in chain_tree"
        );
        assert!(
            inject_count >= 2,
            "should inject B2, B3: got {inject_count}"
        );
    }

    #[tokio::test]
    async fn fetch_range_when_parent_unknown() {
        // Scenario: node adopts block#1(A). A peer announces block#2 whose
        // parent block#1(B) was never inserted into the chain tree.
        // The fetch should use a range from the adopted tip, not a single block.
        let (cmd_tx, mut cmd_rx) = mpsc::channel(32);
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator, 2160);

        // Adopt block 1(A).
        let (tip1a, hdr1a) = make_tip(10, 1, None);
        let hash1a = match &tip1a.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1a.point, &hdr1a);

        // A different block#1(B) — we only know its hash, never announced.
        let hdr1b = make_header(11, 1, None);
        let hash1b = match hdr1b.point().unwrap() {
            Point::Specific { hash, .. } => hash,
            _ => panic!(),
        };

        // Peer announces block#2 whose parent is block#1(B) (unknown to us).
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1b));

        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip2.clone(),
                header: hdr2,
            })
            .await;

        // Should issue a FetchBlockRange. The `from` should be the adopted
        // tip (block#1(A)), not the announced tip itself (which would be a
        // useless single-block fetch).
        let cmd = cmd_rx.recv().await.unwrap();
        match cmd {
            NetworkCommand::FetchBlockRange { from, to } => {
                assert_eq!(
                    from, tip1a.point,
                    "from should be adopted tip, not the announced tip"
                );
                assert_eq!(to, tip2.point, "to should be the announced tip");
            }
            other => panic!("expected FetchBlockRange, got {other:?}"),
        }
    }

    /// Regression: when adopted tip is on a different fork than a validated
    /// unadopted block, `fetch_unvalidated_ancestors` must NOT emit a range
    /// fetch with `from`/`to` on different forks (the BlockFetch range would
    /// be invalid since `from` is not an ancestor of `to`).
    #[tokio::test]
    async fn no_cross_fork_range_in_fetch_unvalidated_ancestors() {
        let (cmd_tx, mut cmd_rx) = mpsc::channel(64);
        let (validator, _val_rx) = Validator::new(test_dyn_rx());
        let mut consensus = Consensus::new("test".into(), cmd_tx, validator, 2160);

        // Adopt block#1(A) — common base.
        let (tip1a, hdr1a) = make_tip(10, 1, None);
        let hash1a = match &tip1a.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1a.point, &hdr1a);

        // Construct block#2(B) on a hidden fork: parent is some unknown
        // block#1(B). We never insert block#1(B) into the tree.
        let hdr1b = make_header(11, 1, None);
        let hash1b = match hdr1b.point().unwrap() {
            Point::Specific { hash, .. } => hash,
            _ => panic!(),
        };
        let (tip2b, hdr2b) = make_tip(20, 2, Some(hash1b));

        // Receive + validate block#2(B). It enters the cache + validated set,
        // but its parent isn't in the tree.
        consensus.on_block_received(&tip2b.point, &make_block_body(&hdr2b));
        // Drain anything from the receive (likely nothing).
        while cmd_rx.try_recv().is_ok() {}
        consensus
            .on_validation_complete(ValidationComplete {
                point: tip2b.point.clone(),
            })
            .await;
        // Drain commands triggered by validation.
        while cmd_rx.try_recv().is_ok() {}

        // Self-produce block#2(A) at a slot LATER than block#2(B). This makes
        // adopted tip newer (in slot terms) than the deepest known ancestor of
        // best_unadopted = block#2(B).
        let (tip2a, hdr2a) = make_tip(30, 2, Some(hash1a));
        consensus.register_self_produced(&tip2a.point, &hdr2a);
        while cmd_rx.try_recv().is_ok() {}

        // Now trigger fetch_unvalidated_ancestors via a no-op TipAdvanced.
        // (Re-announce our own adopted tip — dominated path still calls it.)
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip2a.clone(),
                header: hdr2a.clone(),
            })
            .await;

        // Inspect any range fetches: NONE may have from-slot > to-slot.
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::FetchBlockRange { from, to } = cmd {
                let from_slot = match &from {
                    Point::Specific { slot, .. } => *slot,
                    _ => 0,
                };
                let to_slot = match &to {
                    Point::Specific { slot, .. } => *slot,
                    _ => 0,
                };
                assert!(
                    from_slot <= to_slot,
                    "invalid backwards range: from {from} > to {to}"
                );
            }
        }
    }

    /// Regression: a fetch that the coordinator silently dropped (e.g. no
    /// peer had the requested point in its fragment) must not permanently
    /// block re-fetching. The walk in `fetch_unvalidated_ancestors` would
    /// otherwise `break` on the stale `in_flight` entry, leaving the gap
    /// unfetched forever. With TTL eviction, a later
    /// `fetch_unvalidated_ancestors` call sees the stale entry as expired,
    /// removes it, and emits a retry.
    #[tokio::test]
    async fn stale_in_flight_evicted_so_fetch_retries() {
        let (mut consensus, mut cmd_rx) = make_consensus();

        // Adopt block#1 (self-produced).
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1);

        // Peer announces block#2: header inserted into tree, fetch issued,
        // in_flight[block#2] set.
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
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

    /// A single-block fetch failure marks the hash unfetchable and prunes
    /// the entire fork rooted at it. The walks that previously kept tripping
    /// over the dead fork will now skip it naturally.
    #[tokio::test]
    async fn unfetchable_blocks_pruned_on_failed_fetch() {
        let (mut consensus, _cmd_rx) = make_consensus();

        // Adopt block#1 (self-produced).
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1);

        // Announce block#2 — header inserted into chain_tree.
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip2.clone(),
                header: hdr2,
            })
            .await;
        assert!(consensus.chain_tree.contains(&hash2));

        // Single-block fetch fails for block#2.
        consensus
            .handle_event(&NetworkEvent::BlockFetchFailed {
                from: tip2.point.clone(),
                to: tip2.point.clone(),
            })
            .await;

        assert!(consensus.unfetchable.contains(&hash2));
        assert!(!consensus.chain_tree.contains(&hash2));
        assert!(!consensus.block_cache.contains_key(&hash2));
        assert!(!consensus.in_flight.contains_key(&tip2.point));
    }

    /// When the unfetchable block has descendants in the tree, they must
    /// also be removed — otherwise `best_unadopted` selection or the walk
    /// could still pick a descendant and rediscover the dead fork.
    #[tokio::test]
    async fn unfetchable_subtree_descendants_also_pruned() {
        let (mut consensus, _cmd_rx) = make_consensus();

        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1);

        // Announce a chain block#2 → block#3 → block#4 (headers only).
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
        let (tip4, hdr4) = make_tip(40, 4, Some(hash3));
        let hash4 = match &tip4.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        for (tip, hdr) in [
            (tip2.clone(), hdr2),
            (tip3.clone(), hdr3),
            (tip4.clone(), hdr4),
        ] {
            consensus
                .handle_event(&NetworkEvent::TipAdvanced { tip, header: hdr })
                .await;
        }
        assert!(consensus.chain_tree.contains(&hash4));

        // Block#2 single-fetch fails — should prune 2, 3, 4.
        consensus
            .handle_event(&NetworkEvent::BlockFetchFailed {
                from: tip2.point.clone(),
                to: tip2.point.clone(),
            })
            .await;

        for h in [hash2, hash3, hash4] {
            assert!(
                !consensus.chain_tree.contains(&h),
                "all descendants should be pruned"
            );
        }
        // Best tip falls back to block#1 (the adopted/self-produced one).
        assert_eq!(consensus.chain_tree.best_tip_hash(), Some(hash1));
    }

    /// A re-announcement of an unfetchable hash clears the marker and lets
    /// future fetches retry — important so a transient peer outage doesn't
    /// permanently blacklist a block.
    #[tokio::test]
    async fn unfetchable_cleared_on_reinsert() {
        let (mut consensus, _cmd_rx) = make_consensus();

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
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip2.clone(),
                header: hdr2.clone(),
            })
            .await;
        consensus
            .handle_event(&NetworkEvent::BlockFetchFailed {
                from: tip2.point.clone(),
                to: tip2.point.clone(),
            })
            .await;
        assert!(consensus.unfetchable.contains(&hash2));

        // A fresh peer re-announces block#2.
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip2.clone(),
                header: hdr2,
            })
            .await;

        assert!(!consensus.unfetchable.contains(&hash2));
        assert!(consensus.chain_tree.contains(&hash2));
    }

    /// After a hash has been pruned and marked unfetchable, the walk in
    /// `fetch_unvalidated_ancestors` must skip any root whose chain
    /// dead-ends at that hash. Otherwise it issues a fetch that nobody
    /// can answer and the loop spins forever.
    #[tokio::test]
    async fn fetch_skips_roots_dead_ending_in_unfetchable() {
        let (mut consensus, mut cmd_rx) = make_consensus();

        // Adopt block#1.
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1);

        // Manually plant a chain block#1 → 2 → 3 in chain_tree, then mark
        // block#2 as unfetchable WITHOUT pruning the descendants from the
        // tree (simulating a re-insert after a prior prune).
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let info2 = hdr2.parsed.as_ref().unwrap();
        consensus.chain_tree.insert(
            hash2,
            tip2.point.clone(),
            info2.block_number,
            info2.slot,
            info2.prev_hash,
        );
        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));
        let hash3 = match &tip3.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let info3 = hdr3.parsed.as_ref().unwrap();
        consensus.chain_tree.insert(
            hash3,
            tip3.point.clone(),
            info3.block_number,
            info3.slot,
            info3.prev_hash,
        );

        // Now remove block#2 from the tree (so block#3's parent in tree is
        // gone) and mark it unfetchable.
        let removed = consensus.chain_tree.remove_subtree(hash2);
        // Note: removing block#2 also removes block#3 (it's a descendant).
        assert!(removed.contains(&hash3));
        // Re-insert block#3 alone (simulating a fresh receive that
        // resurrects the dead fork).
        consensus.chain_tree.insert(
            hash3,
            tip3.point.clone(),
            info3.block_number,
            info3.slot,
            info3.prev_hash,
        );
        consensus.unfetchable.insert(hash2);

        // Place block#3 in cache + validated so it would otherwise be
        // chosen as best_unadopted.
        consensus.block_cache.insert(
            hash3,
            CachedBlock {
                point: tip3.point.clone(),
                header: hdr3,
                body: make_block_body(&make_header(30, 3, Some(hash2))),
                block_no: 3,
                prev_hash: Some(hash2),
            },
        );
        consensus.validated.insert(hash3);

        // Trigger fetch_unvalidated_ancestors via on_validation_complete.
        consensus
            .on_validation_complete(ValidationComplete {
                point: tip3.point.clone(),
            })
            .await;

        // Expect NO fetch for block#3's dead chain.
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::FetchBlockRange { from, to } = cmd {
                let from_h = match &from {
                    Point::Specific { hash, .. } => Some(*hash),
                    _ => None,
                };
                let to_h = match &to {
                    Point::Specific { hash, .. } => Some(*hash),
                    _ => None,
                };
                assert!(
                    from_h != Some(hash3) && to_h != Some(hash3),
                    "no fetch should be issued for the dead-ended fork"
                );
                assert!(
                    from_h != Some(hash2) && to_h != Some(hash2),
                    "no fetch should be issued for the unfetchable parent"
                );
            }
        }
    }

    /// When `try_fork_switch` walks a chain and finds a block whose body
    /// isn't cached, it should kick off a single-block fetch for that
    /// block. Otherwise that header sits in `chain_tree` indefinitely,
    /// because `fetch_unvalidated_ancestors`'s walk may follow a different
    /// chain (different `best_unadopted`) and never visit it.
    #[tokio::test]
    async fn fork_switch_kicks_fetch_for_missing_intermediate() {
        let (mut consensus, mut cmd_rx) = make_consensus();

        // Adopt block#1.
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1);

        // Plant a chain block#1 → block#2 (header only) → block#3 (cached
        // + validated) directly into chain_tree, simulating the case where
        // the fork-switch walk reaches a header whose body never arrived.
        let (tip2, hdr2) = make_tip(20, 2, Some(hash1));
        let hash2 = match &tip2.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let info2 = hdr2.parsed.as_ref().unwrap();
        consensus.chain_tree.insert(
            hash2,
            tip2.point.clone(),
            info2.block_number,
            info2.slot,
            info2.prev_hash,
        );

        let (tip3, hdr3) = make_tip(30, 3, Some(hash2));
        let hash3 = match &tip3.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        // Insert block#3 into chain_tree AND cache + validate it.
        consensus.on_block_received(&tip3.point, &make_block_body(&hdr3));
        consensus.validated.insert(hash3);
        // Drain the validation-time fetch attempts so the test only sees
        // commands from the fork-switch path.
        while cmd_rx.try_recv().is_ok() {}

        // Trigger a fork switch attempt. block#3 is "best" (block_no > 1),
        // walk goes block#3 → block#2 → block#1. block#2 has no body —
        // walk should log "fork switch blocked" AND issue a single-block
        // fetch for block#2.
        let switched = consensus.try_fork_switch().await;
        assert!(!switched, "fork switch should be blocked by missing body");

        // Expect a FetchBlockRange { from: block#2, to: block#2 }.
        let mut saw_fetch_for_block2 = false;
        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::FetchBlockRange { from, to } = cmd {
                if from == tip2.point && to == tip2.point {
                    saw_fetch_for_block2 = true;
                }
            }
        }
        assert!(
            saw_fetch_for_block2,
            "fork-switch should kick a single-block fetch for the missing intermediate"
        );
        // And the in_flight set should reflect that.
        assert!(consensus.in_flight.contains_key(&tip2.point));
    }

    /// The full node-14 jam scenario: node has its own self-produced fork
    /// at block#2 (slot 20). It receives a competing chain via TipAdvanced
    /// only (headers, no bodies). Single-fetch for the competing block#2
    /// fails. After pruning, no further fetches should be issued for the
    /// dead fork's descendants, and `try_fork_switch` should be a no-op.
    #[tokio::test]
    async fn node_14_jam_regression() {
        let (mut consensus, mut cmd_rx) = make_consensus();

        // Self-produce block#1 then block#2A (the node's adopted fork).
        let (tip1, hdr1) = make_tip(10, 1, None);
        let hash1 = match &tip1.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        consensus.register_self_produced(&tip1.point, &hdr1);
        let (tip2a, hdr2a) = make_tip(20, 2, Some(hash1));
        consensus.register_self_produced(&tip2a.point, &hdr2a);

        // A peer announces a competing chain block#2B → block#3B → block#4B
        // built on the same hash1 root. Headers only.
        let (tip2b, hdr2b) = make_tip(21, 2, Some(hash1));
        let hash2b = match &tip2b.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip3b, hdr3b) = make_tip(31, 3, Some(hash2b));
        let hash3b = match &tip3b.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        let (tip4b, hdr4b) = make_tip(41, 4, Some(hash3b));
        let hash4b = match &tip4b.point {
            Point::Specific { hash, .. } => *hash,
            _ => panic!(),
        };
        for (tip, hdr) in [
            (tip2b.clone(), hdr2b),
            (tip3b.clone(), hdr3b),
            (tip4b.clone(), hdr4b),
        ] {
            consensus
                .handle_event(&NetworkEvent::TipAdvanced { tip, header: hdr })
                .await;
        }
        // Drain commands from the announcement walk.
        while cmd_rx.try_recv().is_ok() {}

        // Single-fetch for block#2B fails (no peer has it any more).
        consensus
            .handle_event(&NetworkEvent::BlockFetchFailed {
                from: tip2b.point.clone(),
                to: tip2b.point.clone(),
            })
            .await;

        // The dead fork is gone from the tree.
        for h in [hash2b, hash3b, hash4b] {
            assert!(
                !consensus.chain_tree.contains(&h),
                "dead fork descendant should be pruned"
            );
        }

        // `on_validation_complete` shouldn't crash and shouldn't issue
        // any fresh fetch for the pruned fork.
        let (_dummy_tip, dummy_hdr) = make_tip(15, 1, None);
        let _ = dummy_hdr; // unused
                           // (No new validation needed; just call fetch_unvalidated_ancestors
                           // directly via on_tip_advanced of the existing self-produced tip.)
        consensus
            .handle_event(&NetworkEvent::TipAdvanced {
                tip: tip2a.clone(),
                header: hdr2a,
            })
            .await;

        while let Ok(cmd) = cmd_rx.try_recv() {
            if let NetworkCommand::FetchBlockRange { from, to } = cmd {
                let from_h = match &from {
                    Point::Specific { hash, .. } => Some(*hash),
                    _ => None,
                };
                let to_h = match &to {
                    Point::Specific { hash, .. } => Some(*hash),
                    _ => None,
                };
                for h in [hash2b, hash3b, hash4b] {
                    assert!(
                        from_h != Some(h) && to_h != Some(h),
                        "no fetch should be issued for the pruned fork"
                    );
                }
            }
        }
    }
}
