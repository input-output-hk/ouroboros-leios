//! Chain selection: SelectionDecision, select_chain_once, try_stored_switch,
//! select_chain, execute_switch.

use std::collections::HashSet;

use net_core::multi_peer::types::NetworkCommand;
use net_core::peer::PeerId;
use net_core::types::Point;
use tracing::info;

use crate::chain_tree::is_better_tip;
use crate::validation::LedgerCommand;

use super::peer_chain::PeerChainEntry;

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

impl super::PraosConsensus {
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
    pub(super) fn select_chain_once(&self, skip: &HashSet<PeerId>) -> SelectionDecision {
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
    ///
    /// Returns `Ok((ancestor, replay))` on success, or `Err(gap_point)`
    /// when the walk from best_tip doesn't reach adopted_tip — the
    /// gap_point is where the walk stopped (the oldest block in the walk
    /// whose parent is missing from chain_tree). Callers can fetch that
    /// missing block to bridge the gap.
    pub(super) fn try_stored_switch(&self) -> Result<([u8; 32], Vec<[u8; 32]>), Option<Point>> {
        let best_hash = match self.chain_tree.best_tip_hash() {
            Some(h) => h,
            None => return Err(None),
        };
        let adopted = self.adopted_tip_hash.unwrap_or([0u8; 32]);
        if best_hash == adopted {
            return Err(None);
        }

        let walk = self.chain_tree.ancestors(best_hash);
        let adopted_pos = match walk.iter().position(|h| *h == adopted) {
            Some(p) => p,
            None => {
                // Walk didn't reach adopted_tip — there's a gap.
                // The oldest block in the walk has a missing parent.
                let gap_hash = walk.last().copied();
                let _gap_parent = gap_hash.and_then(|h| self.chain_tree.prev_hash(&h));
                // Return the point of the missing parent's child so
                // the caller knows where to fetch around.
                let gap_point = gap_hash.and_then(|h| self.chain_tree.point(&h).cloned());
                return Err(gap_point);
            }
        };

        // Blocks from adopted (exclusive) to best_tip (inclusive), oldest first.
        let replay: Vec<[u8; 32]> = walk[..adopted_pos].iter().rev().copied().collect();
        if replay.is_empty() {
            return Err(None);
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
            return Err(None);
        }
        Ok((adopted, prefix))
    }

    /// Drive chain selection to completion. First tries switching using
    /// stored blocks (chain_tree walk), then falls through to peer-chain
    /// based selection for fetching decisions.
    pub(super) async fn select_chain(&mut self) {
        // Try switching using blocks we already have, regardless of
        // which peer announced them.
        match self.try_stored_switch() {
            Ok((ancestor, replay)) => {
                info!(
                    node_id = %self.node_id,
                    replay_len = replay.len(),
                    ancestor = format!("{:02x}{:02x}", ancestor[30], ancestor[31]),
                    "select_chain: stored-block switch"
                );
                self.execute_switch(ancestor, replay).await;
                return;
            }
            Err(Some(_gap_point)) => {
                // Walk from best_tip didn't reach adopted — gap exists.
                // Don't fetch here (select_chain runs too often); the
                // periodic retry_select_chain handles gap fetching.
            }
            Err(None) => {}
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
    pub(super) async fn execute_switch(&mut self, ancestor: [u8; 32], replay: Vec<[u8; 32]>) {
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
}
