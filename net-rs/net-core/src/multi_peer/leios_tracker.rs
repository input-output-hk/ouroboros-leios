//! Leios deduplication, offer tracking, and fetch routing.
//!
//! Extracted from the coordinator to keep Leios-specific intelligence
//! (seen sets, per-peer offer maps, pending fetch dedup, RTT-based routing)
//! in a self-contained unit.

/// Max entries in Leios seen sets before dedup degrades (fail-open).
const MAX_LEIOS_SEEN: usize = 100_000;
/// Max entries in Leios offer maps before tracking degrades.
const MAX_LEIOS_OFFERS: usize = 100_000;

use std::collections::{HashMap, HashSet};
use std::time::Duration;

use crate::peer::PeerId;

/// Result of processing a Leios offer.
pub(crate) enum OfferResult {
    /// First time seeing this item — forward to the application.
    New,
    /// Already seen — deduplicated.
    Duplicate,
    /// Seen set at capacity — forwarding without dedup.
    AtCapacity,
}

/// Result of processing a Leios vote batch.
pub(crate) struct VoteBatchResult {
    /// Votes that haven't been seen before (or all if at capacity).
    pub unseen: Vec<(u64, Vec<u8>)>,
    /// True if the seen set was at capacity (fail-open).
    pub at_capacity: bool,
}

/// Peer RTT lookup — the coordinator provides this so we don't need
/// to store a full peer map reference.
pub(crate) trait PeerRttLookup {
    fn rtt(&self, peer: PeerId) -> Option<Duration>;
    fn peer_exists(&self, peer: PeerId) -> bool;
}

/// Leios deduplication, offer tracking, and fetch routing state.
pub(crate) struct LeiosTracker {
    dedup_window: u64,
    /// Seen Leios EB offers: (slot, hash). Deduplicated before forwarding.
    seen_blocks: HashSet<(u64, [u8; 32])>,
    /// Seen Leios TX offers: (slot, hash).
    seen_txs: HashSet<(u64, [u8; 32])>,
    /// Seen individual vote offers: (slot, voter_id).
    seen_votes: HashSet<(u64, Vec<u8>)>,
    /// Highest slot seen across all Leios offers (for pruning).
    max_slot: u64,
    /// Which peers offered which Leios blocks: (slot, hash) -> offering peers.
    block_offers: HashMap<(u64, [u8; 32]), Vec<PeerId>>,
    /// Which peers offered which Leios TXs.
    txs_offers: HashMap<(u64, [u8; 32]), Vec<PeerId>>,
    /// Which peers offered which votes: (slot, voter_id) -> offering peers.
    vote_offers: HashMap<(u64, Vec<u8>), Vec<PeerId>>,
    /// Pending Leios block fetches: (slot, hash) -> peer fetching it.
    pending_block_fetches: HashMap<(u64, [u8; 32]), PeerId>,
    /// Pending Leios TX fetches: (slot, hash) -> peer fetching it.
    pending_txs_fetches: HashMap<(u64, [u8; 32]), PeerId>,
    /// Peers that have been asked for an EB's txs already, across the
    /// current sequence of attempts. A retry on partial response should
    /// pick a peer not in this set. Cleared by `clear_txs_attempts` once
    /// the requester is satisfied (or gives up).
    txs_attempts: HashMap<(u64, [u8; 32]), HashSet<PeerId>>,
    /// Pending Leios vote fetches: (slot, voter_id) -> peer fetching them.
    pending_vote_fetches: HashMap<(u64, Vec<u8>), PeerId>,
}

impl LeiosTracker {
    pub fn new(dedup_window: u64) -> Self {
        Self {
            dedup_window,
            seen_blocks: HashSet::new(),
            seen_txs: HashSet::new(),
            seen_votes: HashSet::new(),
            max_slot: 0,
            block_offers: HashMap::new(),
            txs_offers: HashMap::new(),
            vote_offers: HashMap::new(),
            pending_block_fetches: HashMap::new(),
            pending_txs_fetches: HashMap::new(),
            pending_vote_fetches: HashMap::new(),
            txs_attempts: HashMap::new(),
        }
    }

    /// Update the max slot and prune old entries from dedup sets and offer maps.
    fn update_slot(&mut self, slot: u64) {
        if slot > self.max_slot {
            self.max_slot = slot;
            let cutoff = slot.saturating_sub(self.dedup_window);
            self.seen_blocks.retain(|(s, _)| *s >= cutoff);
            self.seen_txs.retain(|(s, _)| *s >= cutoff);
            self.seen_votes.retain(|(s, _)| *s >= cutoff);
            self.block_offers.retain(|(s, _), _| *s >= cutoff);
            self.txs_offers.retain(|(s, _), _| *s >= cutoff);
            self.vote_offers.retain(|(s, _), _| *s >= cutoff);
            self.txs_attempts.retain(|(s, _), _| *s >= cutoff);
        }
    }

    /// Process a block offer from a peer. Returns whether the offer is new.
    pub fn handle_block_offer(&mut self, slot: u64, hash: [u8; 32], peer: PeerId) -> OfferResult {
        self.update_slot(slot);
        if self.block_offers.len() < MAX_LEIOS_OFFERS {
            let offers = self.block_offers.entry((slot, hash)).or_default();
            if !offers.contains(&peer) {
                offers.push(peer);
            }
        }
        if self.seen_blocks.len() < MAX_LEIOS_SEEN {
            if self.seen_blocks.insert((slot, hash)) {
                OfferResult::New
            } else {
                OfferResult::Duplicate
            }
        } else {
            OfferResult::AtCapacity
        }
    }

    /// Process a TX offer from a peer. Returns whether the offer is new.
    pub fn handle_txs_offer(&mut self, slot: u64, hash: [u8; 32], peer: PeerId) -> OfferResult {
        self.update_slot(slot);
        if self.txs_offers.len() < MAX_LEIOS_OFFERS {
            let offers = self.txs_offers.entry((slot, hash)).or_default();
            if !offers.contains(&peer) {
                offers.push(peer);
            }
        }
        if self.seen_txs.len() < MAX_LEIOS_SEEN {
            if self.seen_txs.insert((slot, hash)) {
                OfferResult::New
            } else {
                OfferResult::Duplicate
            }
        } else {
            OfferResult::AtCapacity
        }
    }

    /// Process a vote batch from a peer. Returns the unseen votes.
    pub fn handle_vote_batch(
        &mut self,
        votes: Vec<(u64, Vec<u8>)>,
        peer: PeerId,
    ) -> VoteBatchResult {
        let seen_at_capacity = self.seen_votes.len() >= MAX_LEIOS_SEEN;
        let offers_at_capacity = self.vote_offers.len() >= MAX_LEIOS_OFFERS;
        let mut unseen = Vec::new();
        for (slot, voter_id) in votes {
            self.update_slot(slot);
            if !offers_at_capacity {
                let offers = self
                    .vote_offers
                    .entry((slot, voter_id.clone()))
                    .or_default();
                if !offers.contains(&peer) {
                    offers.push(peer);
                }
            }
            let is_new = seen_at_capacity || self.seen_votes.insert((slot, voter_id.clone()));
            if is_new {
                unseen.push((slot, voter_id));
            }
        }
        VoteBatchResult {
            unseen,
            at_capacity: seen_at_capacity,
        }
    }

    /// Record that a block fetch completed.
    pub fn complete_block_fetch(&mut self, slot: u64, hash: [u8; 32]) {
        self.pending_block_fetches.remove(&(slot, hash));
    }

    /// Record that a TX fetch completed.
    pub fn complete_txs_fetch(&mut self, slot: u64, hash: [u8; 32]) {
        self.pending_txs_fetches.remove(&(slot, hash));
    }

    /// Record that a vote fetch completed for a peer.
    pub fn complete_vote_fetch(&mut self, peer: PeerId) {
        self.pending_vote_fetches.retain(|_, id| *id != peer);
    }

    /// Find the lowest-RTT peer from a list of candidates.
    fn best_peer_by_rtt(
        &self,
        candidates: &[PeerId],
        lookup: &dyn PeerRttLookup,
    ) -> Option<PeerId> {
        candidates
            .iter()
            .filter(|id| lookup.peer_exists(**id))
            .min_by_key(|id| lookup.rtt(**id).unwrap_or(Duration::from_secs(999)))
            .copied()
    }

    /// Pick the best peer to fetch a Leios block from. Returns None if already
    /// pending or no peer is available.
    pub fn pick_block_fetch_peer(
        &mut self,
        slot: u64,
        hash: [u8; 32],
        lookup: &dyn PeerRttLookup,
    ) -> Option<PeerId> {
        let key = (slot, hash);
        if self.pending_block_fetches.contains_key(&key) {
            return None;
        }
        let candidates = self.block_offers.get(&key).cloned().unwrap_or_default();
        let best = self.best_peer_by_rtt(&candidates, lookup)?;
        self.pending_block_fetches.insert(key, best);
        Some(best)
    }

    /// Pick the best peer to fetch Leios TXs from. Returns None if already
    /// pending, or if every offering peer has already been tried (i.e.
    /// the attempts set covers all candidates). Records the chosen peer
    /// in `txs_attempts` so a subsequent retry will skip it.
    pub fn pick_txs_fetch_peer(
        &mut self,
        slot: u64,
        hash: [u8; 32],
        lookup: &dyn PeerRttLookup,
    ) -> Option<PeerId> {
        let key = (slot, hash);
        if self.pending_txs_fetches.contains_key(&key) {
            return None;
        }
        let attempted: HashSet<PeerId> = self.txs_attempts.get(&key).cloned().unwrap_or_default();
        let candidates: Vec<PeerId> = self
            .txs_offers
            .get(&key)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|p| !attempted.contains(p))
            .collect();
        let best = self.best_peer_by_rtt(&candidates, lookup)?;
        self.pending_txs_fetches.insert(key, best);
        self.txs_attempts.entry(key).or_default().insert(best);
        Some(best)
    }

    /// Clear the attempts set for an EB's tx fetches. Call when the
    /// requester is fully satisfied (every requested index received) or
    /// has decided to give up. Currently unused by the coordinator —
    /// stale entries are reaped by `update_slot` once the EB ages out
    /// of the dedup window. Kept as the eventual hook for an explicit
    /// "request complete" signal.
    #[allow(dead_code)]
    pub fn clear_txs_attempts(&mut self, slot: u64, hash: [u8; 32]) {
        self.txs_attempts.remove(&(slot, hash));
    }

    /// Pick the best peer for each vote and return grouped by peer.
    /// Skips already-pending votes.
    pub fn pick_vote_fetch_peers(
        &mut self,
        votes: Vec<(u64, Vec<u8>)>,
        lookup: &dyn PeerRttLookup,
    ) -> HashMap<PeerId, Vec<(u64, Vec<u8>)>> {
        let mut by_peer: HashMap<PeerId, Vec<(u64, Vec<u8>)>> = HashMap::new();
        for (slot, voter_id) in votes {
            let key = (slot, voter_id.clone());
            if self.pending_vote_fetches.contains_key(&key) {
                continue;
            }
            let candidates = self.vote_offers.get(&key).cloned().unwrap_or_default();
            if let Some(best) = self.best_peer_by_rtt(&candidates, lookup) {
                self.pending_vote_fetches.insert(key, best);
                by_peer.entry(best).or_default().push((slot, voter_id));
            }
        }
        by_peer
    }

    /// Remove all tracking for a peer that disconnected.
    pub fn remove_peer(&mut self, peer: PeerId) {
        for offers in self.block_offers.values_mut() {
            offers.retain(|id| *id != peer);
        }
        for offers in self.txs_offers.values_mut() {
            offers.retain(|id| *id != peer);
        }
        for offers in self.vote_offers.values_mut() {
            offers.retain(|id| *id != peer);
        }
        self.pending_block_fetches.retain(|_, id| *id != peer);
        self.pending_txs_fetches.retain(|_, id| *id != peer);
        self.pending_vote_fetches.retain(|_, id| *id != peer);
        for attempts in self.txs_attempts.values_mut() {
            attempts.remove(&peer);
        }
    }

    // --- Test accessors ---

    #[cfg(test)]
    pub fn block_offers(&self) -> &HashMap<(u64, [u8; 32]), Vec<PeerId>> {
        &self.block_offers
    }

    #[cfg(test)]
    pub fn seen_blocks(&self) -> &HashSet<(u64, [u8; 32])> {
        &self.seen_blocks
    }

    #[cfg(test)]
    pub fn pending_block_fetches(&self) -> &HashMap<(u64, [u8; 32]), PeerId> {
        &self.pending_block_fetches
    }

    #[cfg(test)]
    pub fn pending_txs_fetches(&self) -> &HashMap<(u64, [u8; 32]), PeerId> {
        &self.pending_txs_fetches
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Simple RTT lookup for tests.
    struct TestPeers {
        rtts: HashMap<PeerId, Option<Duration>>,
    }

    impl PeerRttLookup for TestPeers {
        fn rtt(&self, peer: PeerId) -> Option<Duration> {
            self.rtts.get(&peer).copied().flatten()
        }
        fn peer_exists(&self, peer: PeerId) -> bool {
            self.rtts.contains_key(&peer)
        }
    }

    fn test_hash() -> [u8; 32] {
        let mut h = [0u8; 32];
        h[0] = 0xAB;
        h
    }

    fn test_hash2() -> [u8; 32] {
        let mut h = [0u8; 32];
        h[0] = 0xCD;
        h
    }

    #[test]
    fn block_offer_dedup() {
        let mut tracker = LeiosTracker::new(1000);
        let peer_a = PeerId(0);
        let peer_b = PeerId(1);
        let hash = test_hash();

        // First offer is new.
        assert!(matches!(
            tracker.handle_block_offer(100, hash, peer_a),
            OfferResult::New
        ));

        // Same offer from another peer is a duplicate.
        assert!(matches!(
            tracker.handle_block_offer(100, hash, peer_b),
            OfferResult::Duplicate
        ));

        // Both peers should be tracked as offerers.
        let offerers = tracker.block_offers().get(&(100, hash)).unwrap();
        assert_eq!(offerers.len(), 2);
    }

    #[test]
    fn txs_offer_tracked_separately() {
        let mut tracker = LeiosTracker::new(1000);
        let peer_a = PeerId(0);
        let hash = test_hash();

        assert!(matches!(
            tracker.handle_txs_offer(50, hash, peer_a),
            OfferResult::New
        ));
        // Block offer for same key is independent.
        assert!(matches!(
            tracker.handle_block_offer(50, hash, peer_a),
            OfferResult::New
        ));
    }

    #[test]
    fn vote_dedup_partial() {
        let mut tracker = LeiosTracker::new(1000);
        let peer_a = PeerId(0);
        let peer_b = PeerId(1);

        // Peer A offers votes (1, "aa") and (2, "bb").
        let result = tracker.handle_vote_batch(vec![(1, vec![0xAA]), (2, vec![0xBB])], peer_a);
        assert_eq!(result.unseen.len(), 2);

        // Peer B offers votes (2, "bb") and (3, "cc") — overlap on (2, "bb").
        let result = tracker.handle_vote_batch(vec![(2, vec![0xBB]), (3, vec![0xCC])], peer_b);
        assert_eq!(result.unseen.len(), 1);
        assert_eq!(result.unseen[0], (3, vec![0xCC]));
    }

    #[test]
    fn fetch_routing_by_rtt() {
        let mut tracker = LeiosTracker::new(1000);
        let peer_a = PeerId(0);
        let peer_b = PeerId(1);
        let hash = test_hash();

        tracker.handle_block_offer(10, hash, peer_a);
        tracker.handle_block_offer(10, hash, peer_b);

        let peers = TestPeers {
            rtts: HashMap::from([
                (peer_a, Some(Duration::from_millis(200))),
                (peer_b, Some(Duration::from_millis(50))),
            ]),
        };

        // Should pick peer_b (lower RTT).
        let best = tracker.pick_block_fetch_peer(10, hash, &peers).unwrap();
        assert_eq!(best, peer_b);
    }

    #[test]
    fn pending_fetch_dedup() {
        let mut tracker = LeiosTracker::new(1000);
        let peer_a = PeerId(0);
        let hash = test_hash();

        tracker.handle_block_offer(10, hash, peer_a);

        let peers = TestPeers {
            rtts: HashMap::from([(peer_a, Some(Duration::from_millis(10)))]),
        };

        // First fetch succeeds.
        assert!(tracker.pick_block_fetch_peer(10, hash, &peers).is_some());
        // Second fetch for same block returns None (already pending).
        assert!(tracker.pick_block_fetch_peer(10, hash, &peers).is_none());
    }

    #[test]
    fn pending_fetch_cleanup_on_peer_removal() {
        let mut tracker = LeiosTracker::new(1000);
        let peer_a = PeerId(0);
        let hash = test_hash();

        tracker.handle_block_offer(10, hash, peer_a);

        let peers = TestPeers {
            rtts: HashMap::from([(peer_a, Some(Duration::from_millis(10)))]),
        };

        tracker.pick_block_fetch_peer(10, hash, &peers);
        assert!(!tracker.pending_block_fetches().is_empty());

        tracker.remove_peer(peer_a);

        assert!(tracker.pending_block_fetches().is_empty());
        let offerers = tracker
            .block_offers()
            .get(&(10, hash))
            .map(|v| v.len())
            .unwrap_or(0);
        assert_eq!(offerers, 0);
    }

    #[test]
    fn seen_set_pruning() {
        let mut tracker = LeiosTracker::new(10);
        let peer_a = PeerId(0);
        let hash = test_hash();

        // Offer at slot 1.
        assert!(matches!(
            tracker.handle_block_offer(1, hash, peer_a),
            OfferResult::New
        ));

        // Offer at slot 20 — triggers pruning (window=10, cutoff=10).
        let hash2 = test_hash2();
        assert!(matches!(
            tracker.handle_block_offer(20, hash2, peer_a),
            OfferResult::New
        ));

        // Slot 1 should have been pruned.
        assert!(!tracker.seen_blocks().contains(&(1, hash)));

        // Re-offer (1, hash) — should be treated as new since pruned.
        assert!(matches!(
            tracker.handle_block_offer(1, hash, peer_a),
            OfferResult::New
        ));
    }

    #[test]
    fn fetch_block_txs_routing() {
        let mut tracker = LeiosTracker::new(1000);
        let peer_a = PeerId(0);
        let peer_b = PeerId(1);
        let hash = test_hash();

        tracker.handle_txs_offer(5, hash, peer_a);
        tracker.handle_txs_offer(5, hash, peer_b);

        let peers = TestPeers {
            rtts: HashMap::from([
                (peer_a, Some(Duration::from_millis(200))),
                (peer_b, Some(Duration::from_millis(30))),
            ]),
        };

        // Should pick peer_b (lower RTT).
        let best = tracker.pick_txs_fetch_peer(5, hash, &peers).unwrap();
        assert_eq!(best, peer_b);
        assert!(tracker.pending_txs_fetches().contains_key(&(5, hash)));
    }

    #[test]
    fn pick_txs_fetch_peer_skips_already_attempted() {
        let mut tracker = LeiosTracker::new(1000);
        let peer_a = PeerId(0);
        let peer_b = PeerId(1);
        let peer_c = PeerId(2);
        let hash = test_hash();

        for p in [peer_a, peer_b, peer_c] {
            tracker.handle_txs_offer(7, hash, p);
        }
        let peers = TestPeers {
            rtts: HashMap::from([
                (peer_a, Some(Duration::from_millis(20))),
                (peer_b, Some(Duration::from_millis(50))),
                (peer_c, Some(Duration::from_millis(80))),
            ]),
        };

        // First pick: peer_a (lowest RTT).
        let first = tracker.pick_txs_fetch_peer(7, hash, &peers).unwrap();
        assert_eq!(first, peer_a);
        // Mark complete so a retry can happen.
        tracker.complete_txs_fetch(7, hash);

        // Second pick: peer_b (peer_a is in attempts, skipped).
        let second = tracker.pick_txs_fetch_peer(7, hash, &peers).unwrap();
        assert_eq!(second, peer_b);
        tracker.complete_txs_fetch(7, hash);

        // Third pick: peer_c.
        let third = tracker.pick_txs_fetch_peer(7, hash, &peers).unwrap();
        assert_eq!(third, peer_c);
        tracker.complete_txs_fetch(7, hash);

        // Fourth attempt: every peer is in the attempts set → None.
        assert!(tracker.pick_txs_fetch_peer(7, hash, &peers).is_none());
    }

    #[test]
    fn clear_txs_attempts_resets_eligibility() {
        let mut tracker = LeiosTracker::new(1000);
        let peer_a = PeerId(0);
        let hash = test_hash();
        tracker.handle_txs_offer(3, hash, peer_a);
        let peers = TestPeers {
            rtts: HashMap::from([(peer_a, Some(Duration::from_millis(20)))]),
        };

        let _first = tracker.pick_txs_fetch_peer(3, hash, &peers).unwrap();
        tracker.complete_txs_fetch(3, hash);
        // Without clear, the only candidate is in attempts → no pick.
        assert!(tracker.pick_txs_fetch_peer(3, hash, &peers).is_none());

        // After clear, peer is eligible again.
        tracker.clear_txs_attempts(3, hash);
        let again = tracker.pick_txs_fetch_peer(3, hash, &peers).unwrap();
        assert_eq!(again, peer_a);
    }

    #[test]
    fn txs_attempts_pruned_when_slot_ages_out() {
        let mut tracker = LeiosTracker::new(10);
        let peer_a = PeerId(0);
        let hash = test_hash();
        tracker.handle_txs_offer(1, hash, peer_a);
        let peers = TestPeers {
            rtts: HashMap::from([(peer_a, Some(Duration::from_millis(20)))]),
        };
        let _ = tracker.pick_txs_fetch_peer(1, hash, &peers).unwrap();
        tracker.complete_txs_fetch(1, hash);

        // Advance past the dedup window (window=10, cutoff at slot 20 = 10).
        let hash2 = test_hash2();
        tracker.handle_txs_offer(20, hash2, peer_a);

        // Re-offer at slot 1 should now find no attempts entry.
        tracker.handle_txs_offer(1, hash, peer_a);
        let revived = tracker.pick_txs_fetch_peer(1, hash, &peers).unwrap();
        assert_eq!(revived, peer_a);
    }
}
