//! Multi-peer fetch routing.
//!
//! Four independently-swappable policy traits — one per traffic class
//! (Praos block fetch, Leios EB fetch, Leios EB-tx fetch, Leios vote
//! fetch) — let consumers plug in different selection algorithms per
//! channel as research evolves.  Stock implementations
//! ([`LowestRttFirst`], [`BroadcastN`]) implement all four traits, so
//! the trivial wiring case stays a single-line policy choice.
//!
//! The candidate-peer set (which peers have offered which point) and
//! pending-fetch dedup live in [`CandidateTracker`].  The wrapper
//! feeds it via `note_*_offered` whenever it observes an offer on the
//! wire; consensus state machines query it at fetch-decision time.
//!
//! RTT lookup is a borrowed [`PeerRtt`] handle passed at call time —
//! state machines don't store the oracle, so they don't need a runtime
//! handle to construct in tests.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, RwLock};
use std::time::Duration;

use crate::peer::PeerId;
use crate::types::Point;

/// Vote identity used by the candidate tracker and the vote-fetch
/// policy — `(slot, voter_id)`, matching the wire-format tuple a vote
/// announcement carries.
pub type VoteId = (u64, Vec<u8>);

/// Resolve the offer-set for a single [`VoteId`].  Borrowed by
/// [`VoteFetchPolicy::pick`] so the policy can inspect a per-vote
/// candidate list without owning the offer map.
pub type VoteCandidateLookup<'a> = dyn Fn(&VoteId) -> Vec<PeerId> + 'a;

// ---------------------------------------------------------------------------
// Oracles
// ---------------------------------------------------------------------------

/// Per-peer round-trip-time lookup.  The wrapper implements this from
/// whatever live measurement source it has (KeepAlive ping for net-rs,
/// fixed mock for sim-rs).  `None` means the wrapper hasn't measured a
/// round-trip yet.
pub trait PeerRtt {
    fn rtt(&self, peer: PeerId) -> Option<Duration>;
}

/// Convenience impl: every peer reports the same RTT.  Useful for sim
/// scenarios where RTT isn't modeled, and for tests.
pub struct UniformRtt(pub Duration);

impl PeerRtt for UniformRtt {
    fn rtt(&self, _peer: PeerId) -> Option<Duration> {
        Some(self.0)
    }
}

/// Concurrent-friendly RTT oracle backed by a shared map.
///
/// The wrapper's network actor writes per-peer measurements via
/// [`Self::set`] (typically from a KeepAlive ping handler); consensus
/// state machines read at fetch-decision time via the [`PeerRtt`]
/// impl.  Cheap to clone — internally an `Arc` — so the same cache
/// can back both writer and readers.
#[derive(Clone, Default)]
pub struct PeerRttCache {
    inner: Arc<RwLock<BTreeMap<PeerId, Duration>>>,
}

impl PeerRttCache {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a measurement.
    pub fn set(&self, peer: PeerId, rtt: Duration) {
        if let Ok(mut g) = self.inner.write() {
            g.insert(peer, rtt);
        }
    }

    /// Drop a peer's measurement on disconnect.
    pub fn forget(&self, peer: PeerId) {
        if let Ok(mut g) = self.inner.write() {
            g.remove(&peer);
        }
    }

    /// Number of peers with a recorded measurement.  Useful for tests
    /// and for telemetry; not part of the [`PeerRtt`] read surface.
    pub fn len(&self) -> usize {
        self.inner.read().map(|g| g.len()).unwrap_or(0)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl PeerRtt for PeerRttCache {
    fn rtt(&self, peer: PeerId) -> Option<Duration> {
        self.inner.read().ok()?.get(&peer).copied()
    }
}

// ---------------------------------------------------------------------------
// Policy traits
// ---------------------------------------------------------------------------

/// Pick the peer(s) to issue a Praos `BlockFetch` request to.
pub trait BlockFetchPolicy {
    fn pick(
        &self,
        point: &Point,
        candidates: &[PeerId],
        rtt: &dyn PeerRtt,
    ) -> Vec<PeerId>;
}

/// Pick the peer(s) to fetch a Leios EB body from.
pub trait EbFetchPolicy {
    fn pick(
        &self,
        point: &Point,
        candidates: &[PeerId],
        rtt: &dyn PeerRtt,
    ) -> Vec<PeerId>;
}

/// Pick the peer(s) to fetch Leios EB transactions from, given the
/// bitmap of indices we still need.
pub trait EbTxsFetchPolicy {
    fn pick(
        &self,
        point: &Point,
        bitmap: &BTreeMap<u16, u64>,
        candidates: &[PeerId],
        rtt: &dyn PeerRtt,
    ) -> Vec<PeerId>;
}

/// Group a list of vote ids by the peer to fetch each from.  A single
/// vote id can be assigned to one peer; the policy decides how to
/// fan a batch out across the candidate set.
pub trait VoteFetchPolicy {
    fn pick(
        &self,
        votes: &[VoteId],
        candidates_for: &VoteCandidateLookup<'_>,
        rtt: &dyn PeerRtt,
    ) -> BTreeMap<PeerId, Vec<VoteId>>;
}

// ---------------------------------------------------------------------------
// Stock policies
// ---------------------------------------------------------------------------

/// Single-peer policy: pick the candidate with the lowest measured
/// RTT.  Peers without a measured RTT sort last (treated as effectively
/// infinite latency).  Returns an empty vector when no candidates exist.
pub struct LowestRttFirst;

impl LowestRttFirst {
    fn pick_one(candidates: &[PeerId], rtt: &dyn PeerRtt) -> Vec<PeerId> {
        candidates
            .iter()
            .min_by_key(|p| rtt.rtt(**p).unwrap_or(Duration::from_secs(999)))
            .copied()
            .map(|p| vec![p])
            .unwrap_or_default()
    }
}

impl BlockFetchPolicy for LowestRttFirst {
    fn pick(&self, _: &Point, candidates: &[PeerId], rtt: &dyn PeerRtt) -> Vec<PeerId> {
        Self::pick_one(candidates, rtt)
    }
}

impl EbFetchPolicy for LowestRttFirst {
    fn pick(&self, _: &Point, candidates: &[PeerId], rtt: &dyn PeerRtt) -> Vec<PeerId> {
        Self::pick_one(candidates, rtt)
    }
}

impl EbTxsFetchPolicy for LowestRttFirst {
    fn pick(
        &self,
        _: &Point,
        _: &BTreeMap<u16, u64>,
        candidates: &[PeerId],
        rtt: &dyn PeerRtt,
    ) -> Vec<PeerId> {
        Self::pick_one(candidates, rtt)
    }
}

impl VoteFetchPolicy for LowestRttFirst {
    fn pick(
        &self,
        votes: &[VoteId],
        candidates_for: &VoteCandidateLookup<'_>,
        rtt: &dyn PeerRtt,
    ) -> BTreeMap<PeerId, Vec<VoteId>> {
        let mut grouped: BTreeMap<PeerId, Vec<(u64, Vec<u8>)>> = BTreeMap::new();
        for vote in votes {
            let candidates = candidates_for(vote);
            if let Some(picked) = LowestRttFirst::pick_one(&candidates, rtt).first() {
                grouped.entry(*picked).or_default().push(vote.clone());
            }
        }
        grouped
    }
}

/// Fan-out policy: send the request to the `n` candidates with the
/// lowest measured RTT.  `n = 1` degenerates to "request from first";
/// `n = usize::MAX` degenerates to "request from all".  Useful for
/// research scenarios that trade extra bandwidth for lower
/// completion-time tail latency.
pub struct BroadcastN {
    pub n: usize,
}

impl BroadcastN {
    pub fn one() -> Self {
        Self { n: 1 }
    }

    pub fn all() -> Self {
        Self { n: usize::MAX }
    }

    fn pick_n(&self, candidates: &[PeerId], rtt: &dyn PeerRtt) -> Vec<PeerId> {
        if self.n == 0 || candidates.is_empty() {
            return Vec::new();
        }
        let mut sorted: Vec<PeerId> = candidates.to_vec();
        sorted.sort_by_key(|p| rtt.rtt(*p).unwrap_or(Duration::from_secs(999)));
        sorted.truncate(self.n);
        sorted
    }
}

impl BlockFetchPolicy for BroadcastN {
    fn pick(&self, _: &Point, candidates: &[PeerId], rtt: &dyn PeerRtt) -> Vec<PeerId> {
        self.pick_n(candidates, rtt)
    }
}

impl EbFetchPolicy for BroadcastN {
    fn pick(&self, _: &Point, candidates: &[PeerId], rtt: &dyn PeerRtt) -> Vec<PeerId> {
        self.pick_n(candidates, rtt)
    }
}

impl EbTxsFetchPolicy for BroadcastN {
    fn pick(
        &self,
        _: &Point,
        _: &BTreeMap<u16, u64>,
        candidates: &[PeerId],
        rtt: &dyn PeerRtt,
    ) -> Vec<PeerId> {
        self.pick_n(candidates, rtt)
    }
}

impl VoteFetchPolicy for BroadcastN {
    fn pick(
        &self,
        votes: &[VoteId],
        candidates_for: &VoteCandidateLookup<'_>,
        rtt: &dyn PeerRtt,
    ) -> BTreeMap<PeerId, Vec<VoteId>> {
        let mut grouped: BTreeMap<PeerId, Vec<(u64, Vec<u8>)>> = BTreeMap::new();
        for vote in votes {
            let candidates = candidates_for(vote);
            for picked in self.pick_n(&candidates, rtt) {
                grouped.entry(picked).or_default().push(vote.clone());
            }
        }
        grouped
    }
}

// ---------------------------------------------------------------------------
// Candidate tracker
// ---------------------------------------------------------------------------

/// Per-resource offer map + pending-fetch dedup + per-peer retry-skip.
/// The wrapper feeds offers in via `note_*_offered`; consensus
/// machines query candidates and start/finish fetches against the
/// same instance.
///
/// All fields are `BTreeMap`/`BTreeSet` to keep iteration
/// deterministic — sim-rs replays runs from a seed and can't tolerate
/// `HashMap` ordering.
#[derive(Default)]
pub struct CandidateTracker {
    block_offers: BTreeMap<Point, BTreeSet<PeerId>>,
    eb_offers: BTreeMap<Point, BTreeSet<PeerId>>,
    eb_txs_offers: BTreeMap<Point, BTreeSet<PeerId>>,
    vote_offers: BTreeMap<VoteId, BTreeSet<PeerId>>,

    pending_block_fetches: BTreeSet<Point>,
    pending_eb_fetches: BTreeSet<Point>,
    pending_eb_txs_fetches: BTreeSet<Point>,
    pending_vote_fetches: BTreeSet<VoteId>,

    /// Per-EB set of peers we've already asked for EB-txs.  Used to
    /// skip a peer on retry after a partial response.
    eb_txs_attempts: BTreeMap<Point, BTreeSet<PeerId>>,
}

impl CandidateTracker {
    pub fn new() -> Self {
        Self::default()
    }

    // -- Offer recording ----------------------------------------------------

    /// Record that `peer` offered the Praos block at `point`.
    pub fn note_block_offered(&mut self, point: Point, peer: PeerId) {
        self.block_offers.entry(point).or_default().insert(peer);
    }

    /// Record that `peer` offered the Leios EB at `point`.
    pub fn note_eb_offered(&mut self, point: Point, peer: PeerId) {
        self.eb_offers.entry(point).or_default().insert(peer);
    }

    /// Record that `peer` offered EB transactions for `point`.
    pub fn note_eb_txs_offered(&mut self, point: Point, peer: PeerId) {
        self.eb_txs_offers.entry(point).or_default().insert(peer);
    }

    /// Record that `peer` offered a vote bundle.
    pub fn note_vote_offered(&mut self, vote: VoteId, peer: PeerId) {
        self.vote_offers.entry(vote).or_default().insert(peer);
    }

    // -- Candidate queries --------------------------------------------------

    pub fn block_candidates(&self, point: &Point) -> Vec<PeerId> {
        self.block_offers
            .get(point)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default()
    }

    pub fn eb_candidates(&self, point: &Point) -> Vec<PeerId> {
        self.eb_offers
            .get(point)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default()
    }

    /// EB-txs candidates excluding any peer we've already tried for
    /// this EB (used to advance the retry-after-partial-response flow).
    pub fn eb_txs_candidates(&self, point: &Point) -> Vec<PeerId> {
        let attempted = self.eb_txs_attempts.get(point);
        self.eb_txs_offers
            .get(point)
            .map(|s| {
                s.iter()
                    .filter(|p| attempted.is_none_or(|a| !a.contains(p)))
                    .copied()
                    .collect()
            })
            .unwrap_or_default()
    }

    pub fn vote_candidates(&self, vote: &VoteId) -> Vec<PeerId> {
        self.vote_offers
            .get(vote)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default()
    }

    // -- In-flight fetch dedup ----------------------------------------------

    /// Try to start a Praos block fetch.  Returns `false` if a fetch
    /// for this point is already in flight.
    pub fn start_block_fetch(&mut self, point: Point) -> bool {
        self.pending_block_fetches.insert(point)
    }
    pub fn finish_block_fetch(&mut self, point: &Point) {
        self.pending_block_fetches.remove(point);
    }

    pub fn start_eb_fetch(&mut self, point: Point) -> bool {
        self.pending_eb_fetches.insert(point)
    }
    pub fn finish_eb_fetch(&mut self, point: &Point) {
        self.pending_eb_fetches.remove(point);
    }

    /// Start an EB-txs fetch and record which peers were attempted.
    /// Returns `false` if a fetch for this point is already in flight.
    pub fn start_eb_txs_fetch(&mut self, point: Point, peers: &[PeerId]) -> bool {
        if !self.pending_eb_txs_fetches.insert(point.clone()) {
            return false;
        }
        let attempts = self.eb_txs_attempts.entry(point).or_default();
        for p in peers {
            attempts.insert(*p);
        }
        true
    }
    pub fn finish_eb_txs_fetch(&mut self, point: &Point) {
        self.pending_eb_txs_fetches.remove(point);
    }

    pub fn start_vote_fetch(&mut self, vote: VoteId) -> bool {
        self.pending_vote_fetches.insert(vote)
    }
    pub fn finish_vote_fetch(&mut self, vote: &VoteId) {
        self.pending_vote_fetches.remove(vote);
    }

    // -- Pruning ------------------------------------------------------------

    /// Drop a peer from every offer map and attempts set on disconnect.
    pub fn forget_peer(&mut self, peer: PeerId) {
        for offers in self.block_offers.values_mut() {
            offers.remove(&peer);
        }
        for offers in self.eb_offers.values_mut() {
            offers.remove(&peer);
        }
        for offers in self.eb_txs_offers.values_mut() {
            offers.remove(&peer);
        }
        for offers in self.vote_offers.values_mut() {
            offers.remove(&peer);
        }
        for attempts in self.eb_txs_attempts.values_mut() {
            attempts.remove(&peer);
        }
    }

    /// Drop offer / pending / attempt entries for slots strictly older
    /// than `min_slot`.  Bounds memory.  Vote keys carry their slot in
    /// the tuple, EB keys via `Point::Specific.slot`.
    pub fn prune_below_slot(&mut self, min_slot: u64) {
        self.block_offers.retain(|p, _| point_slot(p) >= min_slot);
        self.eb_offers.retain(|p, _| point_slot(p) >= min_slot);
        self.eb_txs_offers.retain(|p, _| point_slot(p) >= min_slot);
        self.vote_offers.retain(|(s, _), _| *s >= min_slot);
        self.pending_block_fetches.retain(|p| point_slot(p) >= min_slot);
        self.pending_eb_fetches.retain(|p| point_slot(p) >= min_slot);
        self.pending_eb_txs_fetches.retain(|p| point_slot(p) >= min_slot);
        self.pending_vote_fetches.retain(|(s, _)| *s >= min_slot);
        self.eb_txs_attempts.retain(|p, _| point_slot(p) >= min_slot);
    }
}

fn point_slot(p: &Point) -> u64 {
    match p {
        Point::Specific { slot, .. } => *slot,
        Point::Origin => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pid(n: u64) -> PeerId {
        PeerId(n)
    }
    fn pt(slot: u64, byte: u8) -> Point {
        Point::Specific {
            slot,
            hash: [byte; 32],
        }
    }

    struct StaticRtt(BTreeMap<PeerId, Duration>);
    impl PeerRtt for StaticRtt {
        fn rtt(&self, peer: PeerId) -> Option<Duration> {
            self.0.get(&peer).copied()
        }
    }
    fn rtts(entries: &[(u64, u64)]) -> StaticRtt {
        StaticRtt(
            entries
                .iter()
                .map(|(p, ms)| (pid(*p), Duration::from_millis(*ms)))
                .collect(),
        )
    }

    // -- LowestRttFirst -----------------------------------------------------

    #[test]
    fn lowest_rtt_first_picks_min() {
        let policy = LowestRttFirst;
        let rtt = rtts(&[(1, 50), (2, 10), (3, 30)]);
        let picked =
            BlockFetchPolicy::pick(&policy, &pt(1, 1), &[pid(1), pid(2), pid(3)], &rtt);
        assert_eq!(picked, vec![pid(2)]);
    }

    #[test]
    fn lowest_rtt_first_ranks_unmeasured_last() {
        let policy = LowestRttFirst;
        // pid(2) has no measurement → treated as effectively infinite.
        let rtt = rtts(&[(1, 50), (3, 100)]);
        let picked =
            BlockFetchPolicy::pick(&policy, &pt(1, 1), &[pid(1), pid(2), pid(3)], &rtt);
        assert_eq!(picked, vec![pid(1)]);
    }

    #[test]
    fn lowest_rtt_first_empty_candidates_returns_empty() {
        let policy = LowestRttFirst;
        let rtt = UniformRtt(Duration::from_millis(10));
        let picked = BlockFetchPolicy::pick(&policy, &pt(1, 1), &[], &rtt);
        assert!(picked.is_empty());
    }

    // -- BroadcastN ---------------------------------------------------------

    #[test]
    fn broadcast_n_one_matches_request_from_first() {
        let policy = BroadcastN::one();
        let rtt = rtts(&[(1, 50), (2, 10), (3, 30)]);
        let picked =
            BlockFetchPolicy::pick(&policy, &pt(1, 1), &[pid(1), pid(2), pid(3)], &rtt);
        assert_eq!(picked, vec![pid(2)]);
    }

    #[test]
    fn broadcast_n_two_picks_two_lowest() {
        let policy = BroadcastN { n: 2 };
        let rtt = rtts(&[(1, 50), (2, 10), (3, 30)]);
        let picked =
            BlockFetchPolicy::pick(&policy, &pt(1, 1), &[pid(1), pid(2), pid(3)], &rtt);
        // Sorted ascending by RTT: pid(2) 10ms, pid(3) 30ms.
        assert_eq!(picked, vec![pid(2), pid(3)]);
    }

    #[test]
    fn broadcast_n_all_matches_request_from_all() {
        let policy = BroadcastN::all();
        let rtt = rtts(&[(1, 50), (2, 10), (3, 30)]);
        let picked =
            BlockFetchPolicy::pick(&policy, &pt(1, 1), &[pid(1), pid(2), pid(3)], &rtt);
        // Sorted by RTT.
        assert_eq!(picked, vec![pid(2), pid(3), pid(1)]);
    }

    #[test]
    fn broadcast_n_zero_returns_empty() {
        let policy = BroadcastN { n: 0 };
        let rtt = UniformRtt(Duration::from_millis(10));
        let picked =
            BlockFetchPolicy::pick(&policy, &pt(1, 1), &[pid(1), pid(2)], &rtt);
        assert!(picked.is_empty());
    }

    // -- VoteFetchPolicy ----------------------------------------------------

    #[test]
    fn vote_fetch_groups_by_lowest_rtt_per_vote() {
        let policy = LowestRttFirst;
        let rtt = rtts(&[(1, 50), (2, 10)]);
        let votes = vec![(10u64, b"voter-a".to_vec()), (10u64, b"voter-b".to_vec())];
        let candidates_for = |v: &VoteId| {
            // voter-a is offered by both peers; voter-b only by pid(1).
            if v.1 == b"voter-a" {
                vec![pid(1), pid(2)]
            } else {
                vec![pid(1)]
            }
        };
        let grouped = VoteFetchPolicy::pick(&policy, &votes, &candidates_for, &rtt);
        // pid(2) (lower RTT) gets voter-a; pid(1) (only candidate) gets voter-b.
        assert_eq!(
            grouped.get(&pid(2)).cloned().unwrap_or_default(),
            vec![(10u64, b"voter-a".to_vec())]
        );
        assert_eq!(
            grouped.get(&pid(1)).cloned().unwrap_or_default(),
            vec![(10u64, b"voter-b".to_vec())]
        );
    }

    // -- CandidateTracker ---------------------------------------------------

    #[test]
    fn tracker_records_offers_and_returns_candidates() {
        let mut t = CandidateTracker::new();
        t.note_eb_offered(pt(10, 1), pid(1));
        t.note_eb_offered(pt(10, 1), pid(2));
        t.note_eb_offered(pt(10, 1), pid(1)); // duplicate is idempotent
        let cands = t.eb_candidates(&pt(10, 1));
        assert_eq!(cands, vec![pid(1), pid(2)]);
    }

    #[test]
    fn tracker_block_fetch_is_dedup() {
        let mut t = CandidateTracker::new();
        assert!(t.start_block_fetch(pt(1, 1)));
        assert!(!t.start_block_fetch(pt(1, 1)));
        t.finish_block_fetch(&pt(1, 1));
        assert!(t.start_block_fetch(pt(1, 1)));
    }

    #[test]
    fn tracker_eb_txs_skips_attempted_peers() {
        let mut t = CandidateTracker::new();
        t.note_eb_txs_offered(pt(10, 1), pid(1));
        t.note_eb_txs_offered(pt(10, 1), pid(2));
        t.note_eb_txs_offered(pt(10, 1), pid(3));
        // First fetch attempts pid(1) and pid(2).
        assert!(t.start_eb_txs_fetch(pt(10, 1), &[pid(1), pid(2)]));
        // After the response, the retry-eligible candidate set excludes
        // pid(1) and pid(2).
        t.finish_eb_txs_fetch(&pt(10, 1));
        let retry = t.eb_txs_candidates(&pt(10, 1));
        assert_eq!(retry, vec![pid(3)]);
    }

    #[test]
    fn tracker_forget_peer_removes_from_all_maps() {
        let mut t = CandidateTracker::new();
        t.note_block_offered(pt(1, 1), pid(1));
        t.note_eb_offered(pt(2, 2), pid(1));
        t.note_eb_txs_offered(pt(3, 3), pid(1));
        t.note_vote_offered((4, b"v".to_vec()), pid(1));
        t.forget_peer(pid(1));
        assert!(t.block_candidates(&pt(1, 1)).is_empty());
        assert!(t.eb_candidates(&pt(2, 2)).is_empty());
        assert!(t.eb_txs_candidates(&pt(3, 3)).is_empty());
        assert!(t.vote_candidates(&(4, b"v".to_vec())).is_empty());
    }

    #[test]
    fn tracker_prune_below_slot_drops_old_entries() {
        let mut t = CandidateTracker::new();
        t.note_eb_offered(pt(5, 1), pid(1));
        t.note_eb_offered(pt(15, 1), pid(2));
        t.note_vote_offered((5, b"a".to_vec()), pid(1));
        t.note_vote_offered((15, b"b".to_vec()), pid(2));
        t.prune_below_slot(10);
        assert!(t.eb_candidates(&pt(5, 1)).is_empty());
        assert_eq!(t.eb_candidates(&pt(15, 1)), vec![pid(2)]);
        assert!(t.vote_candidates(&(5, b"a".to_vec())).is_empty());
        assert_eq!(t.vote_candidates(&(15, b"b".to_vec())), vec![pid(2)]);
    }

    // -- PeerRttCache -------------------------------------------------------

    #[test]
    fn rtt_cache_round_trip() {
        let cache = PeerRttCache::new();
        cache.set(pid(1), Duration::from_millis(50));
        cache.set(pid(2), Duration::from_millis(20));
        assert_eq!(cache.rtt(pid(1)), Some(Duration::from_millis(50)));
        assert_eq!(cache.rtt(pid(2)), Some(Duration::from_millis(20)));
        assert_eq!(cache.rtt(pid(3)), None);
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn rtt_cache_forget_removes_entry() {
        let cache = PeerRttCache::new();
        cache.set(pid(1), Duration::from_millis(10));
        cache.forget(pid(1));
        assert_eq!(cache.rtt(pid(1)), None);
        assert!(cache.is_empty());
    }

    #[test]
    fn rtt_cache_clone_shares_storage() {
        let a = PeerRttCache::new();
        let b = a.clone();
        a.set(pid(1), Duration::from_millis(7));
        assert_eq!(b.rtt(pid(1)), Some(Duration::from_millis(7)));
    }

    #[test]
    fn rtt_cache_drives_lowest_rtt_first() {
        // Sanity: a populated cache makes LowestRttFirst rank by real RTT.
        let cache = PeerRttCache::new();
        cache.set(pid(1), Duration::from_millis(50));
        cache.set(pid(2), Duration::from_millis(10));
        cache.set(pid(3), Duration::from_millis(30));
        let policy = LowestRttFirst;
        let picked =
            BlockFetchPolicy::pick(&policy, &pt(1, 1), &[pid(1), pid(2), pid(3)], &cache);
        assert_eq!(picked, vec![pid(2)]);
    }
}
