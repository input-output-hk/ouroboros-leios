//! Per-peer candidate chain tracking (PeerChain, PeerChainEntry, PeerChainAnchor).

use std::collections::VecDeque;

use net_core::types::Point;

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
    pub(super) entries: VecDeque<PeerChainEntry>,
    pub(super) cap: usize,
    /// The ChainSync intersection point — a guaranteed common ancestor
    /// between the local chain and this peer's chain. Set when
    /// `IntersectionFound` arrives, persists through rollbacks, replaced
    /// on reconnect (new intersection), dropped on disconnect.
    pub(super) anchor: Option<PeerChainAnchor>,
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

#[cfg(test)]
mod tests {
    use super::*;

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
}
