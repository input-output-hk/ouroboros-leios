//! In-memory chain state shared between the coordinator and server-side
//! protocol handlers.
//!
//! The coordinator writes (appends blocks, performs rollbacks).
//! Server-side protocol handlers read (intersection lookups, block ranges,
//! subscribe to change notifications).
//!
//! # Maintained invariants
//!
//! - **Bounded capacity**: FIFO eviction when `blocks.len() > capacity`.
//! - **No duplicate points**: `append_block()` checks for existing point.
//! - **Thread safety**: all access through `Mutex<ChainStoreInner>`.
//! - **Change notification**: every mutation signals the watch channel.
//! - **Rollback truncation**: `rollback_to()` keeps the target point and
//!   everything before it; updates `last_rollback_target`.
//!
//! # Known gaps
//!
//! - **`block_no` is caller-provided**: not validated for monotonicity.
//!   Not decremented on rollback (high-water-mark semantics).
//! - **`get_range` fallback is intentionally imprecise**: when `from` is
//!   not on the local chain (peer on a different fork), returns the prefix
//!   `[0..=to]` so the peer can walk back via `prev_hash`. This can return
//!   more blocks than needed.
//! - **`intersection_candidates` may reference evicted blocks**: the
//!   exponential lookback pattern generates points from the stored VecDeque,
//!   so evicted blocks are not included, but the Origin fallback ensures
//!   intersection always succeeds eventually.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

use tokio::sync::watch;

use crate::types::{BlockBody, Point, Tip, WrappedHeader};

/// A block stored in the chain.
#[derive(Debug, Clone)]
pub struct StoredBlock {
    pub point: Point,
    pub header: WrappedHeader,
    pub body: BlockBody,
}

struct ChainStoreInner {
    blocks: VecDeque<StoredBlock>,
    capacity: usize,
    /// Running block number (monotonically increasing, not reset on eviction).
    block_no: u64,
    /// Tip point after the most recent rollback truncation. Server handlers use
    /// this as the MsgRollBackward target (the true fork point).
    last_rollback_target: Option<Point>,
}

/// Thread-safe in-memory chain state.
///
/// All methods that read or mutate the chain acquire a `Mutex` lock.
/// Operations under the lock are fast (no I/O), so contention is minimal.
/// Change notifications are delivered via a `watch::channel`.
pub struct ChainStore {
    inner: Mutex<ChainStoreInner>,
    notify: watch::Sender<u64>,
}

impl ChainStore {
    /// Create a new chain store with the given block capacity.
    ///
    /// Returns the store (wrapped in `Arc`) and a subscription receiver
    /// for change notifications.
    pub fn new(capacity: usize) -> (Arc<Self>, watch::Receiver<u64>) {
        let (notify_sender, notify_receiver) = watch::channel(0u64);
        let store = Arc::new(Self {
            inner: Mutex::new(ChainStoreInner {
                blocks: VecDeque::new(),
                capacity,
                block_no: 0,
                last_rollback_target: None,
            }),
            notify: notify_sender,
        });
        (store, notify_receiver)
    }

    /// Append a block to the chain. Evicts the oldest block if over capacity.
    /// `block_no` is the caller-provided chain height (not an internal counter).
    /// Returns `false` if the point is already stored (no-op).
    pub fn append_block(
        &self,
        point: Point,
        header: WrappedHeader,
        body: BlockBody,
        block_no: u64,
    ) -> bool {
        let mut inner = self.inner.lock().unwrap();
        if inner.blocks.iter().any(|b| b.point == point) {
            return false;
        }
        inner.block_no = block_no;
        inner.blocks.push_back(StoredBlock {
            point,
            header,
            body,
        });
        while inner.blocks.len() > inner.capacity {
            inner.blocks.pop_front();
        }
        let count = inner.block_no;
        drop(inner);
        let _ = self.notify.send(count);
        true
    }

    /// Roll back the chain to the given point. Removes all blocks after it.
    /// If the point is Origin, clears all blocks.
    /// Returns the new tip point.
    pub fn rollback_to(&self, point: &Point) -> Point {
        let mut inner = self.inner.lock().unwrap();
        if *point == Point::Origin {
            inner.blocks.clear();
            inner.last_rollback_target = Some(Point::Origin);
            drop(inner);
            let _ = self.notify.send(0);
            return Point::Origin;
        }
        // Find the position of the target point and truncate after it.
        if let Some(pos) = inner.blocks.iter().position(|b| b.point == *point) {
            inner.blocks.truncate(pos + 1);
        }
        let tip_point = inner
            .blocks
            .back()
            .map(|b| b.point.clone())
            .unwrap_or(Point::Origin);
        inner.last_rollback_target = Some(tip_point.clone());
        let count = inner.block_no;
        drop(inner);
        let _ = self.notify.send(count);
        tip_point
    }

    /// Roll back the chain by `depth` blocks. Returns the new tip point.
    pub fn rollback(&self, depth: usize) -> Point {
        let mut inner = self.inner.lock().unwrap();
        let new_len = inner.blocks.len().saturating_sub(depth);
        inner.blocks.truncate(new_len);
        let tip_point = inner
            .blocks
            .back()
            .map(|b| b.point.clone())
            .unwrap_or(Point::Origin);
        inner.last_rollback_target = Some(tip_point.clone());
        let count = inner.block_no;
        drop(inner);
        let _ = self.notify.send(count);
        tip_point
    }

    /// Get the current chain tip.
    pub fn tip(&self) -> Tip {
        let inner = self.inner.lock().unwrap();
        match inner.blocks.back() {
            Some(block) => Tip {
                point: block.point.clone(),
                block_no: inner.block_no,
            },
            None => Tip {
                point: Point::Origin,
                block_no: 0,
            },
        }
    }

    /// Find the best intersection between the given points and the chain.
    /// Points are checked in order; first match wins (so callers should
    /// order from most recent to oldest).
    ///
    /// Returns `Some((Origin, tip))` if `Origin` appears in `points` and no
    /// earlier candidate matched — this means the only common point is
    /// genesis. In the praos consensus layer, an Origin intersection maps
    /// to `anchor=None`, which currently only allows a switch when
    /// `adopted_tip_hash` is `None` (fresh node).
    pub fn find_intersection(&self, points: &[Point]) -> Option<(Point, Tip)> {
        let inner = self.inner.lock().unwrap();
        let tip = match inner.blocks.back() {
            Some(block) => Tip {
                point: block.point.clone(),
                block_no: inner.block_no,
            },
            None => Tip {
                point: Point::Origin,
                block_no: 0,
            },
        };

        for candidate in points {
            if *candidate == Point::Origin {
                return Some((Point::Origin, tip));
            }
            if inner.blocks.iter().any(|b| b.point == *candidate) {
                return Some((candidate.clone(), tip));
            }
        }
        None
    }

    /// Get the index of a point in the chain.
    /// Returns `None` for Origin (before the first block).
    pub fn index_of(&self, point: &Point) -> Option<usize> {
        let inner = self.inner.lock().unwrap();
        if *point == Point::Origin {
            return None;
        }
        inner.blocks.iter().position(|b| b.point == *point)
    }

    /// Get blocks after the given index (exclusive).
    /// `None` means Origin — returns all blocks from the beginning.
    pub fn blocks_after(&self, after_index: Option<usize>) -> Vec<StoredBlock> {
        let inner = self.inner.lock().unwrap();
        let start = match after_index {
            Some(i) => i + 1,
            None => 0,
        };
        if start >= inner.blocks.len() {
            return Vec::new();
        }
        inner.blocks.range(start..).cloned().collect()
    }

    /// Get blocks in a range (inclusive on both endpoints).
    pub fn get_range(&self, from: &Point, to: &Point) -> Vec<StoredBlock> {
        let inner = self.inner.lock().unwrap();
        let end = match inner.blocks.iter().position(|b| b.point == *to) {
            Some(e) => e,
            None => return Vec::new(),
        };
        // If `from` is on this chain, slice from there. Otherwise return the
        // whole prefix up to `to` — the client may be on a fork whose `from`
        // we don't know, and giving it the chain prefix lets it walk back
        // through prev_hash to find a common ancestor.
        let start = inner
            .blocks
            .iter()
            .position(|b| b.point == *from)
            .filter(|&s| s <= end)
            .unwrap_or(0);
        inner.blocks.range(start..=end).cloned().collect()
    }

    /// Produce ChainSync intersection candidates from the local chain,
    /// ordered newest-to-oldest: `[tip, tip-1, tip-2, tip-4, tip-8, ...]`
    /// with exponential lookback, capped at `max` points, and always ending
    /// with `Point::Origin` as the ultimate fallback.
    ///
    /// `find_intersection` returns the first candidate that matches, so
    /// newest-first ordering selects the most recent common ancestor — the
    /// shortest possible re-sync window.
    pub fn intersection_candidates(&self, max: usize) -> Vec<Point> {
        let inner = self.inner.lock().unwrap();
        let len = inner.blocks.len();
        let mut out: Vec<Point> = Vec::with_capacity(max.min(len) + 1);
        if len > 0 {
            // Tip (newest) is at `len - 1`. Walk back by 1, 2, 4, 8, ...
            // until we run out of chain or hit `max`.
            let mut offset: usize = 0;
            let mut step: usize = 1;
            while offset < len && out.len() + 1 < max {
                let idx = len - 1 - offset;
                out.push(inner.blocks[idx].point.clone());
                offset = offset.saturating_add(step);
                step = step.saturating_mul(2);
            }
        }
        out.push(Point::Origin);
        out
    }

    /// Check whether a read cursor is still valid by comparing the Point at
    /// the stored index. Returns false if the index is out of bounds OR a
    /// different block now occupies that position (rollback + re-append).
    pub fn is_valid_index(&self, index: Option<usize>, cursor_point: &Option<Point>) -> bool {
        let inner = self.inner.lock().unwrap();
        match (index, cursor_point) {
            (None, _) => true, // Origin is always valid
            (Some(i), Some(p)) => inner.blocks.get(i).is_some_and(|b| b.point == *p),
            (Some(i), None) => i < inner.blocks.len(),
        }
    }

    /// The fork point of the most recent rollback (tip after truncation).
    /// Server handlers use this as the MsgRollBackward target.
    pub fn last_rollback_target(&self) -> Option<Point> {
        self.inner.lock().unwrap().last_rollback_target.clone()
    }

    /// Subscribe to chain change notifications.
    pub fn subscribe(&self) -> watch::Receiver<u64> {
        self.notify.subscribe()
    }

    /// Get the total number of blocks that have been appended (including evicted).
    pub fn block_count(&self) -> u64 {
        self.inner.lock().unwrap().block_no
    }

    /// Get the number of blocks currently stored.
    pub fn stored_count(&self) -> usize {
        self.inner.lock().unwrap().blocks.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_point(slot: u64) -> Point {
        Point::Specific {
            slot,
            hash: [slot as u8; 32],
        }
    }

    fn make_block(slot: u64) -> (Point, WrappedHeader, BlockBody) {
        let point = make_point(slot);
        let header = WrappedHeader::opaque(vec![0xA0]);
        let body = BlockBody::opaque(vec![0xBF, 0xFF]);
        (point, header, body)
    }

    #[test]
    fn empty_chain_tip_is_origin() {
        let (store, _rx) = ChainStore::new(100);
        let tip = store.tip();
        assert_eq!(tip.point, Point::Origin);
        assert_eq!(tip.block_no, 0);
    }

    #[test]
    fn append_advances_tip() {
        let (store, _rx) = ChainStore::new(100);
        let (p1, h1, b1) = make_block(1);
        store.append_block(p1.clone(), h1, b1, 1);

        let tip = store.tip();
        assert_eq!(tip.point, p1);
        assert_eq!(tip.block_no, 1);

        let (p2, h2, b2) = make_block(2);
        store.append_block(p2.clone(), h2, b2, 2);
        let tip = store.tip();
        assert_eq!(tip.point, p2);
        assert_eq!(tip.block_no, 2);
    }

    #[test]
    fn intersection_candidates_empty_chain() {
        let (store, _rx) = ChainStore::new(100);
        let candidates = store.intersection_candidates(10);
        assert_eq!(candidates, vec![Point::Origin]);
    }

    #[test]
    fn intersection_candidates_exponential_lookback() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=20 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        // max=10 → up to 9 chain points + Origin at the end.
        // Offsets from tip: 0, 1, 3, 7, 15 (next would be 31 > 19, stop)
        // → slots: 20, 19, 17, 13, 5, then Origin.
        let candidates = store.intersection_candidates(10);
        assert_eq!(
            candidates,
            vec![
                make_point(20),
                make_point(19),
                make_point(17),
                make_point(13),
                make_point(5),
                Point::Origin,
            ]
        );
    }

    #[test]
    fn intersection_candidates_caps_at_max() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=50 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }
        let candidates = store.intersection_candidates(4);
        // 3 chain points + Origin = 4 total.
        assert_eq!(candidates.len(), 4);
        assert_eq!(candidates[0], make_point(50));
        assert_eq!(*candidates.last().unwrap(), Point::Origin);
    }

    #[test]
    fn append_deduplicates_by_point() {
        let (store, _rx) = ChainStore::new(100);
        let (p1, h1, b1) = make_block(1);
        assert!(store.append_block(p1.clone(), h1.clone(), b1.clone(), 1));

        // Same point again — should be a no-op.
        assert!(!store.append_block(p1, h1, b1, 1));

        let tip = store.tip();
        assert_eq!(tip.block_no, 1);
        assert_eq!(store.stored_count(), 1);
    }

    #[test]
    fn capacity_eviction() {
        let (store, _rx) = ChainStore::new(3);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }
        // Should have blocks 3, 4, 5 (evicted 1 and 2).
        assert_eq!(store.stored_count(), 3);
        assert_eq!(store.block_count(), 5);

        // Block 1 is gone.
        assert!(store.index_of(&make_point(1)).is_none());
        // Block 3 is first.
        assert_eq!(store.index_of(&make_point(3)), Some(0));
    }

    #[test]
    fn rollback_to_point() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        let new_tip = store.rollback_to(&make_point(3));
        assert_eq!(new_tip, make_point(3));
        assert_eq!(store.stored_count(), 3);

        // Blocks 4 and 5 are gone.
        assert!(store.index_of(&make_point(4)).is_none());
        assert!(store.index_of(&make_point(5)).is_none());
    }

    #[test]
    fn rollback_to_origin() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=3 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        let new_tip = store.rollback_to(&Point::Origin);
        assert_eq!(new_tip, Point::Origin);
        assert_eq!(store.stored_count(), 0);
    }

    #[test]
    fn rollback_by_depth() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        let new_tip = store.rollback(2);
        assert_eq!(new_tip, make_point(3));
        assert_eq!(store.stored_count(), 3);
    }

    #[test]
    fn find_intersection_matches_first() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        // Should find point 4 first (it's listed before point 2).
        let result = store.find_intersection(&[make_point(4), make_point(2)]);
        assert!(result.is_some());
        let (found, tip) = result.unwrap();
        assert_eq!(found, make_point(4));
        assert_eq!(tip.block_no, 5);
    }

    #[test]
    fn find_intersection_origin_fallback() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=3 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        let result = store.find_intersection(&[make_point(99), Point::Origin]);
        assert!(result.is_some());
        let (found, _) = result.unwrap();
        assert_eq!(found, Point::Origin);
    }

    #[test]
    fn find_intersection_no_match() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=3 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        let result = store.find_intersection(&[make_point(99), make_point(100)]);
        assert!(result.is_none());
    }

    #[test]
    fn blocks_after_index() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        // After index 2 (block at slot 3) → blocks at slots 4, 5.
        let after = store.blocks_after(Some(2));
        assert_eq!(after.len(), 2);
        assert_eq!(after[0].point, make_point(4));
        assert_eq!(after[1].point, make_point(5));

        // After None (Origin) → all blocks.
        let all = store.blocks_after(None);
        assert_eq!(all.len(), 5);
    }

    #[test]
    fn get_range_inclusive() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        let range = store.get_range(&make_point(2), &make_point(4));
        assert_eq!(range.len(), 3);
        assert_eq!(range[0].point, make_point(2));
        assert_eq!(range[2].point, make_point(4));
    }

    #[test]
    fn get_range_missing_returns_empty() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=3 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        let range = store.get_range(&make_point(99), &make_point(100));
        assert!(range.is_empty());
    }

    /// When `to` is in the store but `from` is not (because `from` is on a
    /// fork the server doesn't know about, or was rolled back), the server
    /// should still return what it has up to `to` so the client can use that
    /// to walk further back. Otherwise the client gets MsgNoBlocks and stays
    /// stuck on a fork it can't bridge.
    #[test]
    fn get_range_returns_prefix_when_from_unknown() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        // from is not in the store, to is.
        let range = store.get_range(&make_point(99), &make_point(4));
        assert!(
            !range.is_empty(),
            "should return a prefix of the chain up to `to`"
        );
        assert_eq!(range.last().unwrap().point, make_point(4));
    }

    #[test]
    fn is_valid_index_after_rollback() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        let point5 = Some(make_point(5));
        let point3 = Some(make_point(3));
        assert!(store.is_valid_index(Some(4), &point5)); // index 4 = block 5
        store.rollback(2); // remove blocks 4, 5
        assert!(!store.is_valid_index(Some(4), &point5)); // out of bounds
        assert!(store.is_valid_index(Some(2), &point3)); // block 3 still there
        assert!(store.is_valid_index(None, &None)); // Origin always valid

        // Verify last_rollback_target is block 3 (tip after truncation).
        assert_eq!(store.last_rollback_target(), Some(make_point(3)));
    }

    #[test]
    fn rollback_reappend_detected_by_point_matching() {
        // The key bug: rollback + re-append at the same index must be detected.
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b, slot);
        }

        // Cursor at index 4 = block at slot 5.
        let old_point = Some(make_point(5));
        assert!(store.is_valid_index(Some(4), &old_point));

        // Rollback removes block 5, then a different block occupies index 4.
        store.rollback(1); // remove block 5, now [1,2,3,4]
        let (p, h, b) = make_block(50); // different block at slot 50
        store.append_block(p, h, b, 50); // now [1,2,3,4,block_50]

        // Same index 4, but different block — must detect as invalid.
        assert!(!store.is_valid_index(Some(4), &old_point));

        // Rollback target is block 4 (tip after truncation).
        assert_eq!(store.last_rollback_target(), Some(make_point(4)));
    }

    #[tokio::test]
    async fn subscribe_notifies_on_change() {
        let (store, _rx) = ChainStore::new(100);
        let mut sub = store.subscribe();

        let (p, h, b) = make_block(1);
        store.append_block(p, h, b, 1);

        // Should wake up.
        let result = tokio::time::timeout(std::time::Duration::from_secs(1), sub.changed()).await;
        assert!(result.is_ok());
        assert_eq!(*sub.borrow(), 1);
    }
}
