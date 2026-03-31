//! In-memory chain state shared between the coordinator and server-side
//! protocol handlers.
//!
//! The coordinator writes (appends blocks, performs rollbacks).
//! Server-side protocol handlers read (intersection lookups, block ranges,
//! subscribe to change notifications).

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
            }),
            notify: notify_sender,
        });
        (store, notify_receiver)
    }

    /// Append a block to the chain. Evicts the oldest block if over capacity.
    /// Returns `false` if the point is already stored (no-op).
    pub fn append_block(&self, point: Point, header: WrappedHeader, body: BlockBody) -> bool {
        let mut inner = self.inner.lock().unwrap();
        if inner.blocks.iter().any(|b| b.point == point) {
            return false;
        }
        inner.block_no += 1;
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
        let start = inner.blocks.iter().position(|b| b.point == *from);
        let end = inner.blocks.iter().position(|b| b.point == *to);
        match (start, end) {
            (Some(s), Some(e)) if s <= e => inner.blocks.range(s..=e).cloned().collect(),
            _ => Vec::new(),
        }
    }

    /// Check if the given read_index is still valid (within the chain).
    pub fn is_valid_index(&self, index: Option<usize>) -> bool {
        let inner = self.inner.lock().unwrap();
        match index {
            None => true, // Origin is always valid
            Some(i) => i < inner.blocks.len(),
        }
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
        store.append_block(p1.clone(), h1, b1);

        let tip = store.tip();
        assert_eq!(tip.point, p1);
        assert_eq!(tip.block_no, 1);

        let (p2, h2, b2) = make_block(2);
        store.append_block(p2.clone(), h2, b2);
        let tip = store.tip();
        assert_eq!(tip.point, p2);
        assert_eq!(tip.block_no, 2);
    }

    #[test]
    fn append_deduplicates_by_point() {
        let (store, _rx) = ChainStore::new(100);
        let (p1, h1, b1) = make_block(1);
        assert!(store.append_block(p1.clone(), h1.clone(), b1.clone()));

        // Same point again — should be a no-op.
        assert!(!store.append_block(p1, h1, b1));

        let tip = store.tip();
        assert_eq!(tip.block_no, 1);
        assert_eq!(store.stored_count(), 1);
    }

    #[test]
    fn capacity_eviction() {
        let (store, _rx) = ChainStore::new(3);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b);
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
            store.append_block(p, h, b);
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
            store.append_block(p, h, b);
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
            store.append_block(p, h, b);
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
            store.append_block(p, h, b);
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
            store.append_block(p, h, b);
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
            store.append_block(p, h, b);
        }

        let result = store.find_intersection(&[make_point(99), make_point(100)]);
        assert!(result.is_none());
    }

    #[test]
    fn blocks_after_index() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b);
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
            store.append_block(p, h, b);
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
            store.append_block(p, h, b);
        }

        let range = store.get_range(&make_point(99), &make_point(100));
        assert!(range.is_empty());
    }

    #[test]
    fn is_valid_index_after_rollback() {
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=5 {
            let (p, h, b) = make_block(slot);
            store.append_block(p, h, b);
        }

        assert!(store.is_valid_index(Some(4))); // index 4 = block 5
        store.rollback(2); // remove blocks 4, 5
        assert!(!store.is_valid_index(Some(4))); // now invalid
        assert!(store.is_valid_index(Some(2))); // index 2 = block 3, still valid
        assert!(store.is_valid_index(None)); // Origin always valid
    }

    #[tokio::test]
    async fn subscribe_notifies_on_change() {
        let (store, _rx) = ChainStore::new(100);
        let mut sub = store.subscribe();

        let (p, h, b) = make_block(1);
        store.append_block(p, h, b);

        // Should wake up.
        let result = tokio::time::timeout(std::time::Duration::from_secs(1), sub.changed()).await;
        assert!(result.is_ok());
        assert_eq!(*sub.borrow(), 1);
    }
}
