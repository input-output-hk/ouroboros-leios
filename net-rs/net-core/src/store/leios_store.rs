//! Content-addressed store for Leios data (endorser blocks, votes).
//!
//! Separate from `ChainStore` because Leios data is keyed by `(slot, hash)`,
//! not part of a linear chain. Praos has no equivalent — all Praos data lives
//! on the chain itself.
//!
//! The coordinator writes (injects EBs, votes).
//! Server-side protocol handlers read (block lookups, vote lookups,
//! notification subscriptions).

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use tokio::sync::watch;

use crate::types::Point;

/// A notification about available Leios data, served by LeiosNotify.
#[derive(Debug, Clone)]
pub enum LeiosNotification {
    /// An endorser block is available for download.
    BlockOffer { point: Point },
    /// An EB's transactions are available for download.
    BlockTxsOffer { point: Point },
    /// Votes are available for download.
    VotesOffer { votes: Vec<(u64, Vec<u8>)> },
}

/// Key for block lookups.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct BlockKey {
    slot: u64,
    hash: [u8; 32],
}

struct LeiosStoreInner {
    /// Endorser blocks keyed by (slot, hash).
    blocks: HashMap<BlockKey, Vec<u8>>,
    /// Transactions per EB, keyed by (slot, hash).
    block_txs: HashMap<BlockKey, Vec<Vec<u8>>>,
    /// Votes keyed by (slot, voter_id).
    votes: HashMap<(u64, Vec<u8>), Vec<u8>>,
    /// Notification queue for the LeiosNotify server.
    notifications: Vec<LeiosNotification>,
    /// Max number of blocks to retain.
    capacity: usize,
    /// Monotonically increasing counter for change notifications.
    version: u64,
}

/// Thread-safe content-addressed store for Leios data.
///
/// Follows the same Mutex + watch pattern as `ChainStore`.
pub struct LeiosStore {
    inner: Mutex<LeiosStoreInner>,
    notify: watch::Sender<u64>,
}

impl LeiosStore {
    /// Create a new Leios store with the given block capacity.
    ///
    /// Returns the store (wrapped in `Arc`) and a subscription receiver
    /// for change notifications.
    pub fn new(capacity: usize) -> (Arc<Self>, watch::Receiver<u64>) {
        let (notify_sender, notify_receiver) = watch::channel(0u64);
        let store = Arc::new(Self {
            inner: Mutex::new(LeiosStoreInner {
                blocks: HashMap::new(),
                block_txs: HashMap::new(),
                votes: HashMap::new(),
                notifications: Vec::new(),
                capacity,
                version: 0,
            }),
            notify: notify_sender,
        });
        (store, notify_receiver)
    }

    /// Inject an endorser block. Generates a BlockOffer notification.
    ///
    /// The `point` must be `Point::Specific { slot, hash }`. If `Point::Origin`
    /// is passed, the block is silently dropped.
    pub fn inject_block(&self, point: Point, block: Vec<u8>) {
        let (slot, hash) = match &point {
            Point::Specific { slot, hash } => (*slot, *hash),
            Point::Origin => return,
        };
        let mut inner = self.inner.lock().unwrap();
        let key = BlockKey { slot, hash };
        inner.blocks.insert(key, block);
        inner
            .notifications
            .push(LeiosNotification::BlockOffer { point });
        self.bump_version(&mut inner);
    }

    /// Inject transactions for an endorser block. Generates a BlockTxsOffer notification.
    ///
    /// The `point` must be `Point::Specific { slot, hash }`. If `Point::Origin`
    /// is passed, the transactions are silently dropped.
    pub fn inject_block_txs(&self, point: Point, transactions: Vec<Vec<u8>>) {
        let (slot, hash) = match &point {
            Point::Specific { slot, hash } => (*slot, *hash),
            Point::Origin => return,
        };
        let mut inner = self.inner.lock().unwrap();
        let key = BlockKey { slot, hash };
        inner.block_txs.insert(key, transactions);
        inner
            .notifications
            .push(LeiosNotification::BlockTxsOffer { point });
        self.bump_version(&mut inner);
    }

    /// Inject votes. Generates a VotesOffer notification.
    ///
    /// `ids` are `(slot, voter_id)` pairs; `data` are the corresponding
    /// opaque vote blobs (same length).
    pub fn inject_votes(&self, ids: Vec<(u64, Vec<u8>)>, data: Vec<Vec<u8>>) {
        let mut inner = self.inner.lock().unwrap();
        for (id, blob) in ids.iter().zip(data.iter()) {
            inner.votes.insert(id.clone(), blob.clone());
        }
        inner
            .notifications
            .push(LeiosNotification::VotesOffer { votes: ids });
        self.bump_version(&mut inner);
    }

    /// Look up an endorser block by (slot, hash).
    pub fn get_block(&self, slot: u64, hash: &[u8; 32]) -> Option<Vec<u8>> {
        let inner = self.inner.lock().unwrap();
        let key = BlockKey { slot, hash: *hash };
        inner.blocks.get(&key).cloned()
    }

    /// Look up transactions for an endorser block.
    pub fn get_block_txs(&self, slot: u64, hash: &[u8; 32]) -> Option<Vec<Vec<u8>>> {
        let inner = self.inner.lock().unwrap();
        let key = BlockKey { slot, hash: *hash };
        inner.block_txs.get(&key).cloned()
    }

    /// Look up votes by their `(slot, voter_id)` identifiers.
    /// Returns one blob per requested id (empty vec if not found).
    pub fn get_votes(&self, ids: &[(u64, Vec<u8>)]) -> Vec<Vec<u8>> {
        let inner = self.inner.lock().unwrap();
        ids.iter()
            .filter_map(|id| inner.votes.get(id).cloned())
            .collect()
    }

    /// Get notifications after the given index (exclusive).
    /// Index 0 means "from the beginning".
    pub fn notifications_after(&self, after: usize) -> Vec<LeiosNotification> {
        let inner = self.inner.lock().unwrap();
        if after >= inner.notifications.len() {
            return Vec::new();
        }
        inner.notifications[after..].to_vec()
    }

    /// Get the total number of notifications so far.
    pub fn notification_count(&self) -> usize {
        self.inner.lock().unwrap().notifications.len()
    }

    /// Subscribe to change notifications.
    pub fn subscribe(&self) -> watch::Receiver<u64> {
        self.notify.subscribe()
    }

    /// Current version (monotonically increasing).
    pub fn version(&self) -> u64 {
        self.inner.lock().unwrap().version
    }

    fn bump_version(&self, inner: &mut LeiosStoreInner) {
        inner.version += 1;
        // Evict oldest blocks if over capacity.
        if inner.blocks.len() > inner.capacity {
            // Simple eviction: just clear half. Fine for a content store.
            // A real implementation would use LRU.
            let to_remove: Vec<BlockKey> = inner
                .blocks
                .keys()
                .take(inner.blocks.len() - inner.capacity)
                .cloned()
                .collect();
            for key in to_remove {
                inner.blocks.remove(&key);
                inner.block_txs.remove(&key);
            }
        }
        let version = inner.version;
        let _ = self.notify.send(version);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inject_and_get_block() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0xABu8; 32];
        let block = vec![1, 2, 3, 4];
        let point = Point::Specific { slot: 42, hash };

        store.inject_block(point, block.clone());

        assert_eq!(store.get_block(42, &hash), Some(block));
        assert_eq!(store.get_block(99, &hash), None);
    }

    #[test]
    fn inject_and_get_block_txs() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0xCDu8; 32];
        let txs = vec![vec![10, 20], vec![30, 40]];
        let point = Point::Specific { slot: 42, hash };

        store.inject_block_txs(point, txs.clone());

        assert_eq!(store.get_block_txs(42, &hash), Some(txs));
        assert_eq!(store.get_block_txs(99, &hash), None);
    }

    #[test]
    fn inject_and_get_votes() {
        let (store, _rx) = LeiosStore::new(100);
        let ids = vec![(100, vec![0x01]), (101, vec![0x02])];
        let data = vec![vec![0xA0], vec![0xB0]];

        store.inject_votes(ids.clone(), data.clone());

        let result = store.get_votes(&ids);
        assert_eq!(result, data);

        // Unknown vote returns empty.
        let result = store.get_votes(&[(999, vec![0xFF])]);
        assert!(result.is_empty());
    }

    #[test]
    fn notifications_accumulate() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0u8; 32];
        let point = Point::Specific { slot: 1, hash };

        store.inject_block(point, vec![0x01]);
        store.inject_votes(vec![(10, vec![0x02])], vec![vec![0x03]]);

        let all = store.notifications_after(0);
        assert_eq!(all.len(), 2);
        assert!(matches!(
            all[0],
            LeiosNotification::BlockOffer {
                point: Point::Specific { slot: 1, .. }
            }
        ));
        assert!(matches!(all[1], LeiosNotification::VotesOffer { .. }));

        let after_first = store.notifications_after(1);
        assert_eq!(after_first.len(), 1);

        let after_all = store.notifications_after(2);
        assert!(after_all.is_empty());
    }

    #[tokio::test]
    async fn subscribe_notifies_on_inject() {
        let (store, _rx) = LeiosStore::new(100);
        let mut sub = store.subscribe();

        store.inject_block(
            Point::Specific {
                slot: 1,
                hash: [0u8; 32],
            },
            vec![0x01],
        );

        let result = tokio::time::timeout(std::time::Duration::from_secs(1), sub.changed()).await;
        assert!(result.is_ok());
        assert!(*sub.borrow() > 0);
    }
}
