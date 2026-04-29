//! Content-addressed store for Leios data (endorser blocks, votes).
//!
//! Separate from `ChainStore` because Leios data is keyed by `(slot, hash)`,
//! not part of a linear chain. Praos has no equivalent — all Praos data lives
//! on the chain itself.
//!
//! The coordinator writes (injects EBs, votes).
//! Server-side protocol handlers read (block lookups, vote lookups,
//! notification subscriptions).

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};

use tokio::sync::watch;

use crate::protocols::leios_fetch::bitmap;
use crate::types::Point;

/// Resolves a transaction body by its 32-byte hash. The Leios store calls
/// this when a peer asks for an EB's txs and only the manifest is cached
/// locally — typically the host application's mempool answers.
pub trait TxBodyResolver: Send + Sync {
    /// Return the body for `tx_id`, or `None` if unknown.
    fn resolve_body(&self, tx_id: &[u8]) -> Option<Vec<u8>>;
}

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
    /// Full transaction bodies per EB. Populated by the producer of an EB
    /// (it has every body in hand) — gives a fast direct lookup path.
    block_txs: HashMap<BlockKey, Vec<Vec<u8>>>,
    /// Per-EB ordered tx hash list. Populated by receivers after decoding
    /// a fetched EB manifest. Pairs with `tx_body_resolver` to serve the
    /// bodies indirectly without keeping a duplicate copy.
    eb_tx_hashes: HashMap<BlockKey, Vec<[u8; 32]>>,
    /// Votes keyed by (slot, voter_id).
    votes: HashMap<(u64, Vec<u8>), Vec<u8>>,
    /// Notification queue for the LeiosNotify server.
    notifications: Vec<LeiosNotification>,
    /// Max number of blocks to retain.
    capacity: usize,
    /// Monotonically increasing counter for change notifications.
    version: u64,
    /// Highest slot observed in any inject — drives slot-based eviction.
    max_slot: u64,
    /// Slot-window retention. Entries older than `max_slot - retention_slots`
    /// are evicted on every `bump_version`. Bounds memory under sustained
    /// EB / vote load (each EB carries ~600 votes; without slot eviction,
    /// receivers accumulate the full history forever).
    retention_slots: u64,
    /// Log a stats line every Nth `bump_version` call. `0` disables.
    stats_log_interval: u64,
}

/// Snapshot of internal map sizes — for memory diagnostics.
#[derive(Debug, Clone)]
pub struct LeiosStoreStats {
    pub blocks: usize,
    pub block_txs: usize,
    pub eb_tx_hashes: usize,
    pub votes: usize,
    pub notifications: usize,
    pub max_slot: u64,
}

/// Default slot-window retention for `LeiosStore`. Sized for the Linear Leios
/// pipeline (13 slots end-to-end) plus comfortable headroom — peers fetching
/// EBs / votes / manifests need only a window long enough to complete the
/// pipeline. Smaller than `LeiosTracker`'s 1000-slot dedup window because
/// the tracker stores tiny offer IDs while this store holds full bodies.
pub const DEFAULT_RETENTION_SLOTS: u64 = 100;

/// Thread-safe content-addressed store for Leios data.
///
/// Follows the same Mutex + watch pattern as `ChainStore`.
pub struct LeiosStore {
    inner: Mutex<LeiosStoreInner>,
    notify: watch::Sender<u64>,
    /// Optional callback that resolves a tx body by its hash. Used to
    /// serve EB tx requests for EBs whose manifest is cached locally
    /// but whose full bodies aren't (i.e. receivers, not producers).
    tx_body_resolver: Option<Arc<dyn TxBodyResolver>>,
}

impl LeiosStore {
    /// Create a new Leios store with the given block capacity.
    ///
    /// Returns the store (wrapped in `Arc`) and a subscription receiver
    /// for change notifications.
    pub fn new(capacity: usize) -> (Arc<Self>, watch::Receiver<u64>) {
        Self::new_with_resolver(capacity, None)
    }

    /// Create a Leios store with an optional `TxBodyResolver` for serving
    /// EB tx requests on receiver nodes that cache only the manifest.
    pub fn new_with_resolver(
        capacity: usize,
        tx_body_resolver: Option<Arc<dyn TxBodyResolver>>,
    ) -> (Arc<Self>, watch::Receiver<u64>) {
        Self::new_with_retention(capacity, tx_body_resolver, DEFAULT_RETENTION_SLOTS, 0)
    }

    /// Full constructor: explicit slot-window retention and stats logging
    /// interval. `stats_log_interval` of `0` disables stats logging.
    pub fn new_with_retention(
        capacity: usize,
        tx_body_resolver: Option<Arc<dyn TxBodyResolver>>,
        retention_slots: u64,
        stats_log_interval: u64,
    ) -> (Arc<Self>, watch::Receiver<u64>) {
        let (notify_sender, notify_receiver) = watch::channel(0u64);
        let store = Arc::new(Self {
            inner: Mutex::new(LeiosStoreInner {
                blocks: HashMap::new(),
                block_txs: HashMap::new(),
                eb_tx_hashes: HashMap::new(),
                votes: HashMap::new(),
                notifications: Vec::new(),
                capacity,
                version: 0,
                max_slot: 0,
                retention_slots,
                stats_log_interval,
            }),
            notify: notify_sender,
            tx_body_resolver,
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
        inner.max_slot = inner.max_slot.max(slot);
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
        inner.max_slot = inner.max_slot.max(slot);
        self.bump_version(&mut inner);
    }

    /// Inject votes. Generates a VotesOffer notification.
    ///
    /// `ids` are `(slot, voter_id)` pairs; `data` are the corresponding
    /// opaque vote blobs (same length).
    pub fn inject_votes(&self, ids: Vec<(u64, Vec<u8>)>, data: Vec<Vec<u8>>) {
        let mut inner = self.inner.lock().unwrap();
        let max_in_batch = ids.iter().map(|(s, _)| *s).max().unwrap_or(0);
        for (id, blob) in ids.iter().zip(data.iter()) {
            inner.votes.insert(id.clone(), blob.clone());
        }
        inner
            .notifications
            .push(LeiosNotification::VotesOffer { votes: ids });
        inner.max_slot = inner.max_slot.max(max_in_batch);
        self.bump_version(&mut inner);
    }

    /// Look up an endorser block by (slot, hash).
    pub fn get_block(&self, slot: u64, hash: &[u8; 32]) -> Option<Vec<u8>> {
        let inner = self.inner.lock().unwrap();
        let key = BlockKey { slot, hash: *hash };
        inner.blocks.get(&key).cloned()
    }

    /// Record the ordered tx-hash list of an EB's manifest. Pairs with a
    /// `TxBodyResolver` so receivers can serve `MsgLeiosBlockTxsRequest`
    /// without keeping the bodies in this store. Also pushes a
    /// `BlockTxsOffer` notification so this node advertises tx availability
    /// to downstream peers — that's how epidemic flooding extends beyond
    /// the original producer.
    pub fn record_eb_manifest(&self, point: Point, tx_hashes: Vec<[u8; 32]>) {
        let (slot, hash) = match &point {
            Point::Specific { slot, hash } => (*slot, *hash),
            Point::Origin => return,
        };
        let mut inner = self.inner.lock().unwrap();
        inner
            .eb_tx_hashes
            .insert(BlockKey { slot, hash }, tx_hashes);
        inner
            .notifications
            .push(LeiosNotification::BlockTxsOffer { point });
        inner.max_slot = inner.max_slot.max(slot);
        self.bump_version(&mut inner);
    }

    /// Look up transactions for an endorser block, filtered by the
    /// CIP-0164 sparse bitmap. Returns `None` if the EB is unknown.
    /// Returns transactions in ascending index order; out-of-range
    /// bits in the bitmap are silently ignored. Indices whose body
    /// the resolver cannot supply are silently dropped (partial response).
    pub fn get_block_txs(
        &self,
        slot: u64,
        hash: &[u8; 32],
        bitmap: &BTreeMap<u16, u64>,
    ) -> Option<Vec<Vec<u8>>> {
        let key = BlockKey { slot, hash: *hash };
        // Producer path: full bodies cached directly.
        {
            let inner = self.inner.lock().unwrap();
            if let Some(stored) = inner.block_txs.get(&key) {
                let selected: Vec<Vec<u8>> = bitmap::iter_indices(bitmap)
                    .filter_map(|i| stored.get(i as usize).cloned())
                    .collect();
                return Some(selected);
            }
        }
        // Receiver path: manifest cached, bodies resolved via callback.
        let manifest = {
            let inner = self.inner.lock().unwrap();
            inner.eb_tx_hashes.get(&key).cloned()
        };
        let manifest = manifest?;
        let resolver = self.tx_body_resolver.as_ref()?;
        let selected: Vec<Vec<u8>> = bitmap::iter_indices(bitmap)
            .filter_map(|i| {
                let h = manifest.get(i as usize)?;
                resolver.resolve_body(h)
            })
            .collect();
        Some(selected)
    }

    /// Look up votes by their `(slot, voter_id)` identifiers.
    /// Returns one blob per requested id (empty vec if not found).
    pub fn get_votes(&self, ids: &[(u64, Vec<u8>)]) -> Vec<Vec<u8>> {
        let inner = self.inner.lock().unwrap();
        ids.iter()
            .filter_map(|id| inner.votes.get(id).cloned())
            .collect()
    }

    /// Snapshot of internal map sizes — for memory diagnostics.
    pub fn stats(&self) -> LeiosStoreStats {
        let inner = self.inner.lock().unwrap();
        LeiosStoreStats {
            blocks: inner.blocks.len(),
            block_txs: inner.block_txs.len(),
            eb_tx_hashes: inner.eb_tx_hashes.len(),
            votes: inner.votes.len(),
            notifications: inner.notifications.len(),
            max_slot: inner.max_slot,
        }
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

        // Slot-window eviction. Bounds memory under sustained EB / vote
        // load: receivers were accumulating every vote and every EB
        // manifest forever, leaking ~70 MB/s on a 25-node cluster.
        let cutoff = inner.max_slot.saturating_sub(inner.retention_slots);
        if cutoff > 0 {
            inner.blocks.retain(|key, _| key.slot >= cutoff);
            inner.block_txs.retain(|key, _| key.slot >= cutoff);
            inner.eb_tx_hashes.retain(|key, _| key.slot >= cutoff);
            inner.votes.retain(|(slot, _), _| *slot >= cutoff);
        }

        // Capacity backstop on `blocks` (independent of slot window).
        if inner.blocks.len() > inner.capacity {
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

        // Optional diagnostic: emit a stats line every Nth bump so we can
        // spot unbounded growth from outside. `0` disables.
        if inner.stats_log_interval > 0 && inner.version % inner.stats_log_interval == 0 {
            tracing::info!(
                version = inner.version,
                max_slot = inner.max_slot,
                cutoff,
                blocks = inner.blocks.len(),
                block_txs = inner.block_txs.len(),
                eb_tx_hashes = inner.eb_tx_hashes.len(),
                votes = inner.votes.len(),
                notifications = inner.notifications.len(),
                "leios_store: stats"
            );
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
    fn get_block_txs_with_select_all_returns_all() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0xCDu8; 32];
        let txs = vec![vec![10, 20], vec![30, 40]];
        let point = Point::Specific { slot: 42, hash };

        store.inject_block_txs(point, txs.clone());

        let bitmap = bitmap::select_all(txs.len() as u32);
        assert_eq!(store.get_block_txs(42, &hash, &bitmap), Some(txs));
        assert_eq!(store.get_block_txs(99, &hash, &bitmap), None);
    }

    #[test]
    fn get_block_txs_empty_bitmap_returns_empty() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0xCDu8; 32];
        let txs = vec![vec![10, 20], vec![30, 40]];
        let point = Point::Specific { slot: 42, hash };

        store.inject_block_txs(point, txs);

        let bitmap = BTreeMap::new();
        assert_eq!(store.get_block_txs(42, &hash, &bitmap), Some(Vec::new()));
    }

    #[test]
    fn get_block_txs_filters_by_bitmap_and_orders_ascending() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0xEFu8; 32];
        let txs: Vec<Vec<u8>> = (0..70u8).map(|i| vec![i]).collect();
        let point = Point::Specific { slot: 1, hash };

        store.inject_block_txs(point, txs);

        // Pick out-of-order indices spanning two segments to check ordering.
        let bitmap = bitmap::from_indices(&[65, 0, 63]);
        let got = store.get_block_txs(1, &hash, &bitmap).unwrap();
        assert_eq!(got, vec![vec![0u8], vec![63u8], vec![65u8]]);
    }

    struct StubResolver(HashMap<Vec<u8>, Vec<u8>>);
    impl TxBodyResolver for StubResolver {
        fn resolve_body(&self, tx_id: &[u8]) -> Option<Vec<u8>> {
            self.0.get(tx_id).cloned()
        }
    }

    #[test]
    fn get_block_txs_resolves_via_manifest_and_resolver() {
        let h0 = [0x10u8; 32];
        let h1 = [0x20u8; 32];
        let h2 = [0x30u8; 32];
        let bodies = HashMap::from([
            (h0.to_vec(), vec![1u8]),
            (h1.to_vec(), vec![2u8]),
            (h2.to_vec(), vec![3u8]),
        ]);
        let resolver: Arc<dyn TxBodyResolver> = Arc::new(StubResolver(bodies));
        let (store, _rx) = LeiosStore::new_with_resolver(100, Some(resolver));

        let eb_hash = [0xEEu8; 32];
        let point = Point::Specific {
            slot: 5,
            hash: eb_hash,
        };
        store.record_eb_manifest(point, vec![h0, h1, h2]);

        // Bitmap selects indices 0 and 2.
        let bitmap = bitmap::from_indices(&[0, 2]);
        let got = store.get_block_txs(5, &eb_hash, &bitmap).unwrap();
        assert_eq!(got, vec![vec![1u8], vec![3u8]]);
    }

    #[test]
    fn get_block_txs_resolver_partial_drops_unknown_bodies() {
        let h0 = [0x40u8; 32];
        let h1 = [0x50u8; 32];
        // Only h0 is resolvable.
        let resolver: Arc<dyn TxBodyResolver> =
            Arc::new(StubResolver(HashMap::from([(h0.to_vec(), vec![0xAA])])));
        let (store, _rx) = LeiosStore::new_with_resolver(100, Some(resolver));

        let eb_hash = [0xCCu8; 32];
        let point = Point::Specific {
            slot: 7,
            hash: eb_hash,
        };
        store.record_eb_manifest(point, vec![h0, h1]);

        let bitmap = bitmap::from_indices(&[0, 1]);
        let got = store.get_block_txs(7, &eb_hash, &bitmap).unwrap();
        assert_eq!(got, vec![vec![0xAA]]);
    }

    #[test]
    fn get_block_txs_block_txs_takes_precedence_over_manifest() {
        // Producer-style store with both block_txs (full bodies) and a
        // manifest cache. The direct path should win.
        let resolver: Arc<dyn TxBodyResolver> = Arc::new(StubResolver(HashMap::new()));
        let (store, _rx) = LeiosStore::new_with_resolver(100, Some(resolver));
        let eb_hash = [0xABu8; 32];
        let point = Point::Specific {
            slot: 1,
            hash: eb_hash,
        };
        store.inject_block_txs(point.clone(), vec![vec![100u8], vec![200u8]]);
        // Pretend we also have manifest hashes (would normally be set
        // separately; here we make sure the block_txs path wins).
        store.record_eb_manifest(point, vec![[0; 32], [0; 32]]);

        let bitmap = bitmap::from_indices(&[0, 1]);
        let got = store.get_block_txs(1, &eb_hash, &bitmap).unwrap();
        assert_eq!(got, vec![vec![100u8], vec![200u8]]);
    }

    #[test]
    fn get_block_txs_returns_none_when_neither_path_has_eb() {
        let resolver: Arc<dyn TxBodyResolver> = Arc::new(StubResolver(HashMap::new()));
        let (store, _rx) = LeiosStore::new_with_resolver(100, Some(resolver));
        let bitmap = bitmap::from_indices(&[0]);
        assert!(store.get_block_txs(99, &[0xFF; 32], &bitmap).is_none());
    }

    #[test]
    fn get_block_txs_ignores_out_of_range_bits() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0xAA; 32];
        let txs = vec![vec![1u8], vec![2u8]];
        let point = Point::Specific { slot: 5, hash };
        store.inject_block_txs(point, txs);

        // Bit 99 is past the available 2 txs; should be silently dropped.
        let bitmap = bitmap::from_indices(&[0, 99]);
        let got = store.get_block_txs(5, &hash, &bitmap).unwrap();
        assert_eq!(got, vec![vec![1u8]]);
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

    #[test]
    fn slot_retention_prunes_old_data() {
        // Tight retention window so the test stays small.
        let (store, _rx) = LeiosStore::new_with_retention(1000, None, 5, 0);

        // Inject votes/blocks at slot 1, then advance the clock far past
        // the retention window. Old entries must be evicted.
        store.inject_votes(vec![(1, vec![0xAA])], vec![vec![0x01]]);
        store.inject_block(
            Point::Specific {
                slot: 1,
                hash: [0x11; 32],
            },
            vec![0xB0],
        );
        store.record_eb_manifest(
            Point::Specific {
                slot: 1,
                hash: [0x22; 32],
            },
            vec![[0xCC; 32]],
        );

        // Pre-eviction sanity.
        assert_eq!(store.get_votes(&[(1, vec![0xAA])]), vec![vec![0x01]]);
        assert!(store.get_block(1, &[0x11; 32]).is_some());

        // Inject something far in the future — past the retention cutoff.
        // max_slot becomes 100; cutoff = 100 - 5 = 95; slot=1 entries evicted.
        store.inject_block(
            Point::Specific {
                slot: 100,
                hash: [0x33; 32],
            },
            vec![0xD0],
        );

        assert!(
            store.get_votes(&[(1, vec![0xAA])]).is_empty(),
            "old vote should be evicted past retention window"
        );
        assert!(
            store.get_block(1, &[0x11; 32]).is_none(),
            "old block should be evicted past retention window"
        );
        assert!(
            store
                .get_block_txs(1, &[0x22; 32], &bitmap::select_all(64))
                .is_none(),
            "old eb_tx_hashes should be evicted past retention window"
        );

        // Recent entry stays.
        assert!(store.get_block(100, &[0x33; 32]).is_some());
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
