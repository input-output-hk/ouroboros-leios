//! Content-addressed store for Leios data (endorser blocks, votes).
//!
//! Separate from `ChainStore` because Leios data is keyed by `(slot, hash)`,
//! not part of a linear chain. Praos has no equivalent — all Praos data lives
//! on the chain itself.
//!
//! The coordinator writes (injects EBs, votes).
//! Server-side protocol handlers read (block lookups, vote lookups,
//! notification subscriptions).

use std::collections::{BTreeMap, HashMap, VecDeque};
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
    /// Transaction bodies per EB, keyed by manifest index. Sparse — a
    /// receiver accumulating partial bitmap responses populates only the
    /// indices it has seen so far. The producer populates `0..N` in one
    /// shot. `get_block_txs` falls through to manifest+resolver for any
    /// index missing here, so partial holdings still serve subsets to
    /// downstream peers.
    block_txs: HashMap<BlockKey, BTreeMap<u32, Vec<u8>>>,
    /// Per-EB ordered tx hash list. Populated by receivers after decoding
    /// a fetched EB manifest. Pairs with `tx_body_resolver` to serve the
    /// bodies indirectly without keeping a duplicate copy.
    eb_tx_hashes: HashMap<BlockKey, Vec<[u8; 32]>>,
    /// Votes keyed by (slot, voter_id).
    votes: HashMap<(u64, Vec<u8>), Vec<u8>>,
    /// Notification queue for the LeiosNotify server.  Front-pruned
    /// alongside the slot-window eviction of the other maps so
    /// long-running connections don't accumulate notifications for
    /// data that no longer lives in the store.
    notifications: VecDeque<LeiosNotification>,
    /// Total notifications popped off `notifications`' front so far —
    /// used to translate `notifications_after`'s logical cursor into
    /// the deque's local index.  Subscribers track a monotonically
    /// increasing logical position; when their cursor falls behind
    /// this count, `notifications_after` advances it to the front.
    notifications_pruned_count: usize,
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

impl LeiosStoreInner {
    /// True when every collection is empty — used by `tick_slot` to skip
    /// the eviction sweep once the store has drained.
    fn is_empty(&self) -> bool {
        self.blocks.is_empty()
            && self.block_txs.is_empty()
            && self.eb_tx_hashes.is_empty()
            && self.votes.is_empty()
            && self.notifications.is_empty()
    }
}

/// Snapshot of internal map sizes — for memory diagnostics.
///
/// `notifications_bytes_estimate` is a precise byte sum over the
/// notifications log: each `BlockOffer` / `BlockTxsOffer` is fixed-size,
/// but `VotesOffer` carries a variable-length `Vec<(u64, Vec<u8>)>` so
/// its payload bytes are summed directly.
#[derive(Debug, Clone, serde::Serialize)]
pub struct LeiosStoreStats {
    pub blocks: usize,
    pub block_txs: usize,
    pub eb_tx_hashes: usize,
    pub votes: usize,
    pub notifications: usize,
    pub notifications_bytes_estimate: usize,
    pub max_slot: u64,
}

/// Default slot-window retention for `LeiosStore`. Sized for the Linear Leios
/// pipeline (13 slots end-to-end) plus comfortable headroom — peers fetching
/// EBs / votes / manifests need only a window long enough to complete the
/// pipeline. Smaller than `LeiosTracker`'s 1000-slot dedup window because
/// the tracker stores tiny offer IDs while this store holds full bodies.
pub const DEFAULT_RETENTION_SLOTS: u64 = 100;

/// Hard ceiling on the `notifications` deque, independent of the slot
/// window. Slot-window eviction is the primary bound, but it relies on
/// front-only popping and on `max_slot` advancing; a peer that floods
/// offers within the active window, or injects with out-of-order slots
/// that bury an evictable entry behind a higher-slot front, could still
/// inflate the deque. This backstop guarantees a fixed upper bound on
/// notification memory regardless of inject order or offer rate — the
/// same role `capacity` plays for `blocks`. Sized well above normal
/// operation (cluster runs peak around ~120 notifications/node).
pub const MAX_NOTIFICATIONS: usize = 10_000;

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
                notifications: VecDeque::new(),
                notifications_pruned_count: 0,
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
        inner.blocks.insert(BlockKey { slot, hash }, block);
        inner.max_slot = inner.max_slot.max(slot);
        Self::push_notification(&mut inner, LeiosNotification::BlockOffer { point });
        self.bump_version(&mut inner);
    }

    /// Merge transaction bodies for an endorser block, indexed by their
    /// position in the EB manifest. Producers call once with indices
    /// `0..N` populated; receivers call repeatedly as partial bitmap
    /// responses arrive. Existing entries are preserved on conflict
    /// (first writer wins).
    ///
    /// A `BlockTxsOffer` notification fires only on the first call for
    /// a given EB. Subsequent merges are silent — peers already know we
    /// have *something* for this EB; their next fetch sees the new
    /// coverage.
    ///
    /// The `point` must be `Point::Specific { slot, hash }`. If
    /// `Point::Origin` is passed, the transactions are silently dropped.
    pub fn inject_block_txs(&self, point: Point, indexed: BTreeMap<u32, Vec<u8>>) {
        let (slot, hash) = match &point {
            Point::Specific { slot, hash } => (*slot, *hash),
            Point::Origin => return,
        };
        let mut inner = self.inner.lock().unwrap();
        let entry = inner.block_txs.entry(BlockKey { slot, hash }).or_default();
        let first_injection = entry.is_empty();
        for (idx, body) in indexed {
            entry.entry(idx).or_insert(body);
        }
        inner.max_slot = inner.max_slot.max(slot);
        if first_injection {
            Self::push_notification(&mut inner, LeiosNotification::BlockTxsOffer { point });
        }
        self.bump_version(&mut inner);
    }

    /// Convenience for the producer path: inject a complete ordered body
    /// list, indices `0..bodies.len()`. Equivalent to constructing a
    /// `BTreeMap` and calling `inject_block_txs`.
    pub fn inject_block_txs_full(&self, point: Point, bodies: Vec<Vec<u8>>) {
        let indexed: BTreeMap<u32, Vec<u8>> = bodies
            .into_iter()
            .enumerate()
            .map(|(i, b)| (i as u32, b))
            .collect();
        self.inject_block_txs(point, indexed);
    }

    /// Inject votes. Generates a VotesOffer notification.
    ///
    /// `ids` are `(slot, voter_id)` pairs; `data` are the corresponding
    /// opaque vote blobs (same length).
    pub fn inject_votes(&self, ids: Vec<(u64, Vec<u8>)>, data: Vec<Vec<u8>>) {
        if ids.is_empty() {
            return;
        }
        let mut inner = self.inner.lock().unwrap();
        let max_in_batch = ids.iter().map(|(s, _)| *s).max().unwrap_or(0);
        for (id, blob) in ids.iter().zip(data.iter()) {
            inner.votes.insert(id.clone(), blob.clone());
        }
        inner.max_slot = inner.max_slot.max(max_in_batch);
        Self::push_notification(&mut inner, LeiosNotification::VotesOffer { votes: ids });
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
        inner.max_slot = inner.max_slot.max(slot);
        Self::push_notification(&mut inner, LeiosNotification::BlockTxsOffer { point });
        self.bump_version(&mut inner);
    }

    /// Look up transactions for an endorser block, filtered by the
    /// CIP-0164 sparse bitmap. Returns `None` if the EB is unknown
    /// (neither sparse `block_txs` nor a manifest is recorded).
    ///
    /// For each requested index, prefers a body from the sparse
    /// `block_txs` map; falls through to manifest + `TxBodyResolver`
    /// for indices not yet held there. Returns the union — bodies in
    /// ascending index order, silently dropping indices whose body
    /// neither path can supply (partial response).
    pub fn get_block_txs(
        &self,
        slot: u64,
        hash: &[u8; 32],
        bitmap: &BTreeMap<u16, u64>,
    ) -> Option<Vec<Vec<u8>>> {
        let key = BlockKey { slot, hash: *hash };
        let (block_txs, manifest) = {
            let inner = self.inner.lock().unwrap();
            (
                inner.block_txs.get(&key).cloned(),
                inner.eb_tx_hashes.get(&key).cloned(),
            )
        };
        if block_txs.is_none() && manifest.is_none() {
            return None;
        }
        let resolver = self.tx_body_resolver.as_ref();
        let selected: Vec<Vec<u8>> = bitmap::iter_indices(bitmap)
            .filter_map(|i| {
                if let Some(body) = block_txs.as_ref().and_then(|m| m.get(&i).cloned()) {
                    return Some(body);
                }
                let h = manifest.as_ref()?.get(i as usize)?;
                resolver?.resolve_body(h)
            })
            .collect();
        Some(selected)
    }

    /// Look up the ordered tx-hash manifest for an EB, if recorded.
    /// Receivers consult this to map a fetched body's content hash to
    /// its position in the EB before merging into `block_txs`.
    pub fn get_eb_manifest(&self, slot: u64, hash: &[u8; 32]) -> Option<Vec<[u8; 32]>> {
        let inner = self.inner.lock().unwrap();
        let key = BlockKey { slot, hash: *hash };
        inner.eb_tx_hashes.get(&key).cloned()
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
        // Each ring-buffer slot costs sizeof(LeiosNotification);
        // `notification_heap_bytes` adds only the extra `VotesOffer`
        // payload on top, so the enum size isn't counted twice.
        let per_entry_overhead = std::mem::size_of::<LeiosNotification>();
        let notifications_bytes_estimate = inner.notifications.len() * per_entry_overhead
            + inner
                .notifications
                .iter()
                .map(notification_heap_bytes)
                .sum::<usize>()
            + std::mem::size_of::<VecDeque<LeiosNotification>>();
        LeiosStoreStats {
            blocks: inner.blocks.len(),
            block_txs: inner.block_txs.len(),
            eb_tx_hashes: inner.eb_tx_hashes.len(),
            votes: inner.votes.len(),
            notifications: inner.notifications.len(),
            notifications_bytes_estimate,
            max_slot: inner.max_slot,
        }
    }

    /// Get notifications after the given logical index (exclusive).
    ///
    /// The cursor `after` is monotonically increasing across the
    /// connection's lifetime — never reset, never shifted by pruning.
    /// If the caller's cursor has fallen behind the prune frontier,
    /// it's bumped up to the frontier so subsequent `*after += 1`
    /// increments stay aligned with the logical position of items the
    /// caller actually consumes.  Index `0` still means "from the
    /// earliest still-retained notification".
    pub fn notifications_after(&self, after: &mut usize) -> Vec<LeiosNotification> {
        let inner = self.inner.lock().unwrap();
        if *after < inner.notifications_pruned_count {
            *after = inner.notifications_pruned_count;
        }
        let local = *after - inner.notifications_pruned_count;
        if local >= inner.notifications.len() {
            // Clamp to the next-write index so a consumer that overshot
            // (asked for an index beyond `notification_count()`)
            // reconverges on the next inject instead of staying stuck
            // forever.
            *after = inner.notifications_pruned_count + inner.notifications.len();
            return Vec::new();
        }
        inner.notifications.range(local..).cloned().collect()
    }

    /// Total notifications ever pushed (including those since pruned).
    pub fn notification_count(&self) -> usize {
        let inner = self.inner.lock().unwrap();
        inner.notifications_pruned_count + inner.notifications.len()
    }

    /// Advance the retention clock to `current_slot`.  Triggers slot-window
    /// eviction even when no injects are happening, so a node that stops
    /// receiving Leios data (peer disconnects, partition) doesn't freeze
    /// its retention window at the last seen `max_slot`.  Cluster runs
    /// showed nodes with `slot − max_slot` of 100+ — retention stalled and
    /// stale notifications stayed retained.  Host should call once per
    /// wall-clock slot from its slot ticker.
    ///
    /// Does **not** bump the version counter or wake watch subscribers:
    /// no new notification was added, so there's nothing for a subscriber
    /// to consume.  Eviction is silent — already-delivered notifications
    /// disappearing from the back of the buffer doesn't concern readers.
    pub fn tick_slot(&self, current_slot: u64) {
        let mut inner = self.inner.lock().unwrap();
        if current_slot > inner.max_slot {
            inner.max_slot = current_slot;
            // Skip the O(n) retain sweep when nothing is retained — the
            // common idle/partition case this method exists for. Once the
            // store drains, every subsequent wall-clock tick is a cheap
            // no-op rather than four empty `retain` passes per slot.
            if !inner.is_empty() {
                Self::evict_old(&mut inner);
            }
        }
    }

    /// Subscribe to change notifications.
    pub fn subscribe(&self) -> watch::Receiver<u64> {
        self.notify.subscribe()
    }

    /// Current version (monotonically increasing).
    pub fn version(&self) -> u64 {
        self.inner.lock().unwrap().version
    }

    /// Push a notification, dropping it on the floor if all the slots it
    /// references are already below the retention cutoff.  The front-only
    /// pop_front eviction loop in `evict_old` can't reach a notification
    /// queued at the back, so a late-arriving offer for data that's
    /// already past retention has to be filtered at the source.  Caller
    /// must have updated `max_slot` already so the cutoff reflects the
    /// post-inject state.
    fn push_notification(inner: &mut LeiosStoreInner, notif: LeiosNotification) {
        let cutoff = inner.max_slot.saturating_sub(inner.retention_slots);
        if cutoff == 0 || !notification_evictable(&notif, cutoff) {
            inner.notifications.push_back(notif);
        }
    }

    /// Run slot-window eviction across all maps plus the capacity backstop
    /// on `blocks`.  Pure data work — does not touch `version` or the
    /// watch channel.  Used by both `bump_version` (after an inject) and
    /// `tick_slot` (silent wall-clock advance).
    fn evict_old(inner: &mut LeiosStoreInner) {
        let cutoff = inner.max_slot.saturating_sub(inner.retention_slots);
        if cutoff > 0 {
            inner.blocks.retain(|key, _| key.slot >= cutoff);
            inner.block_txs.retain(|key, _| key.slot >= cutoff);
            inner.eb_tx_hashes.retain(|key, _| key.slot >= cutoff);
            inner.votes.retain(|(slot, _), _| *slot >= cutoff);
            // Front-prune `notifications` for entries that reference
            // only data older than the cutoff.  `push_notification`
            // refuses anything already below cutoff, so any below-cutoff
            // survivors must have aged past the boundary while at the
            // front — `pop_front` is both safe and O(evicted) without
            // scanning the whole deque.
            while let Some(front) = inner.notifications.front() {
                if notification_evictable(front, cutoff) {
                    inner.notifications.pop_front();
                    inner.notifications_pruned_count += 1;
                } else {
                    break;
                }
            }
        }

        // Capacity backstop on `notifications` (independent of slot
        // window). Front-only popping keeps absolute indexing intact:
        // every pop increments `notifications_pruned_count`, and a
        // subscriber whose cursor falls behind is fast-forwarded by
        // `notifications_after`. Drops the oldest offers first, matching
        // the slot-window prune direction.
        while inner.notifications.len() > MAX_NOTIFICATIONS {
            inner.notifications.pop_front();
            inner.notifications_pruned_count += 1;
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
    }

    fn bump_version(&self, inner: &mut LeiosStoreInner) {
        inner.version += 1;
        Self::evict_old(inner);

        // Optional diagnostic: emit a stats line every Nth bump so we can
        // spot unbounded growth from outside. `0` disables.
        if inner.stats_log_interval > 0 && inner.version.is_multiple_of(inner.stats_log_interval) {
            let cutoff = inner.max_slot.saturating_sub(inner.retention_slots);
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

/// True iff every slot the notification references is below `cutoff`
/// — i.e. the notification only points at data that's already been
/// evicted from the slot-window-pruned maps and can never be served.
fn notification_evictable(n: &LeiosNotification, cutoff: u64) -> bool {
    match n {
        LeiosNotification::BlockOffer { point }
        | LeiosNotification::BlockTxsOffer { point } => match point {
            Point::Specific { slot, .. } => *slot < cutoff,
            Point::Origin => true,
        },
        LeiosNotification::VotesOffer { votes } => votes.iter().all(|(s, _)| *s < cutoff),
    }
}

/// Extra heap bytes beyond the fixed `size_of::<LeiosNotification>()`
/// slot in the deque.  Zero for `BlockOffer` / `BlockTxsOffer` (no heap
/// payload); sums the variable-length `Vec<(u64, Vec<u8>)>` allocation
/// for `VotesOffer`.  The caller adds the fixed per-entry size
/// separately — keeping the two parts separate avoids double-counting
/// the enum size.
fn notification_heap_bytes(n: &LeiosNotification) -> usize {
    match n {
        LeiosNotification::BlockOffer { .. } | LeiosNotification::BlockTxsOffer { .. } => 0,
        LeiosNotification::VotesOffer { votes } => votes
            .iter()
            .map(|(_, id)| std::mem::size_of::<(u64, Vec<u8>)>() + id.len())
            .sum(),
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

        store.inject_block_txs_full(point, txs.clone());

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

        store.inject_block_txs_full(point, txs);

        let bitmap = BTreeMap::new();
        assert_eq!(store.get_block_txs(42, &hash, &bitmap), Some(Vec::new()));
    }

    #[test]
    fn get_block_txs_filters_by_bitmap_and_orders_ascending() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0xEFu8; 32];
        let txs: Vec<Vec<u8>> = (0..70u8).map(|i| vec![i]).collect();
        let point = Point::Specific { slot: 1, hash };

        store.inject_block_txs_full(point, txs);

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
        store.inject_block_txs_full(point.clone(), vec![vec![100u8], vec![200u8]]);
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
        store.inject_block_txs_full(point, txs);

        // Bit 99 is past the available 2 txs; should be silently dropped.
        let bitmap = bitmap::from_indices(&[0, 99]);
        let got = store.get_block_txs(5, &hash, &bitmap).unwrap();
        assert_eq!(got, vec![vec![1u8]]);
    }

    #[test]
    fn inject_block_txs_partial_then_partial_unions_holdings() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0x01u8; 32];
        let point = Point::Specific { slot: 7, hash };

        // First batch: indices 0 and 2.
        let mut first = BTreeMap::new();
        first.insert(0u32, vec![0xA0]);
        first.insert(2u32, vec![0xA2]);
        store.inject_block_txs(point.clone(), first);

        // Second batch: indices 1 and 3.
        let mut second = BTreeMap::new();
        second.insert(1u32, vec![0xA1]);
        second.insert(3u32, vec![0xA3]);
        store.inject_block_txs(point, second);

        let bitmap = bitmap::from_indices(&[0, 1, 2, 3]);
        let got = store.get_block_txs(7, &hash, &bitmap).unwrap();
        assert_eq!(got, vec![vec![0xA0], vec![0xA1], vec![0xA2], vec![0xA3]]);
    }

    #[test]
    fn inject_block_txs_emits_offer_only_on_first_call() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0x02u8; 32];
        let point = Point::Specific { slot: 8, hash };

        let mut a = BTreeMap::new();
        a.insert(0u32, vec![0xB0]);
        store.inject_block_txs(point.clone(), a);

        let mut b = BTreeMap::new();
        b.insert(1u32, vec![0xB1]);
        store.inject_block_txs(point, b);

        // One BlockTxsOffer notification, not two.
        let txs_offers = store
            .notifications_after(&mut 0)
            .into_iter()
            .filter(|n| matches!(n, LeiosNotification::BlockTxsOffer { .. }))
            .count();
        assert_eq!(txs_offers, 1);
    }

    #[test]
    fn inject_block_txs_does_not_overwrite_existing_index() {
        let (store, _rx) = LeiosStore::new(100);
        let hash = [0x03u8; 32];
        let point = Point::Specific { slot: 9, hash };

        let mut a = BTreeMap::new();
        a.insert(0u32, vec![0xC0]);
        store.inject_block_txs(point.clone(), a);

        // Conflicting body for index 0 — first writer wins.
        let mut b = BTreeMap::new();
        b.insert(0u32, vec![0xFF]);
        store.inject_block_txs(point, b);

        let bitmap = bitmap::from_indices(&[0]);
        let got = store.get_block_txs(9, &hash, &bitmap).unwrap();
        assert_eq!(got, vec![vec![0xC0]]);
    }

    #[test]
    fn get_block_txs_unions_block_txs_with_manifest_resolver() {
        // Sparse block_txs has indices 0 and 2; manifest+resolver covers
        // index 1. The union must satisfy a request for all three.
        let h0 = [0x10u8; 32];
        let h1 = [0x20u8; 32];
        let h2 = [0x30u8; 32];
        let resolver: Arc<dyn TxBodyResolver> = Arc::new(StubResolver(HashMap::from([(
            h1.to_vec(),
            vec![0xD1],
        )])));
        let (store, _rx) = LeiosStore::new_with_resolver(100, Some(resolver));

        let eb_hash = [0xDDu8; 32];
        let point = Point::Specific {
            slot: 11,
            hash: eb_hash,
        };
        store.record_eb_manifest(point.clone(), vec![h0, h1, h2]);

        let mut partial = BTreeMap::new();
        partial.insert(0u32, vec![0xD0]);
        partial.insert(2u32, vec![0xD2]);
        store.inject_block_txs(point, partial);

        let bitmap = bitmap::from_indices(&[0, 1, 2]);
        let got = store.get_block_txs(11, &eb_hash, &bitmap).unwrap();
        assert_eq!(got, vec![vec![0xD0], vec![0xD1], vec![0xD2]]);
    }

    #[test]
    fn get_eb_manifest_returns_recorded_hashes() {
        let (store, _rx) = LeiosStore::new(100);
        let eb_hash = [0xE1u8; 32];
        let point = Point::Specific {
            slot: 13,
            hash: eb_hash,
        };
        let manifest = vec![[0xAA; 32], [0xBB; 32]];
        store.record_eb_manifest(point, manifest.clone());

        assert_eq!(store.get_eb_manifest(13, &eb_hash), Some(manifest));
        assert_eq!(store.get_eb_manifest(99, &eb_hash), None);
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

        let all = store.notifications_after(&mut 0);
        assert_eq!(all.len(), 2);
        assert!(matches!(
            all[0],
            LeiosNotification::BlockOffer {
                point: Point::Specific { slot: 1, .. }
            }
        ));
        assert!(matches!(all[1], LeiosNotification::VotesOffer { .. }));

        let after_first = store.notifications_after(&mut 1);
        assert_eq!(after_first.len(), 1);

        let after_all = store.notifications_after(&mut 2);
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

    #[test]
    fn slot_retention_prunes_notifications() {
        // Tight retention window so a few slot advances trigger eviction.
        let (store, _rx) = LeiosStore::new_with_retention(1000, None, 5, 0);

        // Three notifications at slot 1.
        store.inject_block(
            Point::Specific {
                slot: 1,
                hash: [0x11; 32],
            },
            vec![0xB0],
        );
        store.inject_block(
            Point::Specific {
                slot: 1,
                hash: [0x12; 32],
            },
            vec![0xB1],
        );
        store.inject_votes(vec![(1, vec![0xAA])], vec![vec![0x01]]);
        assert_eq!(store.notification_count(), 3);

        // Inject a recent block to push max_slot past the retention
        // window — cutoff = 100 - 5 = 95, all slot-1 notifications
        // are now stale.
        store.inject_block(
            Point::Specific {
                slot: 100,
                hash: [0x33; 32],
            },
            vec![0xD0],
        );

        // The slot-1 notifications were front-pruned; only the
        // slot-100 one remains.  The logical count still reflects
        // every notification ever pushed.
        assert_eq!(store.notification_count(), 4);
        let mut cursor = 0;
        let pending = store.notifications_after(&mut cursor);
        assert_eq!(pending.len(), 1);
        assert_eq!(cursor, 3, "cursor advanced past the prune frontier");
        assert!(matches!(
            pending[0],
            LeiosNotification::BlockOffer {
                point: Point::Specific { slot: 100, .. }
            }
        ));
    }

    #[test]
    fn late_slot_inject_drops_notification_below_cutoff() {
        // max_slot advances to 100 first; a subsequent inject at slot 1 lands
        // below cutoff=95 and must be dropped at the source — the front-only
        // eviction loop in `evict_old` can't reach a late-slot entry at the
        // back of the deque.
        let (store, _rx) = LeiosStore::new_with_retention(1000, None, 5, 0);
        store.inject_block(
            Point::Specific {
                slot: 100,
                hash: [0xAA; 32],
            },
            vec![0xA0],
        );
        let count_before = store.notification_count();

        store.inject_block(
            Point::Specific {
                slot: 1,
                hash: [0xBB; 32],
            },
            vec![0xB0],
        );

        // Notification was filtered at the source — count unchanged.
        assert_eq!(store.notification_count(), count_before);
    }

    #[test]
    fn notifications_after_overshoot_clamps_to_next_write() {
        let (store, _rx) = LeiosStore::new(100);
        store.inject_block(
            Point::Specific {
                slot: 1,
                hash: [0u8; 32],
            },
            vec![0xA0],
        );

        // Overshoot: only 1 notification exists (next-write index 1)
        // but we ask for everything ≥ 10.
        let mut cursor = 10usize;
        let entries = store.notifications_after(&mut cursor);
        assert!(entries.is_empty());
        assert_eq!(
            cursor, 1,
            "cursor should clamp to next-write index, not echo the overshoot"
        );
    }

    #[tokio::test]
    async fn tick_slot_does_not_wake_subscribers() {
        // tick_slot advances the retention clock but adds no new notifications,
        // so it must not wake watch subscribers — those are waiting for new
        // data, and there isn't any.
        let (store, _rx) = LeiosStore::new_with_retention(1000, None, 5, 0);
        let mut sub = store.subscribe();

        store.tick_slot(100);

        let result =
            tokio::time::timeout(std::time::Duration::from_millis(50), sub.changed()).await;
        assert!(
            result.is_err(),
            "tick_slot must not signal on the watch channel"
        );
    }

    #[test]
    fn tick_slot_still_evicts_old_data() {
        // Eviction must run even without a watch wake-up.
        let (store, _rx) = LeiosStore::new_with_retention(1000, None, 5, 0);
        store.inject_block(
            Point::Specific {
                slot: 1,
                hash: [0x11; 32],
            },
            vec![0xB0],
        );
        assert!(store.get_block(1, &[0x11; 32]).is_some());

        store.tick_slot(100);

        assert!(
            store.get_block(1, &[0x11; 32]).is_none(),
            "tick_slot should still evict past retention"
        );
    }

    #[test]
    fn notifications_capped_by_capacity_backstop() {
        // Flood offers all within the retention window (same slot, distinct
        // hashes) so slot-window eviction never fires. The capacity backstop
        // must still bound the deque, and absolute indexing must stay intact:
        // `notification_count` (pruned + retained) reflects every push.
        let (store, _rx) = LeiosStore::new_with_retention(MAX_NOTIFICATIONS, None, 1000, 0);
        let pushed = MAX_NOTIFICATIONS + 250;
        for i in 0..pushed {
            let mut hash = [0u8; 32];
            hash[0] = (i & 0xff) as u8;
            hash[1] = ((i >> 8) & 0xff) as u8;
            store.inject_block(Point::Specific { slot: 10, hash }, vec![0xAB]);
        }

        let stats = store.stats();
        assert!(
            stats.notifications <= MAX_NOTIFICATIONS,
            "deque must stay within the backstop: {} > {}",
            stats.notifications,
            MAX_NOTIFICATIONS
        );
        assert_eq!(
            store.notification_count(),
            pushed,
            "pruned + retained must account for every pushed notification"
        );

        // A subscriber whose cursor fell behind the pruned front is
        // fast-forwarded rather than reading a stale local index.
        let mut cursor = 0usize;
        let entries = store.notifications_after(&mut cursor);
        assert!(cursor >= pushed - MAX_NOTIFICATIONS, "cursor fast-forwarded past pruned front");
        assert_eq!(entries.len(), stats.notifications);
    }

    #[test]
    fn long_run_stays_bounded_under_sustained_load() {
        // Stress test for the eviction guarantee that motivates this PR.
        // Simulates a node receiving sustained Leios traffic for many
        // retention windows in a row: votes + EBs every slot, plus a
        // wall-clock `tick_slot` running ahead.  Both the data maps and
        // the notifications deque must stay O(retention) — not O(slots).
        const RETENTION: u64 = 100;
        const SLOTS: u64 = 10_000;
        let (store, _rx) = LeiosStore::new_with_retention(10_000, None, RETENTION, 0);

        for slot in 0..SLOTS {
            store.inject_votes(vec![(slot, vec![0xAA; 32])], vec![vec![0xBB; 100]]);
            store.inject_block(
                Point::Specific {
                    slot,
                    hash: [0xCC; 32],
                },
                vec![0xDD; 100],
            );
            // Wall-clock leads inject slots; exercises tick_slot eviction.
            if slot % 7 == 0 {
                store.tick_slot(slot + 5);
            }
        }

        let stats = store.stats();
        let bound = (RETENTION * 2) as usize;
        assert!(
            stats.votes <= bound,
            "votes leaked: {} > {} after {} slots",
            stats.votes,
            bound,
            SLOTS
        );
        assert!(
            stats.blocks <= bound,
            "blocks leaked: {} > {} after {} slots",
            stats.blocks,
            bound,
            SLOTS
        );
        assert!(
            stats.notifications <= bound * 2,
            "notifications leaked: {} > {} after {} slots",
            stats.notifications,
            bound * 2,
            SLOTS
        );
        let byte_bound = stats.notifications * 10_000 + 4096;
        assert!(
            stats.notifications_bytes_estimate <= byte_bound,
            "notifications_bytes_estimate looks inflated: {} > {}",
            stats.notifications_bytes_estimate,
            byte_bound
        );
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
