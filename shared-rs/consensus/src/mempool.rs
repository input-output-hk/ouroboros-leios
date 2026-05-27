//! Transaction mempool — sans-IO state machine.
//!
//! Holds pending transactions for inclusion in a block (RB body or EB
//! body) plus the per-peer "already advertised" sets that prevent
//! re-announcing the same tx to the same peer.  Bounded by a tx count
//! capacity; the oldest tx is evicted on overflow.
//!
//! Tx bodies live in two compartments under one roof:
//!
//! - `txs` — the FIFO queue of free txs, drained for the next RB body
//!   and advertised through TxSubmission.
//! - `eb_pinned` — bodies pinned because they're referenced by an EB
//!   that hasn't been settled yet.  Lookups (LeiosFetch BlockTxs server,
//!   the CIP-0164 `MissingTX` voting predicate) consult both
//!   transparently via [`MempoolState::has_tx`] /
//!   [`MempoolState::get_body_by_id`].
//!
//! Validation crosses this crate's boundary as an effect / response pair,
//! the same pattern Praos uses for block validation and Leios uses for
//! EB / vote validation:
//!
//! ```text
//!  on_tx_received(tx_id, body)    →  emit ValidateTx
//!                                    (wrapper validates)
//!  on_tx_validated(tx_id, size)   →  admit + (caller pulls advertise list)
//!  on_tx_validation_failed(...)   →  emit TxRejected
//! ```
//!
//! Locally-generated transactions skip the dance via
//! [`MempoolState::admit_validated`].

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::{Arc, Mutex};

use tracing::info;

use crate::behaviour::{Behaviour, BehaviourOutcome, HonestBehaviour};
use crate::peer::PeerId;

/// Slot-window retention for EB-pinned bodies.  Holds wide enough that
/// every active voting / certification window stays serveable; pruned
/// entries are dropped on every EB observation.
pub const DEFAULT_EB_RETENTION_SLOTS: u64 = 100;

/// Identifier for an Endorser Block: `(slot, hash)`.  The `hash` half
/// is a Blake2b-256 over the EB's wire bytes — the wrapper picks the
/// hash scheme and supplies it on every entry path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct EbKey {
    pub slot: u64,
    pub hash: [u8; 32],
}

/// Opaque transaction identifier.  Conventionally Blake2b-256 of the
/// body, but this crate doesn't enforce that — the wrapper picks the hash
/// scheme and supplies it on every entry path.
pub type TxId = Vec<u8>;

/// A transaction body the mempool is holding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PendingTx {
    pub tx_id: TxId,
    pub body: Vec<u8>,
    pub size: u32,
}

// ---------------------------------------------------------------------------
// Effect type
// ---------------------------------------------------------------------------

/// What the I/O layer should do as a result of a state mutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MempoolEffect {
    /// Submit `body` to the wrapper's transaction validator.  When the
    /// validator returns, the wrapper calls
    /// [`MempoolState::on_tx_validated`] or
    /// [`MempoolState::on_tx_validation_failed`].
    ValidateTx { tx_id: TxId, body: Vec<u8> },
    /// A tx was dropped before reaching the mempool (overflow,
    /// validation failure) or evicted from it.  Telemetry only — the
    /// wrapper forwards this to its events sink.
    TxRejected {
        tx_id: TxId,
        reason: TxRejectReason,
    },
}

/// Why a tx was rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TxRejectReason {
    /// Mempool was at capacity; the oldest tx was evicted to admit a
    /// newly-validated tx.  The evicted tx_id is the one carried in
    /// the `TxRejected` effect.
    QueueFull,
    /// The wrapper's validator returned a failure.
    ValidationFailed(String),
    /// Already in the mempool or already pending validation; the
    /// duplicate body was discarded.
    AlreadyKnown,
    /// The tx was pinned under an EB whose manifest aged past the
    /// retention window (`eb_retention_slots` slots behind
    /// `max_eb_slot`).  No surviving manifest referenced this body, so
    /// it was released from `eb_pinned`.  Sim adapters map this to
    /// their `EBExpired` tx-loss reason.
    EbClosurePruned,
}

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// Transaction mempool.
///
/// Fields are `pub` for adapter inspection, matching the convention
/// of [`crate::praos::PraosState`] and [`crate::leios::LeiosState`].
/// Treat them as state-machine internals: prefer the public methods,
/// which preserve invariants.
pub struct MempoolState {
    /// Admitted transactions in arrival order — the "free" pool drained
    /// for RB body inclusion.
    pub txs: VecDeque<PendingTx>,
    /// Membership index over `txs`, kept in lockstep with every push /
    /// pop / retain so `contains` and `current_tx_ids` are `O(log n)`
    /// instead of a linear scan.
    pub tx_index: BTreeSet<TxId>,
    /// Sum of `tx.size` across `txs`.
    pub total_bytes: usize,
    /// Maximum transaction count for `txs`.
    pub capacity: usize,
    /// Per-peer "already advertised to this peer" set, so the
    /// TxSubmission server never re-announces the same tx to the same
    /// peer.
    pub peer_advertised: BTreeMap<PeerId, BTreeSet<TxId>>,
    /// Bodies currently with the validator.  Cleared on
    /// `on_tx_validated` (body moves to `txs`) or
    /// `on_tx_validation_failed` (body dropped).
    pub pending_validation: BTreeMap<TxId, Vec<u8>>,
    /// Per-EB ordered tx-hash list — the "EB Body" in CIP-0164 terms.
    /// Producers populate this from `produce_eb`; receivers from
    /// `record_eb_manifest` after decoding a fetched EB body.
    pub eb_manifests: BTreeMap<EbKey, Vec<TxId>>,
    /// EB-pinned bodies, keyed by `tx_id`.  A body lands here when the
    /// producer drains it into an EB (so it leaves `txs` but stays
    /// serveable) or when a receiver fetches it via LeiosFetch.  Drops
    /// out of the slot retention window prune away EBs whose manifests
    /// no longer reference a body in here.
    pub eb_pinned: BTreeMap<TxId, PendingTx>,
    /// Highest EB slot observed.  Drives slot-window retention.
    pub max_eb_slot: u64,
    /// EB retention window in slots.  Manifests + pinned bodies older
    /// than `max_eb_slot - eb_retention_slots` are evicted on every
    /// `record_eb_manifest` / `produce_eb` call.
    pub eb_retention_slots: u64,
    /// Pluggable behaviour for tx-acceptance and admission hooks.  See
    /// [`crate::behaviour`].  Shared with the I/O wrapper via
    /// `Arc<Mutex<>>` so out-of-band callers can lock the same instance.
    pub behaviour: Arc<Mutex<Box<dyn Behaviour>>>,
}

impl MempoolState {
    pub fn new(capacity: usize) -> Self {
        Self::new_with_eb_retention(capacity, DEFAULT_EB_RETENTION_SLOTS)
    }

    /// Construct with an explicit EB-body retention window.
    pub fn new_with_eb_retention(capacity: usize, eb_retention_slots: u64) -> Self {
        Self {
            txs: VecDeque::new(),
            tx_index: BTreeSet::new(),
            total_bytes: 0,
            capacity,
            peer_advertised: BTreeMap::new(),
            pending_validation: BTreeMap::new(),
            eb_manifests: BTreeMap::new(),
            eb_pinned: BTreeMap::new(),
            max_eb_slot: 0,
            eb_retention_slots,
            behaviour: Arc::new(Mutex::new(Box::new(HonestBehaviour))),
        }
    }

    /// Replace the behaviour.  Swaps the trait object under the mutex.
    pub fn set_behaviour(&mut self, behaviour: Box<dyn Behaviour>) {
        *self.behaviour.lock().expect("behaviour mutex poisoned") = behaviour;
    }

    /// Lock the behaviour and call the hook with `(&mut dyn Behaviour,
    /// &MempoolState)`.
    fn invoke_hook<F>(&mut self, hook: F) -> BehaviourOutcome<MempoolEffect>
    where
        F: FnOnce(&mut dyn Behaviour, &MempoolState) -> BehaviourOutcome<MempoolEffect>,
    {
        let arc = self.behaviour.clone();
        let mut guard = arc.lock().expect("behaviour mutex poisoned");
        hook(&mut **guard, self)
    }

    // -- Network event handlers --------------------------------------------

    /// A tx body arrived from the network.  If the mempool already
    /// holds it (or it's pending validation), emits `TxRejected` with
    /// `AlreadyKnown` and discards.  Otherwise records the body and
    /// emits `ValidateTx`; the wrapper validates and reports back via
    /// [`Self::on_tx_validated`] or [`Self::on_tx_validation_failed`].
    pub fn on_tx_received(&mut self, tx_id: TxId, body: Vec<u8>) -> Vec<MempoolEffect> {
        let appended: Vec<MempoolEffect> =
            match self.invoke_hook(|b, s| b.on_tx_received(s, &tx_id, &body)) {
                BehaviourOutcome::Continue => Vec::new(),
                BehaviourOutcome::Replace(effects) => return effects,
                BehaviourOutcome::Append(extra) => extra,
            };
        if self.pending_validation.contains_key(&tx_id) || self.contains(&tx_id) {
            let mut fx = vec![MempoolEffect::TxRejected {
                tx_id,
                reason: TxRejectReason::AlreadyKnown,
            }];
            fx.extend(appended);
            return fx;
        }
        self.pending_validation.insert(tx_id.clone(), body.clone());
        let mut fx = vec![MempoolEffect::ValidateTx { tx_id, body }];
        fx.extend(appended);
        fx
    }

    // -- Validation outcomes -----------------------------------------------

    /// Validator confirmed the body for `tx_id` — admit it.  If the
    /// queue is at capacity, evicts the oldest tx and emits a
    /// `TxRejected { reason: QueueFull }` for it.  No-op if the
    /// tx_id wasn't pending validation.
    pub fn on_tx_validated(&mut self, tx_id: TxId, size: u32) -> Vec<MempoolEffect> {
        let appended: Vec<MempoolEffect> =
            match self.invoke_hook(|b, s| b.on_tx_validated(s, &tx_id, size)) {
                BehaviourOutcome::Continue => Vec::new(),
                BehaviourOutcome::Replace(effects) => return effects,
                BehaviourOutcome::Append(extra) => extra,
            };
        let Some(body) = self.pending_validation.remove(&tx_id) else {
            return appended;
        };
        let mut fx = self.admit_internal(tx_id, body, size);
        fx.extend(appended);
        fx
    }

    /// Validator rejected `tx_id`.  Drops the pending body and emits
    /// `TxRejected { ValidationFailed }`.
    pub fn on_tx_validation_failed(
        &mut self,
        tx_id: TxId,
        reason: String,
    ) -> Vec<MempoolEffect> {
        self.pending_validation.remove(&tx_id);
        vec![MempoolEffect::TxRejected {
            tx_id,
            reason: TxRejectReason::ValidationFailed(reason),
        }]
    }

    /// Admit a tx that's already been validated externally — typically
    /// a locally-produced tx the wrapper has validated against its own
    /// ledger view, or a test fixture.  Bypasses the
    /// `on_tx_received` → `ValidateTx` → `on_tx_validated` dance.
    pub fn admit_validated(
        &mut self,
        tx_id: TxId,
        body: Vec<u8>,
        size: u32,
    ) -> Vec<MempoolEffect> {
        if self.contains(&tx_id) {
            return vec![MempoolEffect::TxRejected {
                tx_id,
                reason: TxRejectReason::AlreadyKnown,
            }];
        }
        // If a validation was in flight for this id, drop it — the
        // local admission supersedes.
        self.pending_validation.remove(&tx_id);
        self.admit_internal(tx_id, body, size)
    }

    // -- Block lifecycle ---------------------------------------------------

    /// A block was applied — the listed txs are now on-chain.  Drops
    /// them from the mempool (their inputs are spent).  No-op for ids
    /// not in the mempool.
    pub fn on_block_applied(&mut self, included_tx_ids: &[TxId]) {
        if included_tx_ids.is_empty() {
            return;
        }
        let included: BTreeSet<&TxId> = included_tx_ids.iter().collect();
        let before = self.txs.len();
        self.txs.retain(|tx| !included.contains(&tx.tx_id));
        if self.txs.len() == before {
            return;
        }
        for tx_id in included_tx_ids {
            self.tx_index.remove(tx_id);
        }
        self.total_bytes = self.txs.iter().map(|tx| tx.size as usize).sum();
        for tx_id in included_tx_ids {
            self.prune_from_peer_sets(tx_id);
        }
    }

    /// A block was rolled back.  Mempool entries that were dropped on
    /// `on_block_applied` for that block stay dropped (they re-enter
    /// via the normal arrival path if the wrapper re-submits them).
    /// No-op today; here for parity with the Praos / Leios surface
    /// and to give wrappers a hook for future re-admit logic.
    pub fn on_block_rolled_back(&mut self) {}

    // -- Peer lifecycle ----------------------------------------------------

    /// Drop per-peer advertised state on disconnect.
    pub fn forget_peer(&mut self, peer_id: PeerId) {
        self.peer_advertised.remove(&peer_id);
    }

    // -- Pure queries ------------------------------------------------------

    /// All admitted tx ids.  Used by the Leios layer's MissingTX
    /// voting predicate (via the snapshot the wrapper passes into
    /// `LeiosState::on_slot`).
    pub fn current_tx_ids(&self) -> BTreeSet<TxId> {
        self.tx_index.clone()
    }

    /// True iff `tx_id` is in the mempool.
    pub fn contains(&self, tx_id: &TxId) -> bool {
        self.tx_index.contains(tx_id)
    }

    /// Look up a tx body by its id across both compartments — the free
    /// FIFO pool and the EB-pinned pool.  Linear scan over `txs`;
    /// mempool sizes this prototype targets keep it acceptable.  Used
    /// by the LeiosFetch BlockTxs server (via the `TxBodyResolver`
    /// trait in the consumer's wrapper) to resolve manifest entries.
    pub fn get_body_by_id(&self, id: &[u8]) -> Option<Vec<u8>> {
        if let Some(body) = self
            .txs
            .iter()
            .find(|tx| tx.tx_id == id)
            .map(|tx| tx.body.clone())
        {
            return Some(body);
        }
        self.eb_pinned.get(id).map(|tx| tx.body.clone())
    }

    /// Return up to `max_count` txs not yet advertised to `peer_id`,
    /// recording them so subsequent calls skip them.  The per-peer
    /// advertised set is pruned automatically when txs leave the
    /// mempool.  Hot path under TxSubmission pull traffic; the
    /// `contains` check before the clone-and-insert avoids the heap
    /// allocation for tx ids the peer already has.
    pub fn peek_unannounced_for_peer(
        &mut self,
        peer_id: PeerId,
        max_count: usize,
    ) -> Vec<PendingTx> {
        let mut result = Vec::with_capacity(max_count);
        let advertised = self.peer_advertised.entry(peer_id).or_default();
        for tx in &self.txs {
            if result.len() >= max_count {
                break;
            }
            if !advertised.contains(&tx.tx_id) {
                advertised.insert(tx.tx_id.clone());
                result.push(tx.clone());
            }
        }
        result
    }

    /// Mark `tx_id` as advertised to `peer_id`.  Returns `true` iff the
    /// entry was newly inserted (the caller still needs to send the tx
    /// body to that peer).  Used by the admit-fanout path to announce
    /// a single just-admitted tx to every connected peer in O(log N)
    /// per peer.
    pub fn mark_announced_to_peer(&mut self, peer_id: PeerId, tx_id: &TxId) -> bool {
        self.peer_advertised
            .entry(peer_id)
            .or_default()
            .insert(tx_id.clone())
    }

    /// Drain txs from the front of the queue up to `max_bytes`.  At
    /// least one tx is always returned if the queue is non-empty,
    /// even if it exceeds `max_bytes` on its own.  Used for RB body
    /// production.
    pub fn drain_up_to(&mut self, max_bytes: usize) -> Vec<PendingTx> {
        let mut result = Vec::new();
        let mut bytes = 0usize;
        while let Some(front) = self.txs.front() {
            let next_bytes = bytes + front.size as usize;
            if next_bytes > max_bytes && !result.is_empty() {
                break;
            }
            let tx = self.txs.pop_front().unwrap();
            self.tx_index.remove(&tx.tx_id);
            bytes = next_bytes;
            self.total_bytes -= tx.size as usize;
            result.push(tx);
            if bytes >= max_bytes {
                break;
            }
        }
        for tx in &result {
            self.prune_from_peer_sets(&tx.tx_id);
        }
        result
    }

    /// Drain everything (for EB overflow path).
    pub fn drain_all(&mut self) -> Vec<PendingTx> {
        self.total_bytes = 0;
        let drained: Vec<PendingTx> = self.txs.drain(..).collect();
        self.tx_index.clear();
        for tx in &drained {
            self.prune_from_peer_sets(&tx.tx_id);
        }
        drained
    }

    pub fn total_bytes(&self) -> usize {
        self.total_bytes
    }

    pub fn len(&self) -> usize {
        self.txs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.txs.is_empty()
    }

    /// Emit an `info!` line summarising the sizes of every internal
    /// collection.  Used by adapters to monitor memory growth — if any
    /// collection grows without bound across consecutive lines, that's
    /// the leak.
    pub fn log_state_sizes(&self, node_id: &str) {
        let peer_advertised_total: usize =
            self.peer_advertised.values().map(|s| s.len()).sum();
        let peer_advertised_max: usize = self
            .peer_advertised
            .values()
            .map(|s| s.len())
            .max()
            .unwrap_or(0);
        let eb_manifest_entries_total: usize =
            self.eb_manifests.values().map(|v| v.len()).sum();
        info!(
            node_id,
            txs = self.txs.len(),
            tx_index = self.tx_index.len(),
            total_bytes = self.total_bytes,
            peer_advertised = self.peer_advertised.len(),
            peer_advertised_total,
            peer_advertised_max,
            pending_validation = self.pending_validation.len(),
            eb_manifests = self.eb_manifests.len(),
            eb_manifest_entries_total,
            eb_pinned = self.eb_pinned.len(),
            "mempool state sizes"
        );
    }

    // -- EB body management ------------------------------------------------

    /// Producer-side: drain the first `count` free txs, pin their
    /// bodies under the new EB key, and return the manifest (ordered
    /// tx-hash list) for the wrapper to encode into the EB's wire
    /// bytes.  The remaining free txs stay in the mempool for the
    /// next RB.  The pinned bodies stay serveable via LeiosFetch and
    /// visible to the `MissingTX` voting predicate.
    ///
    /// `count` must come from `BodyPath::manifest.len()` — pairing the
    /// size-capped manifest selection with a matching prefix drain.
    ///
    /// Returns the manifest and any `TxRejected{EbClosurePruned}`
    /// effects emitted when older EB closures aged out of the
    /// retention window.
    pub fn produce_eb(
        &mut self,
        eb_key: EbKey,
        count: usize,
    ) -> (Vec<TxId>, Vec<MempoolEffect>) {
        let take = count.min(self.txs.len());
        let mut drained: Vec<PendingTx> = Vec::with_capacity(take);
        for _ in 0..take {
            let tx = self.txs.pop_front().expect("checked len");
            self.tx_index.remove(&tx.tx_id);
            self.total_bytes -= tx.size as usize;
            // Drained txs leave the free pool and become EB-pinned; the
            // chain commits them, so they no longer need re-advertising
            // via TxSubmission.  Without this prune, every peer's
            // advertised-tx set grows unboundedly across the lifetime
            // of the producer.
            self.prune_from_peer_sets(&tx.tx_id);
            drained.push(tx);
        }
        let manifest: Vec<TxId> = drained.iter().map(|tx| tx.tx_id.clone()).collect();
        for tx in drained {
            self.eb_pinned.entry(tx.tx_id.clone()).or_insert(tx);
        }
        self.eb_manifests.insert(eb_key, manifest.clone());
        let fx = self.bump_eb_slot(eb_key.slot);
        (manifest, fx)
    }

    /// Receiver-side: register the manifest of an EB whose body bytes
    /// the wrapper has just decoded.  Bodies arrive separately via
    /// `merge_eb_body` as LeiosFetch responses come in.  No-op if a
    /// manifest is already recorded for this `eb_key` (first writer
    /// wins — manifests are content-addressed via the EB hash).
    ///
    /// Returns any `TxRejected{EbClosurePruned}` effects emitted when
    /// older EB closures aged out of the retention window.
    pub fn record_eb_manifest(&mut self, eb_key: EbKey, manifest: Vec<TxId>) -> Vec<MempoolEffect> {
        self.eb_manifests.entry(eb_key).or_insert(manifest);
        self.bump_eb_slot(eb_key.slot)
    }

    /// Receiver-side: insert a body fetched via LeiosFetch.  `tx_id`
    /// must be the integrity-verified Blake2b-256 of `body` — the
    /// wrapper hashes incoming bodies and matches against the manifest
    /// before calling here.  No-op if the tx is already known via
    /// `txs` or `eb_pinned`.
    pub fn merge_eb_body(&mut self, tx_id: TxId, body: Vec<u8>, size: u32) {
        if self.contains(&tx_id) || self.eb_pinned.contains_key(&tx_id) {
            return;
        }
        self.eb_pinned.insert(
            tx_id.clone(),
            PendingTx {
                tx_id,
                body,
                size,
            },
        );
    }

    /// True iff the body for `tx_id` is locally available — either
    /// in the free FIFO pool or pinned under an EB.  Used by the
    /// CIP-0164 `MissingTX` voting predicate.
    pub fn has_tx(&self, tx_id: &TxId) -> bool {
        self.contains(tx_id) || self.eb_pinned.contains_key(tx_id)
    }

    /// Manifest (ordered tx-hash list) for the given EB, if recorded.
    pub fn get_eb_manifest(&self, eb_key: &EbKey) -> Option<&[TxId]> {
        self.eb_manifests.get(eb_key).map(Vec::as_slice)
    }

    /// Resolve a bitmap-of-indices request for an EB's bodies.
    /// Returns `None` if the EB's manifest isn't recorded; otherwise
    /// returns bodies for every requested index whose body is locally
    /// resolvable.  Out-of-range indices and indices whose body is
    /// missing are silently dropped (partial response).
    pub fn get_eb_bodies<I>(&self, eb_key: &EbKey, indices: I) -> Option<Vec<Vec<u8>>>
    where
        I: IntoIterator<Item = u32>,
    {
        let manifest = self.eb_manifests.get(eb_key)?;
        let bodies: Vec<Vec<u8>> = indices
            .into_iter()
            .filter_map(|i| {
                let tx_id = manifest.get(i as usize)?;
                self.get_body_by_id(tx_id)
            })
            .collect();
        Some(bodies)
    }

    /// Manifest indices whose body is **not** locally available.
    /// Drives a receiver's outgoing `LeiosFetch BlockTxs` bitmap.
    pub fn missing_eb_indices(&self, eb_key: &EbKey) -> Vec<u32> {
        let Some(manifest) = self.eb_manifests.get(eb_key) else {
            return Vec::new();
        };
        manifest
            .iter()
            .enumerate()
            .filter(|(_, id)| !self.has_tx(id))
            .map(|(i, _)| i as u32)
            .collect()
    }

    // -- Internal helpers --------------------------------------------------

    fn bump_eb_slot(&mut self, slot: u64) -> Vec<MempoolEffect> {
        self.max_eb_slot = self.max_eb_slot.max(slot);
        self.prune_eb_slot_window()
    }

    /// Drop EB manifests older than the retention window.  Pinned
    /// bodies that no surviving manifest references are released too —
    /// otherwise the producer's drain-into-EB path would leak them
    /// forever.  Each released body produces an `EbClosurePruned`
    /// `TxRejected` effect so consumers can record the tx loss.
    fn prune_eb_slot_window(&mut self) -> Vec<MempoolEffect> {
        let cutoff = self.max_eb_slot.saturating_sub(self.eb_retention_slots);
        if cutoff == 0 {
            return Vec::new();
        }
        self.eb_manifests.retain(|key, _| key.slot >= cutoff);
        let still_referenced: BTreeSet<TxId> = self
            .eb_manifests
            .values()
            .flat_map(|m| m.iter().cloned())
            .collect();
        let mut fx = Vec::new();
        self.eb_pinned.retain(|id, _| {
            if still_referenced.contains(id) {
                true
            } else {
                fx.push(MempoolEffect::TxRejected {
                    tx_id: id.clone(),
                    reason: TxRejectReason::EbClosurePruned,
                });
                false
            }
        });
        fx
    }

    fn admit_internal(
        &mut self,
        tx_id: TxId,
        body: Vec<u8>,
        size: u32,
    ) -> Vec<MempoolEffect> {
        let mut fx = Vec::new();
        if self.txs.len() >= self.capacity {
            if let Some(old) = self.txs.pop_front() {
                self.tx_index.remove(&old.tx_id);
                self.total_bytes -= old.size as usize;
                let evicted_id = old.tx_id.clone();
                self.prune_from_peer_sets(&evicted_id);
                info!(
                    evicted = ?hex_short(&evicted_id),
                    capacity = self.capacity,
                    "mempool: evicting oldest tx to make room"
                );
                fx.push(MempoolEffect::TxRejected {
                    tx_id: evicted_id,
                    reason: TxRejectReason::QueueFull,
                });
            }
        }
        self.total_bytes += size as usize;
        self.tx_index.insert(tx_id.clone());
        self.txs.push_back(PendingTx {
            tx_id,
            body,
            size,
        });
        fx
    }

    fn prune_from_peer_sets(&mut self, tx_id: &TxId) {
        for set in self.peer_advertised.values_mut() {
            set.remove(tx_id);
        }
    }
}

fn hex_short(id: &[u8]) -> String {
    id.iter()
        .take(4)
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pid(n: u64) -> PeerId {
        PeerId(n)
    }

    fn tx(id: u8, size: u32) -> (TxId, Vec<u8>, u32) {
        (vec![id; 32], vec![0u8; size as usize], size)
    }

    fn admit(state: &mut MempoolState, id: u8, size: u32) -> Vec<MempoolEffect> {
        let (tx_id, body, sz) = tx(id, size);
        state.admit_validated(tx_id, body, sz)
    }

    // -- on_tx_received → ValidateTx dance ---------------------------------

    #[test]
    fn on_tx_received_emits_validate_tx() {
        let mut s = MempoolState::new(10);
        let (tx_id, body, _) = tx(1, 100);
        let fx = s.on_tx_received(tx_id.clone(), body.clone());
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            MempoolEffect::ValidateTx { tx_id: id, body: b } => {
                assert_eq!(*id, tx_id);
                assert_eq!(*b, body);
            }
            other => panic!("expected ValidateTx, got {other:?}"),
        }
        assert!(s.pending_validation.contains_key(&tx_id));
    }

    #[test]
    fn on_tx_received_dedup_pending_returns_already_known() {
        let mut s = MempoolState::new(10);
        let (tx_id, body, _) = tx(1, 100);
        let _ = s.on_tx_received(tx_id.clone(), body.clone());
        // Second arrival while pending.
        let fx = s.on_tx_received(tx_id.clone(), body);
        assert_eq!(fx.len(), 1);
        assert!(matches!(
            fx[0],
            MempoolEffect::TxRejected {
                reason: TxRejectReason::AlreadyKnown,
                ..
            }
        ));
    }

    #[test]
    fn on_tx_received_dedup_admitted_returns_already_known() {
        let mut s = MempoolState::new(10);
        let _ = admit(&mut s, 1, 100);
        let (tx_id, body, _) = tx(1, 100);
        let fx = s.on_tx_received(tx_id, body);
        assert!(matches!(
            fx[0],
            MempoolEffect::TxRejected {
                reason: TxRejectReason::AlreadyKnown,
                ..
            }
        ));
    }

    #[test]
    fn on_tx_validated_admits_to_queue() {
        let mut s = MempoolState::new(10);
        let (tx_id, body, sz) = tx(1, 100);
        let _ = s.on_tx_received(tx_id.clone(), body);
        let fx = s.on_tx_validated(tx_id.clone(), sz);
        assert!(fx.is_empty()); // no overflow → no effect
        assert_eq!(s.len(), 1);
        assert_eq!(s.total_bytes(), 100);
        assert!(!s.pending_validation.contains_key(&tx_id));
    }

    #[test]
    fn on_tx_validated_unknown_id_is_noop() {
        let mut s = MempoolState::new(10);
        let (tx_id, _, _) = tx(99, 0);
        let fx = s.on_tx_validated(tx_id, 100);
        assert!(fx.is_empty());
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn on_tx_validation_failed_emits_rejected() {
        let mut s = MempoolState::new(10);
        let (tx_id, body, _) = tx(1, 100);
        let _ = s.on_tx_received(tx_id.clone(), body);
        let fx = s.on_tx_validation_failed(tx_id.clone(), "bad signature".into());
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            MempoolEffect::TxRejected {
                tx_id: id,
                reason: TxRejectReason::ValidationFailed(msg),
            } => {
                assert_eq!(*id, tx_id);
                assert_eq!(msg, "bad signature");
            }
            other => panic!("expected TxRejected ValidationFailed, got {other:?}"),
        }
        assert!(!s.pending_validation.contains_key(&tx_id));
    }

    // -- Capacity / overflow -----------------------------------------------

    #[test]
    fn admit_evicts_oldest_at_capacity() {
        let mut s = MempoolState::new(3);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 200);
        admit(&mut s, 3, 300);
        assert_eq!(s.len(), 3);
        let fx = admit(&mut s, 4, 400);
        // tx 1 evicted.
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            MempoolEffect::TxRejected {
                tx_id,
                reason: TxRejectReason::QueueFull,
            } => {
                assert_eq!(*tx_id, vec![1u8; 32]);
            }
            other => panic!("expected TxRejected QueueFull, got {other:?}"),
        }
        assert_eq!(s.len(), 3);
        assert_eq!(s.total_bytes(), 200 + 300 + 400);
    }

    // -- Block lifecycle ---------------------------------------------------

    #[test]
    fn on_block_applied_removes_included_txs() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 200);
        admit(&mut s, 3, 300);
        let included = vec![vec![1u8; 32], vec![3u8; 32]];
        s.on_block_applied(&included);
        assert_eq!(s.len(), 1);
        assert_eq!(s.txs.front().unwrap().tx_id, vec![2u8; 32]);
        assert_eq!(s.total_bytes(), 200);
    }

    #[test]
    fn on_block_applied_empty_is_noop() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        s.on_block_applied(&[]);
        assert_eq!(s.len(), 1);
    }

    #[test]
    fn on_block_applied_unknown_ids_is_noop() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        s.on_block_applied(&[vec![99u8; 32]]);
        assert_eq!(s.len(), 1);
    }

    // -- Drains ------------------------------------------------------------

    #[test]
    fn drain_up_to_respects_byte_limit() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 200);
        admit(&mut s, 3, 300);
        let drained = s.drain_up_to(250);
        // Tx 1 (100) fits; tx 2 would push to 300 > 250 → stop.
        assert_eq!(drained.len(), 1);
        assert_eq!(s.len(), 2);
        assert_eq!(s.total_bytes(), 500);
    }

    #[test]
    fn drain_up_to_takes_at_least_one_even_if_oversize() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 1000);
        let drained = s.drain_up_to(500);
        // First tx exceeds limit but is still taken (avoids deadlock
        // when the next tx is bigger than max_bytes).
        assert_eq!(drained.len(), 1);
        assert!(s.is_empty());
    }

    #[test]
    fn drain_all_empties() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 200);
        let drained = s.drain_all();
        assert_eq!(drained.len(), 2);
        assert!(s.is_empty());
        assert_eq!(s.total_bytes(), 0);
    }

    // -- Per-peer advertised set -------------------------------------------

    #[test]
    fn peek_unannounced_returns_each_tx_once_per_peer() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 100);
        let peer = pid(0);
        let first = s.peek_unannounced_for_peer(peer, 10);
        assert_eq!(first.len(), 2);
        let second = s.peek_unannounced_for_peer(peer, 10);
        assert!(second.is_empty());
    }

    #[test]
    fn peek_unannounced_independent_per_peer() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        let to_a = s.peek_unannounced_for_peer(pid(0), 10);
        let to_b = s.peek_unannounced_for_peer(pid(1), 10);
        assert_eq!(to_a.len(), 1);
        assert_eq!(to_b.len(), 1);
    }

    #[test]
    fn admit_after_peek_returns_only_new_tx() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        let peer = pid(0);
        assert_eq!(s.peek_unannounced_for_peer(peer, 10).len(), 1);
        admit(&mut s, 2, 100);
        let next = s.peek_unannounced_for_peer(peer, 10);
        assert_eq!(next.len(), 1);
        assert_eq!(next[0].tx_id, vec![2u8; 32]);
    }

    #[test]
    fn capacity_eviction_prunes_peer_sets() {
        let mut s = MempoolState::new(2);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 100);
        let peer = pid(0);
        let _ = s.peek_unannounced_for_peer(peer, 10);
        admit(&mut s, 3, 100);
        let advertised = s.peer_advertised.get(&peer).unwrap();
        assert!(!advertised.contains(&vec![1u8; 32]));
        assert!(advertised.contains(&vec![2u8; 32]));
    }

    #[test]
    fn drain_up_to_prunes_peer_sets() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 100);
        let peer = pid(0);
        let _ = s.peek_unannounced_for_peer(peer, 10);
        let _ = s.drain_up_to(10_000);
        assert!(s
            .peer_advertised
            .get(&peer)
            .map(|set| set.is_empty())
            .unwrap_or(true));
    }

    #[test]
    fn on_block_applied_prunes_peer_sets() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 100);
        let peer = pid(0);
        let _ = s.peek_unannounced_for_peer(peer, 10);
        s.on_block_applied(&[vec![1u8; 32]]);
        let advertised = s.peer_advertised.get(&peer).unwrap();
        assert!(!advertised.contains(&vec![1u8; 32]));
        assert!(advertised.contains(&vec![2u8; 32]));
    }

    #[test]
    fn forget_peer_drops_state() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        let peer = pid(0);
        let _ = s.peek_unannounced_for_peer(peer, 10);
        assert!(s.peer_advertised.contains_key(&peer));
        s.forget_peer(peer);
        assert!(!s.peer_advertised.contains_key(&peer));
    }

    // -- admit_validated bypass --------------------------------------------

    #[test]
    fn admit_validated_skips_validation_dance() {
        let mut s = MempoolState::new(10);
        let (tx_id, body, sz) = tx(1, 100);
        let fx = s.admit_validated(tx_id.clone(), body, sz);
        assert!(fx.is_empty());
        assert_eq!(s.len(), 1);
        assert!(s.contains(&tx_id));
    }

    #[test]
    fn admit_validated_dedup_returns_already_known() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        let (tx_id, body, sz) = tx(1, 100);
        let fx = s.admit_validated(tx_id, body, sz);
        assert!(matches!(
            fx[0],
            MempoolEffect::TxRejected {
                reason: TxRejectReason::AlreadyKnown,
                ..
            }
        ));
    }

    #[test]
    fn admit_validated_clears_pending_validation() {
        // If the same tx was already in flight via on_tx_received,
        // admit_validated supersedes — pending entry dropped.
        let mut s = MempoolState::new(10);
        let (tx_id, body, sz) = tx(1, 100);
        let _ = s.on_tx_received(tx_id.clone(), body.clone());
        assert!(s.pending_validation.contains_key(&tx_id));
        let _ = s.admit_validated(tx_id.clone(), body, sz);
        assert!(!s.pending_validation.contains_key(&tx_id));
        assert_eq!(s.len(), 1);
    }

    // -- EB body management ------------------------------------------------

    fn eb_key(slot: u64, hash_byte: u8) -> EbKey {
        EbKey {
            slot,
            hash: [hash_byte; 32],
        }
    }

    #[test]
    fn produce_eb_drains_txs_into_pinned_and_returns_manifest() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 200);
        admit(&mut s, 3, 300);

        let eb = eb_key(50, 0xEE);
        let (manifest, evictions) = s.produce_eb(eb, 3);

        assert_eq!(manifest, vec![vec![1u8; 32], vec![2u8; 32], vec![3u8; 32]]);
        assert!(evictions.is_empty(), "no older EBs to evict yet");
        assert!(s.is_empty(), "txs are drained");
        assert_eq!(s.total_bytes(), 0);
        assert!(s.eb_pinned.contains_key(&vec![1u8; 32]));
        assert_eq!(s.get_eb_manifest(&eb), Some(manifest.as_slice()));
    }

    #[test]
    fn has_tx_unions_free_pool_and_pinned_bodies() {
        let mut s = MempoolState::new(10);
        admit(&mut s, 1, 100);
        admit(&mut s, 2, 200);
        let eb = eb_key(10, 0x11);
        let _ = s.produce_eb(eb, 2);
        // Both still locally available, just under different roofs.
        assert!(s.has_tx(&vec![1u8; 32]));
        assert!(s.has_tx(&vec![2u8; 32]));
        assert!(!s.has_tx(&vec![99u8; 32]));
        // After draining into an EB, a new tx in the free pool is also has_tx-true.
        admit(&mut s, 3, 100);
        assert!(s.has_tx(&vec![3u8; 32]));
    }

    #[test]
    fn get_body_by_id_resolves_from_either_compartment() {
        let mut s = MempoolState::new(10);
        let (id1, body1, sz1) = tx(1, 50);
        s.admit_validated(id1.clone(), body1.clone(), sz1);
        s.produce_eb(eb_key(5, 0x55), 1);
        // Now id1 is in eb_pinned, not txs.
        assert_eq!(s.get_body_by_id(&id1), Some(body1));
        // A fresh free tx resolves from `txs`.
        let (id2, body2, sz2) = tx(2, 60);
        s.admit_validated(id2.clone(), body2.clone(), sz2);
        assert_eq!(s.get_body_by_id(&id2), Some(body2));
        assert_eq!(s.get_body_by_id(&[99u8; 32]), None);
    }

    #[test]
    fn record_eb_manifest_for_receiver_then_merge_bodies() {
        // Receiver-side flow: see the EB header → fetch body → decode
        // manifest → record. Bodies arrive later via merge_eb_body.
        let mut s = MempoolState::new(10);
        let id_a = vec![0xAAu8; 32];
        let id_b = vec![0xBBu8; 32];
        let eb = eb_key(20, 0x77);
        s.record_eb_manifest(eb, vec![id_a.clone(), id_b.clone()]);

        // Before any bodies, both indices are missing.
        assert_eq!(s.missing_eb_indices(&eb), vec![0, 1]);

        // Merge the second body first (out-of-order delivery is fine).
        s.merge_eb_body(id_b.clone(), vec![0xB0], 1);
        assert_eq!(s.missing_eb_indices(&eb), vec![0]);
        assert!(s.has_tx(&id_b));

        // Then the first.
        s.merge_eb_body(id_a.clone(), vec![0xA0], 1);
        assert!(s.missing_eb_indices(&eb).is_empty());
    }

    #[test]
    fn get_eb_bodies_returns_partial_subset_in_index_order() {
        let mut s = MempoolState::new(10);
        let ids: Vec<TxId> = (0..5).map(|i| vec![i as u8; 32]).collect();
        let eb = eb_key(30, 0x33);
        s.record_eb_manifest(eb, ids.clone());
        // Only bodies for indices 1 and 3 are locally available.
        s.merge_eb_body(ids[1].clone(), vec![0x11], 1);
        s.merge_eb_body(ids[3].clone(), vec![0x33], 1);

        // Server gets a bitmap request for [0, 1, 2, 3, 4]; returns only the
        // bodies it has, in ascending index order.
        let got = s.get_eb_bodies(&eb, 0..5).unwrap();
        assert_eq!(got, vec![vec![0x11], vec![0x33]]);
    }

    #[test]
    fn get_eb_bodies_returns_none_for_unknown_eb() {
        let s = MempoolState::new(10);
        let eb = eb_key(0, 0xFF);
        assert!(s.get_eb_bodies(&eb, 0..3).is_none());
    }

    #[test]
    fn merge_eb_body_idempotent_against_existing() {
        let mut s = MempoolState::new(10);
        let id = vec![0xCCu8; 32];
        s.record_eb_manifest(eb_key(40, 0x40), vec![id.clone()]);
        s.merge_eb_body(id.clone(), vec![0xCC], 1);
        // Second call with a different (faked) body must not overwrite.
        s.merge_eb_body(id.clone(), vec![0xFF], 1);
        assert_eq!(s.get_body_by_id(&id), Some(vec![0xCC]));
    }

    #[test]
    fn merge_eb_body_skipped_when_already_in_free_pool() {
        // If a tx is already in `txs` (via TxSubmission), don't double-store
        // it under eb_pinned.
        let mut s = MempoolState::new(10);
        let (id, body, sz) = tx(1, 100);
        s.admit_validated(id.clone(), body.clone(), sz);
        s.merge_eb_body(id.clone(), body, sz);
        assert_eq!(s.eb_pinned.len(), 0);
    }

    #[test]
    fn slot_retention_drops_old_eb_manifest_and_pinned_bodies() {
        // Tight window so the test stays small.
        let mut s = MempoolState::new_with_eb_retention(100, 5);
        let old_eb = eb_key(1, 0x01);
        let evicted_id = vec![0xAAu8; 32];
        let evictions_initial = s.record_eb_manifest(old_eb, vec![evicted_id.clone()]);
        assert!(evictions_initial.is_empty(), "no evictions on first record");
        s.merge_eb_body(evicted_id.clone(), vec![0xAA], 1);
        assert!(s.has_tx(&evicted_id));
        assert!(s.get_eb_manifest(&old_eb).is_some());

        // Push max_eb_slot far past the window.
        let evictions = s.record_eb_manifest(eb_key(100, 0x02), vec![vec![0xBBu8; 32]]);

        // Old EB and its body are evicted; new EB stays.
        assert!(s.get_eb_manifest(&old_eb).is_none());
        assert!(!s.has_tx(&evicted_id));
        assert!(s.get_eb_manifest(&eb_key(100, 0x02)).is_some());

        // The evicted body produces a TxRejected effect with the new
        // EbClosurePruned reason so adapters can record the tx loss.
        assert_eq!(
            evictions,
            vec![MempoolEffect::TxRejected {
                tx_id: evicted_id,
                reason: TxRejectReason::EbClosurePruned,
            }]
        );
    }

    #[test]
    fn produce_eb_emits_evictions_for_aged_pins() {
        let mut s = MempoolState::new_with_eb_retention(100, 5);
        // Old EB with a pinned body.
        let old_id = vec![0xAAu8; 32];
        let _ = s.record_eb_manifest(eb_key(1, 0x01), vec![old_id.clone()]);
        s.merge_eb_body(old_id.clone(), vec![0xAA], 1);

        // Produce a new EB far past the retention window — the
        // producer-side path also evicts the aged closure.
        admit(&mut s, 9, 100);
        let (_manifest, evictions) = s.produce_eb(eb_key(100, 0x02), 1);

        assert_eq!(
            evictions,
            vec![MempoolEffect::TxRejected {
                tx_id: old_id,
                reason: TxRejectReason::EbClosurePruned,
            }]
        );
    }

    #[test]
    fn slot_retention_keeps_body_referenced_by_a_surviving_eb() {
        // Same tx referenced by two EBs — pruning one shouldn't drop
        // the body if the other still references it.
        let mut s = MempoolState::new_with_eb_retention(100, 5);
        let id = vec![0xCCu8; 32];
        s.record_eb_manifest(eb_key(1, 0x01), vec![id.clone()]);
        s.record_eb_manifest(eb_key(95, 0x02), vec![id.clone()]);
        s.merge_eb_body(id.clone(), vec![0xCC], 1);
        // Bump max so the slot=1 EB falls out of the window but slot=95 stays.
        s.record_eb_manifest(eb_key(99, 0x03), vec![]);
        assert!(s.get_eb_manifest(&eb_key(1, 0x01)).is_none());
        assert!(s.get_eb_manifest(&eb_key(95, 0x02)).is_some());
        assert!(
            s.has_tx(&id),
            "body retained because the slot=95 EB still references it"
        );
    }
}
