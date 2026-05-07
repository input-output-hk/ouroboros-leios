//! Transaction mempool — sans-IO state machine.
//!
//! Holds pending transactions for inclusion in a block (RB body or EB
//! manifest) plus the per-peer "already advertised" sets that prevent
//! re-announcing the same tx to the same peer.  Bounded by a tx count
//! capacity; the oldest tx is evicted on overflow.
//!
//! Validation crosses the con-rs boundary as an effect / response pair,
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

use tracing::info;

use crate::peer::PeerId;

/// Opaque transaction identifier.  Conventionally Blake2b-256 of the
/// body, but con-rs doesn't enforce that — the wrapper picks the hash
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
#[derive(Debug, Clone)]
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
    /// Admitted transactions in arrival order.
    pub txs: VecDeque<PendingTx>,
    /// Sum of `tx.size` across `txs`.
    pub total_bytes: usize,
    /// Maximum transaction count.
    pub capacity: usize,
    /// Per-peer "already advertised to this peer" set, so the
    /// TxSubmission server (or sim-rs's announce loop) never
    /// re-announces the same tx to the same peer.
    pub peer_advertised: BTreeMap<PeerId, BTreeSet<TxId>>,
    /// Bodies currently with the validator.  Cleared on
    /// `on_tx_validated` (body moves to `txs`) or
    /// `on_tx_validation_failed` (body dropped).
    pub pending_validation: BTreeMap<TxId, Vec<u8>>,
}

impl MempoolState {
    pub fn new(capacity: usize) -> Self {
        Self {
            txs: VecDeque::new(),
            total_bytes: 0,
            capacity,
            peer_advertised: BTreeMap::new(),
            pending_validation: BTreeMap::new(),
        }
    }

    // -- Network event handlers --------------------------------------------

    /// A tx body arrived from the network.  If the mempool already
    /// holds it (or it's pending validation), emits `TxRejected` with
    /// `AlreadyKnown` and discards.  Otherwise records the body and
    /// emits `ValidateTx`; the wrapper validates and reports back via
    /// [`Self::on_tx_validated`] or [`Self::on_tx_validation_failed`].
    pub fn on_tx_received(&mut self, tx_id: TxId, body: Vec<u8>) -> Vec<MempoolEffect> {
        if self.pending_validation.contains_key(&tx_id) || self.contains(&tx_id) {
            return vec![MempoolEffect::TxRejected {
                tx_id,
                reason: TxRejectReason::AlreadyKnown,
            }];
        }
        self.pending_validation.insert(tx_id.clone(), body.clone());
        vec![MempoolEffect::ValidateTx { tx_id, body }]
    }

    // -- Validation outcomes -----------------------------------------------

    /// Validator confirmed the body for `tx_id` — admit it.  If the
    /// queue is at capacity, evicts the oldest tx and emits a
    /// `TxRejected { reason: QueueFull }` for it.  No-op if the
    /// tx_id wasn't pending validation.
    pub fn on_tx_validated(&mut self, tx_id: TxId, size: u32) -> Vec<MempoolEffect> {
        let Some(body) = self.pending_validation.remove(&tx_id) else {
            return Vec::new();
        };
        self.admit_internal(tx_id, body, size)
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
        self.txs.iter().map(|tx| tx.tx_id.clone()).collect()
    }

    /// True iff `tx_id` is in the mempool.
    pub fn contains(&self, tx_id: &TxId) -> bool {
        self.txs.iter().any(|tx| &tx.tx_id == tx_id)
    }

    /// Look up a tx body by its id.  Linear scan; mempool sizes this
    /// prototype targets keep it acceptable.
    pub fn get_body_by_id(&self, id: &[u8]) -> Option<Vec<u8>> {
        self.txs
            .iter()
            .find(|tx| tx.tx_id == id)
            .map(|tx| tx.body.clone())
    }

    /// Return up to `max_count` txs not yet advertised to `peer_id`,
    /// recording them so subsequent calls skip them.  The per-peer
    /// advertised set is pruned automatically when txs leave the
    /// mempool.
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
            if advertised.insert(tx.tx_id.clone()) {
                result.push(tx.clone());
            }
        }
        result
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

    // -- Internal helpers --------------------------------------------------

    fn admit_internal(
        &mut self,
        tx_id: TxId,
        body: Vec<u8>,
        size: u32,
    ) -> Vec<MempoolEffect> {
        let mut fx = Vec::new();
        if self.txs.len() >= self.capacity {
            if let Some(old) = self.txs.pop_front() {
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
}
