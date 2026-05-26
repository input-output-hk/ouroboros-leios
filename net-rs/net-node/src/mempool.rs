//! Transaction pool wrapper around `shared_consensus::mempool::MempoolState`.
//!
//! Translates between net-core's wire-format `PendingTx`/`TxId`/`TxBody`
//! and the opaque-bytes shape `shared-consensus` uses, plus the per-peer
//! `net_core::peer::PeerId` ↔ `shared_consensus::peer::PeerId` mapping.  The
//! actual queue, capacity, eviction, per-peer advertised set, and
//! validation-effect surface live in `shared_consensus::mempool`.
//!
//! `spawn_tx_generator` and `spawn_tx_validator` stay here — they are
//! the I/O-side actors that drive the state machine.

use std::collections::HashSet;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tokio::sync::{mpsc, watch};
use tracing::{info, warn};

use shared_consensus::mempool::{EbKey, MempoolState};
use net_core::peer::PeerId;
use net_core::protocols::txsubmission::{PendingTx, TxBody, TxId};

use crate::config::{DynamicConfig, TxConfig};

/// Shared handle to the mempool.
pub type SharedMempool = Arc<Mutex<Mempool>>;

/// Translate a net-core peer id to the shared-consensus one.  Both are
/// `pub struct PeerId(pub u64)`; this is a single field copy.
fn to_con_pid(id: PeerId) -> shared_consensus::peer::PeerId {
    shared_consensus::peer::PeerId(id.0)
}

fn from_con_tx(tx: shared_consensus::mempool::PendingTx) -> PendingTx {
    PendingTx {
        tx_id: TxId(tx.tx_id),
        body: TxBody(tx.body),
        size: tx.size,
    }
}

/// Pad/truncate a `Vec<u8>` tx-id into the wrapper's 32-byte hash form.
/// shared-consensus's `TxId = Vec<u8>` is hash-scheme-agnostic; net-rs's wire
/// format pins it at Blake2b-256.
fn to_hash_32(id: Vec<u8>) -> [u8; 32] {
    let mut h = [0u8; 32];
    let n = id.len().min(32);
    h[..n].copy_from_slice(&id[..n]);
    h
}

/// Which body the next self-produced RB carries — wire-typed sibling of
/// [`shared_consensus::production::BodyPath`].
///
/// `inline` becomes the RB body; `manifest_hashes` becomes a fresh EB
/// announcement attached to the same RB header.  Either may be empty
/// independently:
///
/// - both empty: empty body, no EB (safety gate; or cert + small mempool).
/// - `inline` non-empty, `manifest_hashes` empty: inline-only body, no EB.
/// - `inline` empty, `manifest_hashes` non-empty: empty body + EB (cert + overflow).
/// - both non-empty: inline body + EB residual (no cert + overflow).
///
/// `inline` is already drained from the mempool.  The manifest txs are
/// still in the free pool; the caller commits the EB-pin via
/// [`Mempool::produce_eb`] once it has the EB key.
#[derive(Debug, Clone, Default)]
pub struct BodyPath {
    pub inline: Vec<PendingTx>,
    pub manifest_hashes: Vec<[u8; 32]>,
}

/// I/O-side wrapper around `shared_consensus::mempool::MempoolState`.  Public
/// methods preserve the net-core wire types at the boundary; shared-consensus
/// Capacity of the admit-fanout channel.  Sized for short bursts of
/// admits without backpressuring `push`; on overflow `try_send` drops
/// the wake-up and the tx is picked up on the next `TxsRequested`
/// pull.
const ADMIT_FANOUT_CAPACITY: usize = 1024;

/// holds the actual state.
pub struct Mempool {
    state: MempoolState,
    /// Carries each just-admitted [`PendingTx`] to the main loop's
    /// fan-out branch, which announces it to every connected peer in
    /// O(log N) per peer via [`Self::mark_announced_to_peer`].
    /// `try_send`: overflow drops the wake-up; the tx remains in the
    /// mempool and reaches peers via the pull path on the next
    /// `MsgRequestTxIds`.
    admit_tx: mpsc::Sender<PendingTx>,
    /// Receiver half handed to the main loop exactly once.  The
    /// `Option` lets `take_admit_rx` move it out — the channel is
    /// single-consumer.
    admit_rx: Option<mpsc::Receiver<PendingTx>>,
}

impl Mempool {
    pub fn new(capacity: usize) -> Self {
        let (admit_tx, admit_rx) = mpsc::channel(ADMIT_FANOUT_CAPACITY);
        Self {
            state: MempoolState::new(capacity),
            admit_tx,
            admit_rx: Some(admit_rx),
        }
    }

    /// Take the admit-fanout receiver.  Returns `None` on subsequent
    /// calls — there is one consumer (the main loop).
    pub fn take_admit_rx(&mut self) -> Option<mpsc::Receiver<PendingTx>> {
        self.admit_rx.take()
    }

    /// Borrow the underlying shared-consensus state for read-only operations
    /// that consult the mempool but don't mutate it (e.g.
    /// `LeiosState::missing_eb_tx_bitmap`).
    pub fn as_inner(&self) -> &MempoolState {
        &self.state
    }

    /// Install a shared behaviour handle on the underlying mempool
    /// state.  The `Consensus` facade hands the same handle to every
    /// owned state machine.
    pub fn install_behaviour_handle(
        &mut self,
        handle: shared_consensus::behaviour::BehaviourHandle,
    ) {
        self.state.behaviour = handle;
    }

    /// Admit a tx that's already been validated (locally generated, or
    /// produced by `spawn_tx_validator` after its delay).  TxRejected
    /// effects (queue-full evictions, dedup) are dropped silently —
    /// telemetry plumbing for them is a follow-up.
    ///
    /// On successful admit, sends the tx through the admit-fanout
    /// channel so the main loop can announce it per-peer.  Duplicate
    /// admits do not signal — nothing new to fan out.
    pub fn push(&mut self, tx: PendingTx) {
        use shared_consensus::mempool::{MempoolEffect, TxRejectReason};
        let effects = self.state.admit_validated(
            tx.tx_id.0.clone(),
            tx.body.0.clone(),
            tx.size,
        );
        let admitted = !effects.iter().any(|e| matches!(
            e,
            MempoolEffect::TxRejected { reason: TxRejectReason::AlreadyKnown, .. }
        ));
        if admitted {
            if let Err(mpsc::error::TrySendError::Full(_)) = self.admit_tx.try_send(tx) {
                // Fanout channel full — peer will pick the tx up via
                // the next pull.  Warn so the operator notices if it
                // happens persistently.
                warn!("mempool admit fanout channel full; dropping notification");
            }
        }
    }

    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.state.len()
    }

    pub fn peek_unannounced_for_peer(
        &mut self,
        peer_id: PeerId,
        max_count: usize,
    ) -> Vec<PendingTx> {
        self.state
            .peek_unannounced_for_peer(to_con_pid(peer_id), max_count)
            .into_iter()
            .map(from_con_tx)
            .collect()
    }

    pub fn forget_peer(&mut self, peer_id: PeerId) {
        self.state.forget_peer(to_con_pid(peer_id));
    }


    pub fn get_body_by_id(&self, id: &[u8]) -> Option<Vec<u8>> {
        self.state.get_body_by_id(id)
    }

    /// Run the CIP-0164 overflow rule.  Returns the body path the next
    /// self-produced RB should take: `inline` holds drained tx bodies
    /// (empty when the safety gate fires or a cert ships in a small
    /// mempool); `manifest_hashes` holds the residual overflow
    /// (empty when the mempool fit in the RB body cap).
    ///
    /// `endorsement_present` must reflect whether the caller is about
    /// to attach a Leios certificate to this RB; the body-path
    /// decision enforces the CIP-0164 cert-XOR-inline-body rule.
    ///
    /// Policy lives in [`shared_consensus::production::BodyPath::decide`].
    pub fn decide_body_path(
        &mut self,
        rb_body_max_bytes: usize,
        eb_body_max_bytes: usize,
        leios: &shared_consensus::leios::LeiosState,
        endorsement_present: bool,
    ) -> BodyPath {
        let con = shared_consensus::production::BodyPath::decide(
            &mut self.state,
            rb_body_max_bytes,
            eb_body_max_bytes,
            leios,
            endorsement_present,
        );
        BodyPath {
            inline: con.inline.into_iter().map(from_con_tx).collect(),
            manifest_hashes: con.manifest.into_iter().map(to_hash_32).collect(),
        }
    }

    /// Drain the first `count` free txs into an EB pin under `eb_key`.
    /// `count` must come from `BodyPath::manifest_hashes.len()` so the
    /// drain matches the size-capped selection.  After this the
    /// drained txs stay locally available via `has_tx` /
    /// `get_body_by_id` but no longer count toward `total_bytes` /
    /// `drain_up_to` — i.e. they won't be double-included in a
    /// subsequent RB body.
    ///
    /// `MempoolEffect::TxRejected{EbClosurePruned}` evictions of older
    /// closures aging past the retention window are dropped on the
    /// floor here; net-rs has no telemetry plumbing for them yet, and
    /// sim-rs's adapter will surface them directly.
    pub fn produce_eb(&mut self, eb_key: EbKey, count: usize) {
        let _ = self.state.produce_eb(eb_key, count);
    }

    /// Receiver-side: insert a body fetched via LeiosFetch.  Idempotent
    /// against duplicates already in either compartment.  Hashes the
    /// body to derive the tx_id (the wire-format manifest reference).
    ///
    /// EB-pinned bodies live in `eb_pinned`, not the free pool that
    /// `peek_unannounced_for_peer` iterates, so no admit-fanout
    /// notification fires here — peers fetch these via LeiosFetch
    /// BlockTxs, not TxSubmission.
    pub fn merge_eb_body(&mut self, body: Vec<u8>) {
        let tx = tx_from_received_bytes(body);
        self.state.merge_eb_body(tx.tx_id.0, tx.body.0, tx.size);
    }

    /// Mark a tx as advertised to the given peer; returns `true` iff
    /// the entry was newly inserted (caller should send the body).
    /// The admit-fanout path uses this to announce a single tx in
    /// O(log N) per peer instead of rescanning the mempool.
    pub fn mark_announced_to_peer(&mut self, peer_id: PeerId, tx_id: &TxId) -> bool {
        self.state
            .mark_announced_to_peer(to_con_pid(peer_id), &tx_id.0)
    }

    /// Snapshot of every locally available tx id — free pool plus
    /// EB-pinned bodies.  Used by the CIP-0164 `MissingTX` voting
    /// predicate.
    pub fn all_known_tx_ids(&self) -> HashSet<Vec<u8>> {
        let mut ids: HashSet<Vec<u8>> = self.state.txs.iter().map(|t| t.tx_id.clone()).collect();
        ids.extend(self.state.eb_pinned.keys().cloned());
        ids
    }
}

/// Create a new shared mempool.
pub fn new_mempool(capacity: usize) -> SharedMempool {
    Arc::new(Mutex::new(Mempool::new(capacity)))
}

/// Mempool-backed `TxBodyResolver`.  Wraps `SharedMempool` and exposes
/// the body-by-hash lookup that the Leios store uses when receivers
/// re-serve EB tx requests.
pub struct MempoolTxBodyResolver(SharedMempool);

impl MempoolTxBodyResolver {
    pub fn new(mempool: SharedMempool) -> Self {
        Self(mempool)
    }
}

impl net_core::store::leios_store::TxBodyResolver for MempoolTxBodyResolver {
    fn resolve_body(&self, tx_id: &[u8]) -> Option<Vec<u8>> {
        self.0.lock().unwrap().get_body_by_id(tx_id)
    }
}

/// Build a `PendingTx` from raw bytes received from a peer.
/// The tx_id is derived by hashing the body with Blake2b-256.
pub fn tx_from_received_bytes(body: Vec<u8>) -> PendingTx {
    let hash = blake2b_simd::Params::new().hash_length(32).hash(&body);
    let size = body.len() as u32;
    PendingTx {
        tx_id: TxId(hash.as_bytes().to_vec()),
        body: TxBody(body),
        size,
    }
}

/// Spawn the transaction generator as a background task.
///
/// The generator reads `tx_rate` from the watch channel each iteration,
/// so rate changes take effect immediately. Each generated tx is pushed
/// into the local mempool for block inclusion and peer advertisement
/// via the TxSubmission pull model.
pub fn spawn_tx_generator(
    config: &TxConfig,
    seed: Option<u64>,
    mempool: SharedMempool,
    node_id: String,
    mut dyn_config: watch::Receiver<DynamicConfig>,
) -> tokio::task::JoinHandle<()> {
    let min_size = config.tx_size_min;
    let max_size = config.tx_size_max;

    tokio::spawn(async move {
        let mut rng = match seed {
            Some(s) => StdRng::seed_from_u64(s.wrapping_add(0xBEEF)),
            None => StdRng::from_entropy(),
        };
        let mut tx_count: u64 = 0;

        loop {
            let rate = dyn_config.borrow().tx_rate;
            if rate <= 0.0 {
                if dyn_config.changed().await.is_err() {
                    break;
                }
                continue;
            }

            let interval = exp_sample(&mut rng, rate);
            tokio::time::sleep(interval).await;

            let size = if min_size >= max_size {
                min_size
            } else {
                rng.gen_range(min_size..=max_size)
            };

            let tx = make_fake_tx(&mut rng, size);
            tx_count += 1;

            {
                let mut pool = mempool.lock().unwrap();
                pool.push(tx);
            }

            info!(
                node_id = %node_id,
                tx_count,
                size,
                "generated transaction"
            );
        }
    })
}

/// Spawn the transaction validator as a background task.
///
/// Received transactions go through a simulated validation delay before
/// entering the mempool.  Each tx is validated concurrently (Phase 1
/// validation is independent per tx).  Concurrency is gated by a
/// semaphore.
pub fn spawn_tx_validator(
    tx_validation_ms: f64,
    tx_validation_ms_per_byte: f64,
    mempool: SharedMempool,
    mut rx: mpsc::Receiver<Vec<u8>>,
) -> tokio::task::JoinHandle<()> {
    let sem = Arc::new(tokio::sync::Semaphore::new(256));
    tokio::spawn(async move {
        while let Some(body) = rx.recv().await {
            let permit = sem.clone().acquire_owned().await.unwrap();
            let mempool = mempool.clone();
            let ms = tx_validation_ms + tx_validation_ms_per_byte * body.len() as f64;
            tokio::spawn(async move {
                let _permit = permit;
                if ms > 0.0 {
                    tokio::time::sleep(Duration::from_secs_f64(ms / 1000.0)).await;
                }
                let tx = tx_from_received_bytes(body);
                let mut pool = mempool.lock().unwrap();
                pool.push(tx);
            });
        }
    })
}

/// Build a fake transaction.  The `tx_id` is `blake2b256(body)` so it
/// matches what `tx_from_received_bytes` would compute on a peer; the
/// EB manifest carries this hash, and receivers hash bodies the same
/// way to match them back to manifest indices.
fn make_fake_tx(rng: &mut StdRng, size: usize) -> PendingTx {
    let mut body_buf = vec![0u8; size];
    rng.fill(&mut body_buf[..]);
    tx_from_received_bytes(body_buf)
}

/// Sample an exponential inter-arrival time: `-ln(U) / lambda`.
fn exp_sample(rng: &mut StdRng, rate: f64) -> Duration {
    let u: f64 = rng.gen_range(0.001..1.0);
    Duration::from_secs_f64(-u.ln() / rate)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_tx_with_id(id: u8, size: usize) -> PendingTx {
        PendingTx {
            tx_id: TxId(vec![id; 32]),
            body: TxBody(vec![0; size]),
            size: size as u32,
        }
    }

    #[test]
    fn make_fake_tx_id_equals_body_hash() {
        // Locally-produced txs must hash identically to peer-received ones
        // so that EB manifest matching works on the receiver side.
        let mut rng = StdRng::seed_from_u64(7);
        let tx = make_fake_tx(&mut rng, 256);
        let recomputed = tx_from_received_bytes(tx.body.0.clone());
        assert_eq!(tx.tx_id, recomputed.tx_id);
    }

    #[test]
    fn make_fake_tx_correct_size() {
        let mut rng = StdRng::seed_from_u64(42);
        let tx = make_fake_tx(&mut rng, 500);
        assert_eq!(tx.body.0.len(), 500);
        assert_eq!(tx.size, 500);
        assert_eq!(tx.tx_id.0.len(), 32);
    }

    #[test]
    fn tx_from_received_bytes_deterministic() {
        let body = vec![0xAA; 100];
        let tx1 = tx_from_received_bytes(body.clone());
        let tx2 = tx_from_received_bytes(body);
        assert_eq!(tx1.tx_id.0, tx2.tx_id.0);
        assert_eq!(tx1.size, 100);
    }

    #[test]
    fn tx_from_received_bytes_different_inputs() {
        let tx1 = tx_from_received_bytes(vec![0xAA; 100]);
        let tx2 = tx_from_received_bytes(vec![0xBB; 100]);
        assert_ne!(tx1.tx_id.0, tx2.tx_id.0);
    }

    #[test]
    fn exp_sample_positive() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let d = exp_sample(&mut rng, 1.0);
            assert!(d.as_secs_f64() > 0.0);
        }
    }

    #[test]
    fn exp_sample_mean_roughly_correct() {
        let mut rng = StdRng::seed_from_u64(42);
        let rate = 2.0;
        let n = 10_000;
        let total: f64 = (0..n)
            .map(|_| exp_sample(&mut rng, rate).as_secs_f64())
            .sum();
        let mean = total / n as f64;
        assert!((0.4..=0.6).contains(&mean), "mean={mean}, expected ~0.5");
    }

    // -- Wrapper translation tests (algorithmic behaviour lives in shared-consensus) --

    #[tokio::test]
    async fn mempool_resolver_serves_body_through_trait() {
        use net_core::store::leios_store::TxBodyResolver;
        let pool = new_mempool(100);
        {
            let mut p = pool.lock().unwrap();
            p.push(PendingTx {
                tx_id: TxId(vec![0xCC; 32]),
                body: TxBody(vec![0xDE, 0xAD]),
                size: 2,
            });
        }
        let resolver = MempoolTxBodyResolver::new(pool);
        assert_eq!(resolver.resolve_body(&[0xCC; 32]), Some(vec![0xDE, 0xAD]));
        assert_eq!(resolver.resolve_body(&[0x99; 32]), None);
    }

    #[tokio::test]
    async fn validator_pushes_received_body_into_mempool_with_hash_id() {
        let pool = new_mempool(100);
        let (tx, rx) = mpsc::channel::<Vec<u8>>(8);
        let _h = spawn_tx_validator(0.0, 0.0, pool.clone(), rx);

        let body = vec![0xDE, 0xAD, 0xBE, 0xEF];
        tx.send(body.clone()).await.unwrap();

        for _ in 0..50 {
            tokio::time::sleep(Duration::from_millis(5)).await;
            if pool.lock().unwrap().len() == 1 {
                break;
            }
        }
        let pool_locked = pool.lock().unwrap();
        assert_eq!(pool_locked.len(), 1);
        let expected = tx_from_received_bytes(body);
        assert_eq!(
            pool_locked.get_body_by_id(&expected.tx_id.0),
            Some(expected.body.0)
        );
    }

    #[test]
    fn peek_unannounced_translates_peer_ids() {
        // Net-core's PeerId(u64) maps to shared-consensus's PeerId(u64); verify
        // the wrapper preserves per-peer dedup across the boundary.
        let mut pool = Mempool::new(10);
        pool.push(make_tx_with_id(1, 100));
        pool.push(make_tx_with_id(2, 100));
        let peer = PeerId(0);
        assert_eq!(pool.peek_unannounced_for_peer(peer, 10).len(), 2);
        assert!(pool.peek_unannounced_for_peer(peer, 10).is_empty());
    }
}
