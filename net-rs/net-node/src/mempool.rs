//! Transaction pool and fake transaction generation.
//!
//! `Mempool` accumulates transactions from both local generation and received
//! from peers. The block producer drains it when producing ranking blocks
//! (txs fit in RB body) or endorser blocks (overflow → EB manifest).
//!
//! `spawn_tx_generator` runs a background Poisson process that pushes fake
//! transactions into the mempool and broadcasts them via the coordinator.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tokio::sync::{mpsc, watch};
use tracing::info;

use net_core::protocols::txsubmission::{PendingTx, TxBody, TxId};

use crate::config::{DynamicConfig, TxConfig};

/// Shared handle to the mempool.
pub type SharedMempool = Arc<Mutex<Mempool>>;

/// Transaction accumulator for block production.
///
/// Collects pending transactions from local generation and peer receipt.
/// The block producer drains it on each RB production attempt.
pub struct Mempool {
    txs: VecDeque<PendingTx>,
    total_bytes: usize,
    capacity: usize,
}

impl Mempool {
    /// Create an empty mempool with the given max transaction count.
    pub fn new(capacity: usize) -> Self {
        Self {
            txs: VecDeque::new(),
            total_bytes: 0,
            capacity,
        }
    }

    /// Add a transaction. Drops the oldest tx if at capacity.
    pub fn push(&mut self, tx: PendingTx) {
        if self.txs.len() >= self.capacity {
            if let Some(old) = self.txs.pop_front() {
                self.total_bytes -= old.size as usize;
            }
        }
        self.total_bytes += tx.size as usize;
        self.txs.push_back(tx);
    }

    /// Total bytes of pending transactions.
    pub fn total_bytes(&self) -> usize {
        self.total_bytes
    }

    /// Number of pending transactions.
    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.txs.len()
    }

    /// Drain all transactions (for EB overflow path).
    pub fn drain_all(&mut self) -> Vec<PendingTx> {
        self.total_bytes = 0;
        self.txs.drain(..).collect()
    }

    /// Peek at up to `max_count` transactions without removing them.
    /// Used by TxSubmission pull model — txs stay available for other
    /// peers and block production.
    pub fn peek_up_to(&self, max_count: usize) -> Vec<PendingTx> {
        self.txs.iter().take(max_count).cloned().collect()
    }

    /// Snapshot of all current `tx_id` byte vectors. Used by the Leios
    /// receiver to decide which EB transactions need to be fetched.
    pub fn current_tx_ids(&self) -> std::collections::HashSet<Vec<u8>> {
        self.txs.iter().map(|tx| tx.tx_id.0.clone()).collect()
    }

    /// Drain transactions up to a byte limit (for RB body path).
    pub fn drain_up_to(&mut self, max_bytes: usize) -> Vec<PendingTx> {
        let mut result = Vec::new();
        let mut bytes = 0;
        while let Some(front) = self.txs.front() {
            if bytes + front.size as usize > max_bytes && !result.is_empty() {
                break;
            }
            let tx = self.txs.pop_front().unwrap();
            bytes += tx.size as usize;
            self.total_bytes -= tx.size as usize;
            result.push(tx);
            if bytes >= max_bytes {
                break;
            }
        }
        result
    }
}

/// Create a new shared mempool.
pub fn new_mempool(capacity: usize) -> SharedMempool {
    Arc::new(Mutex::new(Mempool::new(capacity)))
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
/// into the local mempool for block inclusion and peer advertisement via
/// the TxSubmission pull model.
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
                // Wait for a config update that might set a positive rate.
                if dyn_config.changed().await.is_err() {
                    break; // sender dropped
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

            // Push into local mempool for block inclusion.
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
/// entering the mempool. Each tx is validated concurrently (Phase 1
/// validation is independent per tx). Concurrency is gated by a semaphore.
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
                    tokio::time::sleep(std::time::Duration::from_secs_f64(ms / 1000.0)).await;
                }
                let tx = tx_from_received_bytes(body);
                let mut pool = mempool.lock().unwrap();
                pool.push(tx);
            });
        }
    })
}

/// Build a fake transaction with random id and body.
fn make_fake_tx(rng: &mut StdRng, size: usize) -> PendingTx {
    let mut id_buf = vec![0u8; 32];
    rng.fill(&mut id_buf[..]);

    let mut body_buf = vec![0u8; size];
    rng.fill(&mut body_buf[..]);

    PendingTx {
        tx_id: TxId(id_buf),
        body: TxBody(body_buf),
        size: size as u32,
    }
}

/// Sample an exponential inter-arrival time: -ln(U) / lambda.
fn exp_sample(rng: &mut StdRng, rate: f64) -> Duration {
    let u: f64 = rng.gen_range(0.001..1.0);
    Duration::from_secs_f64(-u.ln() / rate)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_tx(size: usize) -> PendingTx {
        let mut rng = StdRng::seed_from_u64(42);
        make_fake_tx(&mut rng, size)
    }

    fn make_tx_with_id(id: u8, size: usize) -> PendingTx {
        PendingTx {
            tx_id: TxId(vec![id; 32]),
            body: TxBody(vec![0; size]),
            size: size as u32,
        }
    }

    // -- Mempool tests --

    #[test]
    fn mempool_push_and_len() {
        let mut pool = Mempool::new(100);
        assert_eq!(pool.len(), 0);
        assert_eq!(pool.total_bytes(), 0);

        pool.push(make_tx_with_id(1, 500));
        assert_eq!(pool.len(), 1);
        assert_eq!(pool.total_bytes(), 500);

        pool.push(make_tx_with_id(2, 300));
        assert_eq!(pool.len(), 2);
        assert_eq!(pool.total_bytes(), 800);
    }

    #[test]
    fn capacity_drops_oldest() {
        let mut pool = Mempool::new(3);
        pool.push(make_tx_with_id(1, 100));
        pool.push(make_tx_with_id(2, 200));
        pool.push(make_tx_with_id(3, 300));
        assert_eq!(pool.len(), 3);
        assert_eq!(pool.total_bytes(), 600);

        // Push a 4th — oldest (100 bytes) should be dropped.
        pool.push(make_tx_with_id(4, 400));
        assert_eq!(pool.len(), 3);
        assert_eq!(pool.total_bytes(), 900); // 200 + 300 + 400
    }

    #[test]
    fn current_tx_ids_returns_pushed_ids() {
        let mut pool = Mempool::new(100);
        pool.push(make_tx_with_id(1, 50));
        pool.push(make_tx_with_id(2, 50));
        let ids = pool.current_tx_ids();
        assert_eq!(ids.len(), 2);
        assert!(ids.contains(&vec![1u8; 32]));
        assert!(ids.contains(&vec![2u8; 32]));
    }

    #[test]
    fn drain_all_empties_pool() {
        let mut pool = Mempool::new(100);
        pool.push(make_tx_with_id(1, 100));
        pool.push(make_tx_with_id(2, 200));

        let drained = pool.drain_all();
        assert_eq!(drained.len(), 2);
        assert_eq!(pool.len(), 0);
        assert_eq!(pool.total_bytes(), 0);
    }

    #[test]
    fn drain_up_to_respects_limit() {
        let mut pool = Mempool::new(100);
        pool.push(make_tx_with_id(1, 100));
        pool.push(make_tx_with_id(2, 200));
        pool.push(make_tx_with_id(3, 300));

        // Drain up to 250 bytes — gets tx 1 (100), then tx 2 (200) would
        // push to 300 > 250, so stops after tx 1 only.
        let drained = pool.drain_up_to(250);
        assert_eq!(drained.len(), 1);
        assert_eq!(pool.len(), 2);
        assert_eq!(pool.total_bytes(), 500);
    }

    #[test]
    fn drain_up_to_takes_all_if_under_limit() {
        let mut pool = Mempool::new(100);
        pool.push(make_tx_with_id(1, 100));
        pool.push(make_tx_with_id(2, 200));

        let drained = pool.drain_up_to(1000);
        assert_eq!(drained.len(), 2);
        assert_eq!(pool.len(), 0);
        assert_eq!(pool.total_bytes(), 0);
    }

    #[test]
    fn drain_up_to_empty_pool() {
        let mut pool = Mempool::new(100);
        let drained = pool.drain_up_to(1000);
        assert!(drained.is_empty());
    }

    #[test]
    fn total_bytes_tracks_correctly() {
        let mut pool = Mempool::new(100);
        pool.push(make_tx_with_id(1, 100));
        pool.push(make_tx_with_id(2, 200));
        assert_eq!(pool.total_bytes(), 300);

        pool.drain_up_to(150);
        assert_eq!(pool.total_bytes(), 200);

        pool.drain_all();
        assert_eq!(pool.total_bytes(), 0);
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

    // -- Existing generator tests --

    #[test]
    fn make_fake_tx_correct_size() {
        let mut rng = StdRng::seed_from_u64(42);
        let tx = make_fake_tx(&mut rng, 500);
        assert_eq!(tx.body.0.len(), 500);
        assert_eq!(tx.size, 500);
        assert_eq!(tx.tx_id.0.len(), 32);
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
        // Expected mean = 1/rate = 0.5. Allow ±20%.
        assert!((0.4..=0.6).contains(&mean), "mean={mean}, expected ~0.5");
    }

    // -- peek_up_to tests --

    #[test]
    fn peek_up_to_doesnt_remove() {
        let mut pool = Mempool::new(100);
        pool.push(make_tx_with_id(1, 100));
        pool.push(make_tx_with_id(2, 200));
        pool.push(make_tx_with_id(3, 300));

        let peeked = pool.peek_up_to(2);
        assert_eq!(peeked.len(), 2);
        assert_eq!(pool.len(), 3);
    }

    #[test]
    fn peek_up_to_clamps_to_available() {
        let mut pool = Mempool::new(100);
        pool.push(make_tx_with_id(1, 100));
        pool.push(make_tx_with_id(2, 200));

        let peeked = pool.peek_up_to(10);
        assert_eq!(peeked.len(), 2);
    }
}
