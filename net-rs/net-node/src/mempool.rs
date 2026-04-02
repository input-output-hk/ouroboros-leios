//! Transaction pool and fake transaction generation.
//!
//! Spawns a background task that generates random transactions on a Poisson
//! schedule and submits them via the coordinator.

use std::time::Duration;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tokio::sync::{mpsc, watch};
use tracing::info;

use net_core::multi_peer::types::NetworkCommand;
use net_core::protocols::txsubmission::{PendingTx, TxBody, TxId};

use crate::config::{DynamicConfig, TxConfig};

/// Spawn the transaction generator as a background task.
///
/// Returns a `JoinHandle` that runs until the `commands` channel is closed.
/// The generator reads `tx_rate` from the watch channel each iteration,
/// so rate changes take effect immediately.
pub fn spawn_tx_generator(
    config: &TxConfig,
    seed: Option<u64>,
    commands: mpsc::Sender<NetworkCommand>,
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

            info!(
                node_id = %node_id,
                tx_count,
                size,
                "generated transaction"
            );

            if commands
                .send(NetworkCommand::SubmitTransaction { tx })
                .await
                .is_err()
            {
                break; // coordinator shut down
            }
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
}
