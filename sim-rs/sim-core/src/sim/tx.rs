use anyhow::Result;
use rand::Rng;
use rand_chacha::ChaChaRng;
use rand_distr::Distribution;
use std::{collections::HashMap, sync::Arc, time::Duration};
use tokio::sync::mpsc;

use crate::{
    clock::{ClockBarrier, Timestamp},
    config::{NodeId, RealTransactionConfig, SimConfiguration, TransactionConfig},
    model::{Transaction, TransactionId},
};

pub struct TransactionProducer {
    rng: ChaChaRng,
    clock: ClockBarrier,
    node_tx_sinks: HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>,
    ib_shards: u64,
    config: Option<RealTransactionConfig>,
}

impl TransactionProducer {
    pub fn new(
        rng: ChaChaRng,
        clock: ClockBarrier,
        node_tx_sinks: HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>,
        config: &SimConfiguration,
    ) -> Self {
        Self {
            rng,
            clock,
            node_tx_sinks,
            ib_shards: config.ib_shards,
            config: match &config.transactions {
                TransactionConfig::Real(config) => Some(config.clone()),
                _ => None,
            },
        }
    }

    pub async fn run(&mut self) -> Result<()> {
        let Some(config) = self.config.take() else {
            self.clock.wait_forever().await;
            return Ok(());
        };
        let node_count = self.node_tx_sinks.len();
        let mut next_tx_id = 0;
        let mut next_tx_at = Timestamp::zero();
        let mut rng = &mut self.rng;

        if let Some(start) = config.start_time {
            self.clock.wait_until(start).await;
            next_tx_at = start;
        };

        loop {
            let id = TransactionId::new(next_tx_id);
            let shard = rng
                .random_bool(config.sharded_percentage)
                .then(|| rng.random_range(0..self.ib_shards));
            let bytes = (config.size_bytes.sample(&mut rng) as u64).min(config.max_size);
            let tx = Transaction { id, shard, bytes };

            let node_index = rng.random_range(0..node_count);
            let node_id = NodeId::new(node_index);

            self.node_tx_sinks
                .get(&node_id)
                .unwrap()
                .send(Arc::new(tx))?;

            next_tx_id += 1;
            let millis_until_tx = config.frequency_ms.sample(&mut rng) as u64;
            next_tx_at += Duration::from_millis(millis_until_tx);

            if config.stop_time.is_some_and(|t| next_tx_at > t) {
                self.clock.wait_forever().await;
                return Ok(());
            } else {
                self.clock.wait_until(next_tx_at).await;
            }
        }
    }
}
