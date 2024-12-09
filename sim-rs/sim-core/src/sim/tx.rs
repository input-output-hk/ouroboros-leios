use anyhow::Result;
use rand::Rng;
use rand_chacha::ChaChaRng;
use rand_distr::Distribution;
use std::{collections::HashMap, sync::Arc, time::Duration};
use tokio::sync::mpsc;

use crate::{
    clock::{Clock, Timestamp},
    config::{NodeId, SimConfiguration},
    model::{Transaction, TransactionId},
    probability::FloatDistribution,
};

pub struct TransactionProducer {
    rng: ChaChaRng,
    clock: Clock,
    node_tx_sinks: HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>,
    ib_shards: u64,
    frequency_ms: FloatDistribution,
    size_bytes: FloatDistribution,
}

impl TransactionProducer {
    pub fn new(
        rng: ChaChaRng,
        clock: Clock,
        node_tx_sinks: HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>,
        config: &SimConfiguration,
    ) -> Self {
        Self {
            rng,
            clock,
            node_tx_sinks,
            ib_shards: config.ib_shards,
            frequency_ms: config.transaction_frequency_ms,
            size_bytes: config.transaction_size_bytes,
        }
    }

    pub async fn run(&mut self) -> Result<()> {
        let node_count = self.node_tx_sinks.len();
        let mut next_tx_id = 0;
        let mut next_tx_at = Timestamp::zero();
        let mut rng = &mut self.rng;
        loop {
            let id = TransactionId::new(next_tx_id);
            let shard = rng.gen_range(0..self.ib_shards);
            let bytes = self.size_bytes.sample(&mut rng) as u64;
            let tx = Transaction { id, shard, bytes };

            let node_index = rng.gen_range(0..node_count);
            let node_id = NodeId::new(node_index);

            self.node_tx_sinks
                .get(&node_id)
                .unwrap()
                .send(Arc::new(tx))?;

            next_tx_id += 1;
            let millis_until_tx = self.frequency_ms.sample(&mut rng) as u64;
            next_tx_at = next_tx_at + Duration::from_millis(millis_until_tx);

            self.clock.wait_until(next_tx_at).await;
        }
    }
}
