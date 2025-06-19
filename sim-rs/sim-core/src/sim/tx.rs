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

struct NodeState {
    sink: mpsc::UnboundedSender<Arc<Transaction>>,
    tx_conflict_fraction: Option<f64>,
}

pub struct TransactionProducer {
    rng: ChaChaRng,
    clock: ClockBarrier,
    nodes: HashMap<NodeId, NodeState>,
    ib_shards: u64,
    config: Option<RealTransactionConfig>,
}

impl TransactionProducer {
    pub fn new(
        rng: ChaChaRng,
        clock: ClockBarrier,
        mut node_tx_sinks: HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>,
        config: &SimConfiguration,
    ) -> Self {
        let nodes = config
            .nodes
            .iter()
            .map(|node| {
                let sink = node_tx_sinks.remove(&node.id).unwrap();
                let state = NodeState {
                    sink,
                    tx_conflict_fraction: node.tx_conflict_fraction,
                };
                (node.id, state)
            })
            .collect();
        Self {
            rng,
            clock,
            nodes,
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
        let node_count = self.nodes.len();
        let mut next_tx_id = 0;
        let mut next_tx_at = Timestamp::zero();
        let mut next_input_id = 0;
        let mut rng = &mut self.rng;

        if let Some(start) = config.start_time {
            self.clock.wait_until(start).await;
            next_tx_at = start;
        };

        loop {
            let node_index = rng.random_range(0..node_count);
            let node_id = NodeId::new(node_index);
            let node = self.nodes.get(&node_id).unwrap();

            let conflict_fraction = node
                .tx_conflict_fraction
                .unwrap_or(config.conflict_fraction);

            let id = TransactionId::new(next_tx_id);
            let shard = rng.random_range(0..self.ib_shards);
            let bytes = (config.size_bytes.sample(&mut rng) as u64).min(config.max_size);
            let input_id = if next_input_id > 0 && rng.random_bool(conflict_fraction) {
                next_input_id - 1
            } else {
                let id = next_input_id;
                next_input_id += 1;
                id
            };
            let overcollateralization_factor =
                config.overcollateralization_factor.sample(&mut rng) as u64;

            let tx = Transaction {
                id,
                shard,
                bytes,
                input_id,
                overcollateralization_factor,
            };

            node.sink.send(Arc::new(tx))?;

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
