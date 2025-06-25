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
    tx_generation_weight: u64,
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
                let state =
                    NodeState {
                        sink,
                        tx_conflict_fraction: node.tx_conflict_fraction,
                        tx_generation_weight: node
                            .tx_generation_weight
                            .unwrap_or(if node.stake > 0 { 0 } else { 1 }),
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
        let mut next_tx_id = 0;
        let mut next_tx_at = Timestamp::zero();
        let mut next_input_id = 0;
        let mut rng = &mut self.rng;

        if let Some(start) = config.start_time {
            self.clock.wait_until(start).await;
            next_tx_at = start;
        };

        let node_weights = self.nodes.iter().filter_map(|(id, node)| {
            let weight = node.tx_generation_weight;
            (weight != 0).then_some((*id, weight))
        });
        let node_lookup = WeightedLookup::new(node_weights);

        loop {
            let node_id = node_lookup.sample(rng).unwrap();
            let node = self.nodes.get(node_id).unwrap();

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

struct WeightedLookup<T> {
    elements: Vec<(T, u64)>,
    total_weight: u64,
}

impl<T> WeightedLookup<T> {
    pub fn new(weights: impl IntoIterator<Item = (T, u64)>) -> Self {
        let elements: Vec<_> = weights
            .into_iter()
            .scan(0, |cum_weight, (element, weight)| {
                *cum_weight += weight;
                Some((element, *cum_weight))
            })
            .collect();
        let total_weight = elements
            .last()
            .map(|(_, weight)| *weight)
            .unwrap_or_default();
        Self {
            elements,
            total_weight,
        }
    }

    pub fn sample<R: Rng>(&self, rng: &mut R) -> Option<&T> {
        let choice = rng.random_range(0..self.total_weight);
        match self
            .elements
            .binary_search_by_key(&choice, |(_, weight)| *weight)
        {
            Ok(index) => self.elements.get(index).map(|(el, _)| el),
            Err(index) => self.elements.get(index).map(|(el, _)| el),
        }
    }
}
