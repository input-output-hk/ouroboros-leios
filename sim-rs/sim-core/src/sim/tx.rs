use anyhow::Result;
use rand::Rng;
use rand_distr::Distribution;
use std::{collections::HashMap, sync::Arc, time::Duration};
use tokio::sync::mpsc;

use crate::{
    clock::{ClockBarrier, Timestamp},
    config::{NodeConfiguration, NodeId, RealTransactionConfig, SimConfiguration, TransactionConfig},
    model::Transaction,
    rng::Rng as SimRng,
};

/// Core transaction generation logic shared between actor and sequential engines.
/// Uses usize indices to identify nodes; callers map these to their own node addressing.
pub(super) struct TxGeneratorCore {
    rng: SimRng,
    /// Monotonic counter. The i-th generated TX draws its random state
    /// deterministically from the context `("tx_generator", i)`, so the
    /// TX stream is a pure function of the master seed regardless of any
    /// per-node or network-timing behaviour elsewhere.
    next_tx_idx: u64,
    config: Option<RealTransactionConfig>,
    node_weights: WeightedLookup<usize>,
    tx_conflict_fractions: Vec<Option<f64>>,
    shard_count: usize,
}

impl TxGeneratorCore {
    /// Create a new TxGeneratorCore.
    /// `nodes` is an iterator of (index, node_config) for nodes in this shard.
    pub(super) fn new<'a>(
        rng: SimRng,
        config: &SimConfiguration,
        nodes: impl IntoIterator<Item = (usize, &'a NodeConfiguration)>,
    ) -> Self {
        let mut tx_conflict_fractions = Vec::new();
        let mut weights = Vec::new();

        for (idx, node) in nodes {
            // Ensure the vec is large enough
            if idx >= tx_conflict_fractions.len() {
                tx_conflict_fractions.resize(idx + 1, None);
            }
            tx_conflict_fractions[idx] = node.tx_conflict_fraction;

            let weight = node
                .tx_generation_weight
                .unwrap_or(if node.stake > 0 { 0 } else { 1 });
            if weight > 0 {
                weights.push((idx, weight));
            }
        }

        Self {
            rng,
            next_tx_idx: 0,
            config: match &config.transactions {
                TransactionConfig::Real(c) => Some(c.clone()),
                _ => None,
            },
            node_weights: WeightedLookup::new(weights),
            tx_conflict_fractions,
            shard_count: config.shard_count,
        }
    }

    /// Returns the timestamp of the first transaction event, if tx generation is configured.
    pub(super) fn first_event_time(&self) -> Option<Timestamp> {
        self.config.as_ref()?;
        if self.node_weights.total_weight == 0 {
            return None;
        }
        Some(
            self.config
                .as_ref()
                .unwrap()
                .start_time
                .unwrap_or(Timestamp::zero()),
        )
    }

    /// Generate one transaction and return the node index, transaction, and next generation time.
    /// Returns `None` if tx generation is not configured or no eligible nodes exist.
    pub(super) fn generate(
        &mut self,
        now: Timestamp,
    ) -> Option<(usize, Arc<Transaction>, Option<Timestamp>)> {
        let config = self.config.as_ref()?;
        if self.node_weights.total_weight == 0 {
            return None;
        }

        // Each generated TX gets its own seeded, one-shot ChaChaRng. The
        // seed is derived from ("tx_generator", tx_idx), so the full
        // sequence of generated TXs is a pure function of the master
        // seed. This holds across shards (they increment their own
        // tx_idx) and regardless of per-node network behaviour.
        let tx_idx = self.next_tx_idx;
        self.next_tx_idx += 1;
        let mut tx_rng = self.rng.seeded_chacha_from(&("tx_generator", tx_idx));

        let &idx = self.node_weights.sample(&mut tx_rng)?;
        let conflict_fraction = self
            .tx_conflict_fractions
            .get(idx)
            .copied()
            .flatten();

        let tx = config.new_tx(&mut tx_rng, conflict_fraction);

        let millis_until_tx =
            config.frequency_ms.sample(&mut tx_rng) as u64 * self.shard_count as u64;
        let next_at = now + Duration::from_millis(millis_until_tx);

        let next_time = if config.stop_time.is_some_and(|t| next_at > t) {
            None
        } else {
            Some(next_at)
        };

        Some((idx, Arc::new(tx), next_time))
    }
}

/// Async actor wrapper for tx generation (used by the actor engine).
pub struct TransactionProducer {
    core: TxGeneratorCore,
    clock: ClockBarrier,
    /// Node sinks indexed by the same usize indices as TxGeneratorCore.
    sinks: Vec<mpsc::UnboundedSender<Arc<Transaction>>>,
}

impl TransactionProducer {
    pub fn new(
        rng: SimRng,
        clock: ClockBarrier,
        mut node_tx_sinks: HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>,
        config: &SimConfiguration,
    ) -> Self {
        // Build indexed sinks and node config pairs, filtering to nodes with sinks
        let mut sinks = Vec::new();
        let mut indexed_nodes = Vec::new();
        for node in &config.nodes {
            if let Some(sink) = node_tx_sinks.remove(&node.id) {
                let idx = sinks.len();
                sinks.push(sink);
                indexed_nodes.push((idx, node));
            }
        }
        Self {
            core: TxGeneratorCore::new(rng, config, indexed_nodes),
            clock,
            sinks,
        }
    }

    pub async fn run(&mut self) -> Result<()> {
        let Some(start) = self.core.first_event_time() else {
            self.clock.wait_forever().await;
            return Ok(());
        };

        let mut next_tx_at = start;
        if next_tx_at > Timestamp::zero() {
            self.clock.wait_until(next_tx_at).await;
        }

        if self.sinks.is_empty() {
            tracing::warn!(
                "No nodes have tx_generation_weight > 0; \
                 skipping transaction generation. \
                 (Hint: topologies where all nodes have stake > 0 need \
                 explicit tx-generation-weight on at least one node.)"
            );
            self.clock.wait_forever().await;
            return Ok(());
        }

        loop {
            let Some((idx, tx, next_time)) = self.core.generate(next_tx_at) else {
                self.clock.wait_forever().await;
                return Ok(());
            };

            self.sinks[idx].send(tx)?;

            match next_time {
                Some(t) => {
                    next_tx_at = t;
                    self.clock.wait_until(next_tx_at).await;
                }
                None => {
                    self.clock.wait_forever().await;
                    return Ok(());
                }
            }
        }
    }
}

pub(super) struct WeightedLookup<T> {
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
        if self.total_weight == 0 {
            return None;
        }
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
