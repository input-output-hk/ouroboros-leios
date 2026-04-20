use anyhow::Result;
use rand::Rng;
use rand_distr::Distribution;
use std::{collections::HashMap, sync::Arc, time::Duration};
use tokio::sync::mpsc;

use crate::{
    clock::{ClockBarrier, Timestamp},
    config::{NodeConfiguration, NodeId, RealTransactionConfig, SimConfiguration, TransactionConfig},
    model::{Transaction, TransactionId},
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
    /// Per-shard TX ID counter.  Derived from (shard_index, tx_idx) to
    /// avoid sharing an atomic across shard threads, which would make
    /// ID assignment depend on OS thread scheduling.
    next_tx_id: u64,
    /// Per-shard input_id counter for conflict tracking.
    next_input_id: u64,
    /// Most recently assigned input_id (for conflict generation).
    last_input_id: u64,
    config: Option<RealTransactionConfig>,
    node_weights: WeightedLookup<usize>,
    tx_conflict_fractions: Vec<Option<f64>>,
    shard_count: usize,
}

impl TxGeneratorCore {
    /// Create a new TxGeneratorCore.
    /// `nodes` is an iterator of (index, node_config) for nodes in this shard.
    /// `shard_index` is used to offset TX IDs so that different shards
    /// produce non-overlapping ID ranges without shared atomics.
    pub(super) fn new<'a>(
        rng: SimRng,
        config: &SimConfiguration,
        shard_index: usize,
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

        // Offset per-shard counters so TX IDs don't collide across shards.
        // 1B IDs per shard is far more than any run will generate.
        let shard_offset = shard_index as u64 * 1_000_000_000;
        Self {
            rng,
            next_tx_idx: 0,
            next_tx_id: shard_offset,
            next_input_id: shard_offset + 1,
            last_input_id: shard_offset,
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
        if self.config.is_none() || self.node_weights.total_weight == 0 {
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

        let tx = {
            let config = self.config.as_ref().unwrap();
            let id = TransactionId::new(self.next_tx_id);
            self.next_tx_id += 1;
            let shard = tx_rng.random_range(0..config.ib_shards);
            let bytes = (config.size_bytes.sample(&mut tx_rng) as u64).min(config.max_size);
            let input_id =
                if tx_rng.random_bool(conflict_fraction.unwrap_or(config.conflict_fraction)) {
                    self.last_input_id
                } else {
                    let id = self.next_input_id;
                    self.next_input_id += 1;
                    self.last_input_id = id;
                    id
                };
            let overcollateralization_factor =
                config.overcollateralization_factor.sample(&mut tx_rng) as u64;
            Transaction {
                id,
                shard,
                bytes,
                input_id,
                overcollateralization_factor,
            }
        };

        // Preserve sub-millisecond precision from the frequency
        // distribution: previously this truncated `f64 as u64`, so a
        // configured 7.5 ms became 7 ms — ~7% faster generation than
        // intended. `Duration::from_secs_f64` converts to a full
        // nanosecond-resolution Duration. `.max(0.0)` matches the old
        // saturating behaviour for non-positive samples from e.g. a
        // Normal distribution (from_secs_f64 panics on negatives).
        let config = self.config.as_ref().unwrap();
        let secs_until_tx = (config.frequency_ms.sample(&mut tx_rng) / 1000.0
            * self.shard_count as f64)
            .max(0.0);
        let next_at = now + Duration::from_secs_f64(secs_until_tx);

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
            core: TxGeneratorCore::new(rng, config, 0, indexed_nodes),
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
