use std::{collections::HashMap, sync::Arc, time::Duration};

use anyhow::Result;
use rand::RngCore;
use rand_chacha::{ChaChaRng, rand_core::SeedableRng};
use tokio::{select, sync::mpsc};
use tokio_util::sync::CancellationToken;

use crate::{
    clock::{Clock, ClockCoordinator, PeerShard},
    config::{NodeId, SimConfiguration},
    model::Transaction,
    network::{Network, ShardLookup},
    sim::tx::TransactionProducer,
};

/// A shard is an independent Logical Process in the CMB model.
pub(crate) struct Shard {
    pub clock_coordinator: ClockCoordinator,
    pub network: Box<dyn NetworkRunnable>,
    pub tx_producer: TransactionProducer,
}

impl Shard {
    /// Run this shard until the token is cancelled.
    pub async fn run(mut self, token: CancellationToken) -> Result<()> {
        select! {
            _ = token.cancelled() => {}
            _ = self.clock_coordinator.run() => {}
            result = self.network.run() => { result? }
            result = self.tx_producer.run() => { result?; }
        }
        Ok(())
    }
}

/// Trait for type-erased network running. Implemented by Network<P, M>.
pub(crate) trait NetworkRunnable: Send {
    fn run(&mut self) -> futures::future::BoxFuture<'_, Result<()>>;
}

use std::fmt::Debug;
use std::hash::Hash;

impl<TProtocol: Clone + Eq + Hash + Send + 'static, TMessage: Debug + Send + 'static> NetworkRunnable
    for Network<TProtocol, TMessage>
{
    fn run(&mut self) -> futures::future::BoxFuture<'_, Result<()>> {
        Box::pin(Network::run(self))
    }
}

/// Build shards from pre-created clock coordinators and config.
/// Creates networks, wires edges (intra + cross-shard), sets up CMB peer
/// lookahead, creates TX producers, and assembles Shard structs.
///
/// `wrap_networks` converts typed `Network<P, M>` into boxed trait objects.
pub(crate) fn build_shards<TProtocol, TMessage>(
    config: &Arc<SimConfiguration>,
    clocks: &[Clock],
    clock_coordinators: &mut Vec<ClockCoordinator>,
    shard_lookup: &ShardLookup,
    per_shard_tx_sinks: Vec<HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>>,
    mut networks: Vec<Network<TProtocol, TMessage>>,
) -> Vec<Shard>
where
    TProtocol: Clone + Eq + Hash + Send + Debug + 'static,
    TMessage: Debug + Send + 'static,
{
    let shard_count = clocks.len();
    let mut rng = ChaChaRng::seed_from_u64(config.seed.wrapping_add(1));

    // Set up direct NC-to-NC cross-shard routing
    if shard_count > 1 {
        let mut delivery_sinks = Vec::new();
        for network in &mut networks {
            let (tx, rx) = mpsc::unbounded_channel();
            delivery_sinks.push(tx);
            network.set_cross_shard_delivery(rx);
        }
        for network in &mut networks {
            network.set_cross_shard_routing(delivery_sinks.clone(), shard_lookup.clone());
        }
    }

    // Add edges to per-shard networks
    for link_config in config.links.iter() {
        let from = link_config.nodes.0;
        let to = link_config.nodes.1;
        let from_shard = shard_lookup[&from];
        let to_shard = shard_lookup[&to];

        if from_shard == to_shard {
            // Intra-shard: both directions
            networks[from_shard]
                .set_edge_policy(from, to, link_config.latency, link_config.bandwidth_bps)
                .expect("failed to set edge policy");
        } else {
            // Cross-shard: incoming connections on each target shard's NC
            networks[to_shard].add_incoming_edge(
                from, to, link_config.latency, link_config.bandwidth_bps,
            );
            networks[from_shard].add_incoming_edge(
                to, from, link_config.latency, link_config.bandwidth_bps,
            );
        }
    }

    // Log cross-shard edge statistics
    if shard_count > 1 {
        let cross_shard_edges = config.links.iter()
            .filter(|l| shard_lookup[&l.nodes.0] != shard_lookup[&l.nodes.1])
            .count();
        let total_edges = config.links.len();
        tracing::info!(
            cross_shard_edges,
            total_edges,
            pct = format!("{:.1}%", 100.0 * cross_shard_edges as f64 / total_edges as f64),
            "cross-shard edge count"
        );
    }

    // CMB peer wiring: compute min cross-shard latencies
    if shard_count > 1 {
        let mut min_latencies = vec![vec![Duration::MAX; shard_count]; shard_count];
        for link in &config.links {
            let fs = shard_lookup[&link.nodes.0];
            let ts = shard_lookup[&link.nodes.1];
            if fs != ts {
                if link.latency < min_latencies[fs][ts] {
                    min_latencies[fs][ts] = link.latency;
                }
                if link.latency < min_latencies[ts][fs] {
                    min_latencies[ts][fs] = link.latency;
                }
            }
        }
        let min_lookahead = config.timestamp_resolution;
        let cmb_lookahead = min_latencies.iter().flatten()
            .filter(|&&d| d != Duration::MAX)
            .min().copied().unwrap_or(Duration::MAX)
            .max(min_lookahead);
        tracing::info!(?cmb_lookahead, "CMB lookahead (min cross-shard latency)");
        for i in 0..shard_count {
            let peers: Vec<PeerShard> = (0..shard_count)
                .filter(|&j| j != i)
                .filter(|&j| min_latencies[j][i] != Duration::MAX)
                .map(|j| PeerShard {
                    time: clock_coordinators[j].shared_time(),
                    min_latency: min_latencies[j][i].max(min_lookahead),
                    time_advanced: clock_coordinators[j].time_advanced_notify(),
                })
                .collect();
            clock_coordinators[i].set_peer_shards(peers);
        }
    }

    // Create per-shard transaction producers
    let tx_producers: Vec<TransactionProducer> = per_shard_tx_sinks
        .into_iter()
        .enumerate()
        .map(|(shard, tx_sinks)| {
            TransactionProducer::new(
                ChaChaRng::seed_from_u64(rng.next_u64()),
                clocks[shard].barrier(),
                tx_sinks,
                config,
            )
        })
        .collect();

    // Assemble shards
    clock_coordinators
        .drain(..)
        .zip(networks)
        .zip(tx_producers)
        .map(|((cc, net), txp)| Shard {
            clock_coordinator: cc,
            network: Box::new(net),
            tx_producer: txp,
        })
        .collect()
}
