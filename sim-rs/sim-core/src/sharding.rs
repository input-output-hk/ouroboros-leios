mod round_robin;
pub(crate) mod shard;
mod zero_latency_clusters;

use std::sync::Arc;

use crate::{
    config::{ShardStrategy, SimConfiguration},
    network::ShardLookup,
};

/// Assign nodes to shards based on the configured strategy.
pub fn compute_shard_lookup(config: &SimConfiguration) -> ShardLookup {
    if config.shard_count <= 1 {
        return Arc::new(config.nodes.iter().map(|n| (n.id, 0)).collect());
    }
    let lookup = match config.shard_strategy {
        ShardStrategy::RoundRobin => round_robin::assign(config),
        ShardStrategy::ZeroLatencyClusters => zero_latency_clusters::assign(config),
    };

    // Log shard sizes for balance diagnostics
    let mut shard_sizes = vec![0usize; config.shard_count];
    for &shard in lookup.values() {
        shard_sizes[shard] += 1;
    }
    tracing::info!(
        strategy = ?config.shard_strategy,
        ?shard_sizes,
        "shard assignment"
    );

    lookup
}
