use std::sync::Arc;

use crate::{config::SimConfiguration, network::ShardLookup};

/// Simple round-robin assignment: node_id % shard_count.
pub fn assign(config: &SimConfiguration) -> ShardLookup {
    Arc::new(
        config
            .nodes
            .iter()
            .map(|n| (n.id, n.id.to_inner() % config.shard_count))
            .collect(),
    )
}
