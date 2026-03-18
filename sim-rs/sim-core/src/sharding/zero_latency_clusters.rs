use std::{collections::HashMap, sync::Arc, time::Duration};

use crate::{
    config::{NodeId, SimConfiguration},
    network::ShardLookup,
};

use super::union_find;

/// Round-robin assignment that keeps 0-latency-connected nodes on the same shard.
///
/// Phase 1: Union-Find groups nodes connected by 0-latency links.
/// Phase 2: Greedy assignment of components to shards, balanced by node count.
pub fn assign(config: &SimConfiguration) -> ShardLookup {
    let components = build_zero_latency_components(config);
    assign_components_balanced(components, config.shard_count)
}

/// Build components of nodes connected by 0-latency links.
pub fn build_zero_latency_components(config: &SimConfiguration) -> Vec<Vec<NodeId>> {
    let mut parent: HashMap<NodeId, NodeId> =
        config.nodes.iter().map(|n| (n.id, n.id)).collect();

    for link in &config.links {
        if link.latency == Duration::ZERO {
            union_find::union(&mut parent, link.nodes.0, link.nodes.1);
        }
    }

    let mut components: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
    for node in &config.nodes {
        let root = union_find::find(&mut parent, node.id);
        components.entry(root).or_default().push(node.id);
    }

    components.into_values().collect()
}

/// Assign components to shards, largest first, greedy balance by node count.
pub fn assign_components_balanced(
    mut components: Vec<Vec<NodeId>>,
    shard_count: usize,
) -> ShardLookup {
    components.sort_by_key(|b| std::cmp::Reverse(b.len()));

    let mut shard_sizes = vec![0usize; shard_count];
    let mut lookup = HashMap::new();
    for component in components {
        let shard = shard_sizes
            .iter()
            .enumerate()
            .min_by_key(|&(_, size)| size)
            .unwrap()
            .0;
        shard_sizes[shard] += component.len();
        for node in component {
            lookup.insert(node, shard);
        }
    }

    Arc::new(lookup)
}
