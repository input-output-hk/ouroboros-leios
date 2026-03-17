use std::{collections::HashMap, sync::Arc, time::Duration};

use crate::{
    config::{NodeId, SimConfiguration},
    network::ShardLookup,
};

/// Round-robin assignment that keeps 0-latency-connected nodes on the same shard.
///
/// Phase 1: Union-Find groups nodes connected by 0-latency links.
/// Phase 2: Greedy assignment of components to shards, balanced by node count.
pub fn assign(config: &SimConfiguration) -> ShardLookup {
    let shard_count = config.shard_count;

    // Union-Find: group nodes connected by 0-latency links
    let mut parent: HashMap<NodeId, NodeId> =
        config.nodes.iter().map(|n| (n.id, n.id)).collect();

    for link in &config.links {
        if link.latency == Duration::ZERO {
            union(&mut parent, link.nodes.0, link.nodes.1);
        }
    }

    // Group nodes by component root
    let mut components: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
    for node in &config.nodes {
        let root = find(&mut parent, node.id);
        components.entry(root).or_default().push(node.id);
    }

    // Assign components to shards, largest first, greedy balance by node count
    let mut sorted: Vec<_> = components.into_values().collect();
    sorted.sort_by(|a, b| b.len().cmp(&a.len()));

    let mut shard_sizes = vec![0usize; shard_count];
    let mut lookup = HashMap::new();
    for component in sorted {
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

fn find(parent: &mut HashMap<NodeId, NodeId>, mut x: NodeId) -> NodeId {
    while parent[&x] != x {
        let grandparent = parent[&parent[&x]];
        parent.insert(x, grandparent);
        x = grandparent;
    }
    x
}

fn union(parent: &mut HashMap<NodeId, NodeId>, a: NodeId, b: NodeId) {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra != rb {
        parent.insert(ra, rb);
    }
}
