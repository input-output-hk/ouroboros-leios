use std::collections::{BTreeMap, HashMap};

use crate::{
    config::{NodeId, SimConfiguration},
    network::ShardLookup,
};

use super::{union_find, zero_latency_clusters};

/// Agglomerative clustering: merge lowest-latency pairs first (Kruskal-style).
///
/// Starts from 0-latency components, sorts all cross-component edges by latency,
/// and merges until shard_count components remain. This maximizes the minimum
/// cross-shard latency — the first unmerged edge defines the CMB lookahead.
pub fn assign(config: &SimConfiguration) -> ShardLookup {
    let shard_count = config.shard_count;

    // Start from 0-latency components
    let components = zero_latency_clusters::build_zero_latency_components(config);
    let num_components = components.len();

    if num_components <= shard_count {
        // Fewer components than shards — fall back to balanced assignment
        return zero_latency_clusters::assign_components_balanced(components, shard_count);
    }

    // Build union-find initialized with 0-latency component membership.
    // Use the first node in each component as the representative.
    let mut parent: HashMap<NodeId, NodeId> = HashMap::new();
    for component in &components {
        let root = component[0];
        for &node in component {
            parent.insert(node, root);
        }
    }

    // Collect all edges with latency > 0 (0-latency already merged), sorted ascending
    let mut edges: Vec<(u64, NodeId, NodeId)> = config
        .links
        .iter()
        .filter(|link| !link.latency.is_zero())
        .map(|link| (link.latency.as_nanos() as u64, link.nodes.0, link.nodes.1))
        .collect();
    edges.sort_unstable();

    // Track component sizes for balance constraint
    let mut comp_size: HashMap<NodeId, usize> = HashMap::new();
    for component in &components {
        let root = union_find::find(&mut parent, component[0]);
        comp_size.insert(root, component.len());
    }
    let avg_shard_size = config.nodes.len() / shard_count;
    let max_shard_size = avg_shard_size * config.shard_max_size_pct as usize / 100;

    // Kruskal: merge until shard_count components remain
    let mut remaining = num_components;
    for (_, a, b) in &edges {
        if remaining <= shard_count {
            break;
        }
        let ra = union_find::find(&mut parent, *a);
        let rb = union_find::find(&mut parent, *b);
        if ra != rb {
            let merged_size = comp_size[&ra] + comp_size[&rb];
            if merged_size > max_shard_size {
                continue; // skip — would create too-large cluster
            }
            union_find::union(&mut parent, *a, *b);
            let new_root = union_find::find(&mut parent, *a);
            comp_size.insert(new_root, merged_size);
            remaining -= 1;
        }
    }

    // Collect final components (BTreeMap for deterministic iteration order).
    let mut final_components: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for node in &config.nodes {
        let root = union_find::find(&mut parent, node.id);
        final_components.entry(root).or_default().push(node.id);
    }

    // Assign components to shards using greedy balanced assignment
    let components: Vec<Vec<NodeId>> = final_components.into_values().collect();
    zero_latency_clusters::assign_components_balanced(components, shard_count)
}
