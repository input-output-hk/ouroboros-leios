use std::{collections::{BTreeMap, HashMap}, sync::Arc};

use crate::{
    config::{NodeId, SimConfiguration},
    network::ShardLookup,
};

use super::zero_latency_clusters;

/// Min-cut partitioning via recursive bisection with Kernighan-Lin refinement.
/// Minimizes cross-shard edge count while maintaining balanced shard sizes.
pub fn assign(config: &SimConfiguration) -> ShardLookup {
    let shard_count = config.shard_count;

    // Build 0-latency components
    let components = zero_latency_clusters::build_zero_latency_components(config);

    if components.len() <= shard_count {
        return zero_latency_clusters::assign_components_balanced(components, shard_count);
    }

    // Build condensed adjacency: component index -> list of (neighbor index, edge count)
    let node_to_comp: HashMap<NodeId, usize> = components
        .iter()
        .enumerate()
        .flat_map(|(i, nodes)| nodes.iter().map(move |&n| (n, i)))
        .collect();

    let num_comps = components.len();
    // BTreeMap so that adjacency iteration is deterministic (affects
    // KL gain computation tie-breaking).
    let mut adj: Vec<BTreeMap<usize, usize>> = vec![BTreeMap::new(); num_comps];
    for link in &config.links {
        let ca = node_to_comp[&link.nodes.0];
        let cb = node_to_comp[&link.nodes.1];
        if ca != cb {
            *adj[ca].entry(cb).or_default() += 1;
            *adj[cb].entry(ca).or_default() += 1;
        }
    }

    let comp_sizes: Vec<usize> = components.iter().map(|c| c.len()).collect();

    // Recursive bisection to get shard_count partitions
    let initial: Vec<usize> = (0..num_comps).collect();
    let mut partitions = vec![initial];

    while partitions.len() < shard_count {
        // Find the largest partition to split
        let (idx, _) = partitions
            .iter()
            .enumerate()
            .max_by_key(|(_, p)| p.iter().map(|&c| comp_sizes[c]).sum::<usize>())
            .unwrap();
        let to_split = partitions.swap_remove(idx);
        let (a, b) = bisect_kl(&to_split, &adj, &comp_sizes);
        partitions.push(a);
        partitions.push(b);
    }

    // Map components to shard indices
    let mut lookup = HashMap::new();
    for (shard, partition) in partitions.iter().enumerate() {
        for &comp_idx in partition {
            for &node in &components[comp_idx] {
                lookup.insert(node, shard);
            }
        }
    }

    Arc::new(lookup)
}

/// Bisect a set of components into two roughly equal halves,
/// then refine with Kernighan-Lin to minimize the cut.
fn bisect_kl(
    items: &[usize],
    adj: &[BTreeMap<usize, usize>],
    comp_sizes: &[usize],
) -> (Vec<usize>, Vec<usize>) {
    let n = items.len();
    if n <= 1 {
        return (items.to_vec(), vec![]);
    }

    // Initial bisection: split at midpoint by cumulative size
    let total_size: usize = items.iter().map(|&c| comp_sizes[c]).sum();
    let half = total_size / 2;

    // Map from global comp index to local index in `items`
    let item_set: HashMap<usize, usize> = items.iter().enumerate().map(|(i, &c)| (c, i)).collect();

    let mut side: Vec<bool> = vec![false; n]; // false = A, true = B
    let mut size_a = 0;
    for (i, &comp) in items.iter().enumerate() {
        if size_a + comp_sizes[comp] <= half {
            size_a += comp_sizes[comp];
        } else {
            // Put remaining in B
            for item in side.iter_mut().skip(i) {
                *item = true;
            }
            break;
        }
    }

    // Compute external cost (edges to other side) and internal cost (edges to same side)
    // for each item. gain[i] = external[i] - internal[i]; positive = wants to move.
    let compute_gains = |side: &[bool]| -> Vec<i64> {
        let mut gains = vec![0i64; n];
        for (local_i, &comp_i) in items.iter().enumerate() {
            let mut external = 0i64;
            let mut internal = 0i64;
            for (&neighbor, &weight) in &adj[comp_i] {
                if let Some(&local_j) = item_set.get(&neighbor) {
                    if side[local_j] != side[local_i] {
                        external += weight as i64;
                    } else {
                        internal += weight as i64;
                    }
                }
            }
            gains[local_i] = external - internal;
        }
        gains
    };

    // KL iterations
    for _ in 0..10 {
        let mut gains = compute_gains(&side);
        let mut locked = vec![false; n];
        let mut best_cumulative = 0i64;
        let mut best_prefix = 0;
        let mut cumulative = 0i64;
        let mut swaps: Vec<(usize, usize)> = Vec::new();

        for step in 0..n / 2 {
            // Find best unlocked pair (a from A, b from B) maximizing gain_a + gain_b - 2*edge(a,b)
            let mut best_gain = i64::MIN;
            let mut best_a = 0;
            let mut best_b = 0;

            // Collect candidates from each side
            let mut best_a_gain = i64::MIN;
            let mut best_b_gain = i64::MIN;
            let mut a_candidates: Vec<usize> = Vec::new();
            let mut b_candidates: Vec<usize> = Vec::new();

            for i in 0..n {
                if locked[i] {
                    continue;
                }
                if !side[i] {
                    if gains[i] > best_a_gain - 100 {
                        // Keep top candidates
                        a_candidates.push(i);
                        if gains[i] > best_a_gain {
                            best_a_gain = gains[i];
                        }
                    }
                } else if gains[i] > best_b_gain - 100 {
                    b_candidates.push(i);
                    if gains[i] > best_b_gain {
                        best_b_gain = gains[i];
                    }
                }
            }

            if a_candidates.is_empty() || b_candidates.is_empty() {
                break;
            }

            // Limit candidates to top-k for performance
            a_candidates.sort_by(|&a, &b| gains[b].cmp(&gains[a]));
            a_candidates.truncate(50);
            b_candidates.sort_by(|&a, &b| gains[b].cmp(&gains[a]));
            b_candidates.truncate(50);

            for &ai in &a_candidates {
                for &bi in &b_candidates {
                    // Edge weight between ai and bi
                    let edge_ab = adj[items[ai]]
                        .get(&items[bi])
                        .copied()
                        .unwrap_or(0) as i64;
                    let gain = gains[ai] + gains[bi] - 2 * edge_ab;
                    if gain > best_gain {
                        best_gain = gain;
                        best_a = ai;
                        best_b = bi;
                    }
                }
            }

            if best_gain == i64::MIN {
                break;
            }

            // Tentatively swap
            swaps.push((best_a, best_b));
            side[best_a] = true;
            side[best_b] = false;
            locked[best_a] = true;
            locked[best_b] = true;
            cumulative += best_gain;

            if cumulative > best_cumulative {
                best_cumulative = cumulative;
                best_prefix = step + 1;
            }

            // Update gains for neighbors of swapped nodes
            // (simplified: just recompute all unlocked gains)
            gains = compute_gains(&side);
        }

        if best_cumulative <= 0 {
            // Undo all swaps — no improvement this round
            for &(a, b) in swaps.iter().rev() {
                side[a] = false;
                side[b] = true;
            }
            break;
        }

        // Undo swaps beyond the best prefix
        for &(a, b) in swaps[best_prefix..].iter().rev() {
            side[a] = false;
            side[b] = true;
        }
    }

    let mut part_a = Vec::new();
    let mut part_b = Vec::new();
    for (i, &comp) in items.iter().enumerate() {
        if !side[i] {
            part_a.push(comp);
        } else {
            part_b.push(comp);
        }
    }

    (part_a, part_b)
}
