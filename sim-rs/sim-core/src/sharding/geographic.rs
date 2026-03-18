use std::collections::HashMap;

use crate::{
    config::{NodeId, SimConfiguration},
    network::ShardLookup,
};

use super::zero_latency_clusters;

/// Geographic clustering: k-means on node coordinates, keeping 0-latency
/// components together. Maximizes cross-shard latency by grouping nearby nodes.
pub fn assign(config: &SimConfiguration) -> ShardLookup {
    let shard_count = config.shard_count;

    // Build 0-latency components
    let components = zero_latency_clusters::build_zero_latency_components(config);

    // Build a map from NodeId to coordinates for centroid computation
    let coords: HashMap<NodeId, (f64, f64)> = config
        .nodes
        .iter()
        .filter_map(|n| n.location.map(|loc| (n.id, loc)))
        .collect();

    // Fall back to zero_latency_clusters if any nodes lack coordinates
    if coords.len() != config.nodes.len() {
        tracing::warn!(
            "geographic sharding: {} nodes lack coordinates, falling back to zero-latency-clusters",
            config.nodes.len() - coords.len()
        );
        return zero_latency_clusters::assign(config);
    }

    // Compute centroid and size for each component
    let comp_data: Vec<(Vec<NodeId>, f64, f64, usize)> = components
        .into_iter()
        .map(|nodes| {
            let n = nodes.len() as f64;
            let (sum_lat, sum_lon) = nodes.iter().fold((0.0, 0.0), |(slat, slon), id| {
                let (lat, lon) = coords[id];
                (slat + lat, slon + lon)
            });
            (nodes, sum_lat / n, sum_lon / n, n as usize)
        })
        .collect();

    if comp_data.len() <= shard_count {
        // Fewer components than shards — just assign one per shard
        return zero_latency_clusters::assign_components_balanced(
            comp_data.into_iter().map(|(nodes, ..)| nodes).collect(),
            shard_count,
        );
    }

    // K-means++ initialization
    let mut centroids: Vec<(f64, f64)> = Vec::with_capacity(shard_count);

    // First centroid: component with most nodes (deterministic)
    let first = comp_data
        .iter()
        .enumerate()
        .max_by_key(|(_, (_, _, _, size))| *size)
        .unwrap()
        .0;
    centroids.push((comp_data[first].1, comp_data[first].2));

    // Remaining centroids: pick component farthest from nearest existing centroid
    for _ in 1..shard_count {
        let mut best_idx = 0;
        let mut best_dist = 0.0f64;
        for (i, (_, lat, lon, _)) in comp_data.iter().enumerate() {
            let min_dist = centroids
                .iter()
                .map(|(clat, clon)| {
                    let dlat = lat - clat;
                    let dlon = lon - clon;
                    dlat * dlat + dlon * dlon
                })
                .fold(f64::MAX, f64::min);
            if min_dist > best_dist {
                best_dist = min_dist;
                best_idx = i;
            }
        }
        centroids.push((comp_data[best_idx].1, comp_data[best_idx].2));
    }

    // K-means iteration
    let mut assignments = vec![0usize; comp_data.len()];
    for _ in 0..20 {
        // Assign each component to nearest centroid
        for (i, (_, lat, lon, _)) in comp_data.iter().enumerate() {
            let nearest = centroids
                .iter()
                .enumerate()
                .map(|(j, (clat, clon))| {
                    let dlat = lat - clat;
                    let dlon = lon - clon;
                    (j, dlat * dlat + dlon * dlon)
                })
                .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
                .unwrap()
                .0;
            assignments[i] = nearest;
        }

        // Recompute centroids weighted by component size
        let mut new_centroids = vec![(0.0f64, 0.0f64, 0usize); shard_count];
        for (i, (_, lat, lon, size)) in comp_data.iter().enumerate() {
            let c = &mut new_centroids[assignments[i]];
            c.0 += lat * (*size as f64);
            c.1 += lon * (*size as f64);
            c.2 += size;
        }
        for (j, (slat, slon, count)) in new_centroids.iter().enumerate() {
            if *count > 0 {
                centroids[j] = (slat / *count as f64, slon / *count as f64);
            }
        }
    }

    // Build shard lookup from assignments
    let mut lookup = HashMap::new();
    for (i, (nodes, ..)) in comp_data.iter().enumerate() {
        let shard = assignments[i];
        for node in nodes {
            lookup.insert(*node, shard);
        }
    }

    std::sync::Arc::new(lookup)
}
