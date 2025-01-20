use crate::models::Topology;
use std::collections::{HashMap, HashSet, VecDeque};

pub struct NetworkStats {
    pub total_nodes: usize,
    pub block_producers: usize,
    pub relay_nodes: usize,
    pub total_connections: usize,
    pub avg_connections: f64,
    pub clustering_coefficient: f64,
    pub network_diameter: usize,
    pub avg_latency_ms: f64,
    pub max_latency_ms: f64,
    pub bidirectional_connections: usize,
    pub asymmetry_ratio: f64,
}

fn calculate_clustering_coefficient(topology: &Topology) -> f64 {
    let mut total_coefficient = 0.0;
    let mut nodes_with_neighbors = 0;

    for (_node_id, node) in &topology.nodes {
        let mut neighbors = node.producers.keys().collect::<Vec<_>>();
        for (other_id, other_node) in &topology.nodes {
            if other_node.producers.contains_key(_node_id) && !neighbors.contains(&other_id) {
                neighbors.push(other_id);
            }
        }

        if neighbors.len() < 2 {
            continue;
        }

        let mut connections = 0;
        // Check connections between neighbors
        // We count a connection if either node has the other as a producer
        for (i, &n1) in neighbors.iter().enumerate() {
            for &n2 in neighbors.iter().skip(i + 1) {
                // Check both directions since connections can be asymmetric
                // Each direction counts as a separate connection
                if topology.nodes[n1].producers.contains_key(n2) {
                    connections += 1;
                }
                if topology.nodes[n2].producers.contains_key(n1) {
                    connections += 1;
                }
            }
        }

        let possible_connections = (neighbors.len() * (neighbors.len() - 1)) / 2;
        total_coefficient += connections as f64 / possible_connections as f64;
        nodes_with_neighbors += 1;
    }

    if nodes_with_neighbors > 0 {
        total_coefficient / nodes_with_neighbors as f64
    } else {
        0.0
    }
}

fn calculate_network_diameter(topology: &Topology) -> usize {
    let mut max_distance = 0;
    let nodes: Vec<_> = topology.nodes.keys().collect();

    // For each node
    for &start_node in &nodes {
        let mut visited = HashMap::new();
        let mut distances = HashMap::new();
        let mut queue = VecDeque::new();

        visited.insert(start_node, true);
        distances.insert(start_node, 0);
        queue.push_back(start_node);

        while let Some(node) = queue.pop_front() {
            let current_dist = distances[node];

            // Check all neighbors
            for neighbor in topology.nodes[node].producers.keys() {
                if !visited.contains_key(neighbor) {
                    visited.insert(neighbor, true);
                    let new_dist = current_dist + 1;
                    distances.insert(neighbor, new_dist);
                    queue.push_back(neighbor);
                    max_distance = max_distance.max(new_dist);
                }
            }
        }
    }

    max_distance
}

fn calculate_latency_stats(topology: &Topology) -> (f64, f64) {
    let mut total_latency = 0.0;
    let mut max_latency = 0.0;
    let mut connection_count = 0;

    for node in topology.nodes.values() {
        for producer in node.producers.values() {
            total_latency += producer.latency_ms;
            max_latency = f64::max(max_latency, producer.latency_ms);
            connection_count += 1;
        }
    }

    let avg_latency = if connection_count > 0 {
        total_latency / connection_count as f64
    } else {
        0.0
    };

    (avg_latency, max_latency)
}

pub fn analyze_network_stats(topology: &Topology) -> NetworkStats {
    let total_nodes = topology.nodes.len();
    let total_connections: usize = topology
        .nodes
        .values()
        .map(|node| node.producers.len())
        .sum();
    let avg_connections = total_connections as f64 / total_nodes as f64;
    let clustering_coefficient = calculate_clustering_coefficient(topology);
    let network_diameter = calculate_network_diameter(topology);
    let block_producers = topology.nodes.values().filter(|n| n.stake > 0).count();
    let relay_nodes = total_nodes - block_producers;
    let (avg_latency, max_latency) = calculate_latency_stats(topology);

    // Calculate asymmetry metrics
    let mut bidirectional_count = 0;
    let mut seen_pairs = HashSet::new();

    for (node_name, node) in &topology.nodes {
        for producer_name in node.producers.keys() {
            let pair = if node_name < producer_name {
                (node_name.clone(), producer_name.clone())
            } else {
                (producer_name.clone(), node_name.clone())
            };

            if seen_pairs.contains(&pair) {
                continue;
            }
            seen_pairs.insert(pair);

            let is_bidirectional = topology.nodes[producer_name]
                .producers
                .contains_key(node_name);
            if is_bidirectional {
                bidirectional_count += 1;
            }
        }
    }

    let asymmetry_ratio = if total_connections > 0 {
        1.0 - (2.0 * bidirectional_count as f64 / total_connections as f64)
    } else {
        0.0
    };

    NetworkStats {
        total_nodes,
        block_producers,
        relay_nodes,
        total_connections,
        avg_connections,
        clustering_coefficient,
        network_diameter,
        avg_latency_ms: avg_latency,
        max_latency_ms: max_latency,
        bidirectional_connections: bidirectional_count,
        asymmetry_ratio,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{Location, Node, Producer};
    use indexmap::IndexMap;

    fn create_test_topology() -> Topology {
        let mut nodes = IndexMap::new();

        // Create a simple topology with 4 nodes:
        // node1 (BP) <-> node2 (Relay) <-> node3 (BP) <-> node4 (Relay)
        // node1 also connects to node3 directly

        let mut node1_producers = IndexMap::new();
        node1_producers.insert(
            "node2".to_string(),
            Producer {
                latency_ms: 10.0,
                bandwidth_bytes_per_second: None,
                cpu_core_count: None,
            },
        );
        node1_producers.insert(
            "node3".to_string(),
            Producer {
                latency_ms: 20.0,
                bandwidth_bytes_per_second: None,
                cpu_core_count: None,
            },
        );

        let mut node2_producers = IndexMap::new();
        node2_producers.insert(
            "node3".to_string(),
            Producer {
                latency_ms: 5.0,
                bandwidth_bytes_per_second: None,
                cpu_core_count: None,
            },
        );

        let mut node3_producers = IndexMap::new();
        node3_producers.insert(
            "node4".to_string(),
            Producer {
                latency_ms: 15.0,
                bandwidth_bytes_per_second: None,
                cpu_core_count: None,
            },
        );

        nodes.insert(
            "node1".to_string(),
            Node {
                location: Location::Cluster {
                    cluster: Some("eu-central-1".to_string()),
                },
                stake: 100,
                producers: node1_producers,
            },
        );

        nodes.insert(
            "node2".to_string(),
            Node {
                location: Location::Cluster {
                    cluster: Some("us-east-1".to_string()),
                },
                stake: 0,
                producers: node2_producers,
            },
        );

        nodes.insert(
            "node3".to_string(),
            Node {
                location: Location::Cluster {
                    cluster: Some("ap-southeast-2".to_string()),
                },
                stake: 200,
                producers: node3_producers,
            },
        );

        nodes.insert(
            "node4".to_string(),
            Node {
                location: Location::Cluster {
                    cluster: Some("eu-central-1".to_string()),
                },
                stake: 0,
                producers: IndexMap::new(),
            },
        );

        Topology { nodes }
    }

    #[test]
    fn test_network_stats() {
        let topology = create_test_topology();
        let stats = analyze_network_stats(&topology);

        assert_eq!(stats.total_nodes, 4);
        assert_eq!(stats.block_producers, 2);
        assert_eq!(stats.relay_nodes, 2);
        assert_eq!(stats.total_connections, 4);
        assert_eq!(stats.avg_connections, 1.0);
        assert_eq!(stats.network_diameter, 2);
        assert!(stats.clustering_coefficient >= 0.0 && stats.clustering_coefficient <= 1.0);
    }

    #[test]
    fn test_latency_stats() {
        let topology = create_test_topology();
        let stats = analyze_network_stats(&topology);

        // Total latencies: 10.0 + 20.0 + 5.0 + 15.0 = 50.0
        // Number of connections: 4
        // Average should be 12.5
        assert!((stats.avg_latency_ms - 12.5).abs() < f64::EPSILON);
        assert!((stats.max_latency_ms - 20.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_clustering_coefficient() {
        let topology = create_test_topology();
        let coefficient = calculate_clustering_coefficient(&topology);

        // Node1 has 2 neighbors (node2, node3), and they are connected = 1 connection out of 1 possible
        // Node2 has 2 neighbors (node1, node3), and they are connected = 1 connection out of 1 possible
        // Node3 has 3 neighbors (node1, node2, node4), and 1 connection (node1-node2) out of 3 possible
        // Node4 has 1 neighbor, so doesn't contribute
        // Average should be (1.0 + 1.0 + 0.33) / 3 ≈ 0.777
        assert!((coefficient - 0.777).abs() < 0.001);
    }
}
