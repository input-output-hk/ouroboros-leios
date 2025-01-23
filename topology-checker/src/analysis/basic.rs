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
    pub stake_weighted_latency_ms: f64,
    pub critical_nodes: Vec<StakeIsolation>,
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

fn calculate_stake_weighted_latency(topology: &Topology) -> f64 {
    let mut weighted_sum = 0.0;
    let mut weight_sum = 0.0;

    for (_source_name, source) in &topology.nodes {
        for (dest_name, link) in &source.producers {
            let dest = &topology.nodes[dest_name];
            let weight = source.stake as f64 * dest.stake as f64;
            weighted_sum += link.latency_ms * weight;
            weight_sum += weight;
        }
    }

    if weight_sum > 0.0 {
        weighted_sum / weight_sum
    } else {
        0.0
    }
}

#[derive(Debug)]
pub struct StakeIsolation {
    pub node: String,
    pub isolated_stake: u64,
    pub percentage_of_total: f64,
}

fn find_critical_stake_nodes(topology: &Topology) -> Vec<StakeIsolation> {
    let total_stake: u64 = topology.nodes.values().map(|n| n.stake).sum();
    let mut critical_nodes = Vec::new();

    // For each node, simulate its failure and calculate isolated stake
    for (node_name, _) in &topology.nodes {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        // Start BFS from a random node that isn't the failed one
        if let Some(start) = topology.nodes.keys().find(|&n| n != node_name) {
            queue.push_back(start);
            visited.insert(start);
        }

        // BFS to find all reachable nodes
        while let Some(current) = queue.pop_front() {
            for dest in topology.nodes[current].producers.keys() {
                if dest != node_name && !visited.contains(dest) {
                    visited.insert(dest);
                    queue.push_back(dest);
                }
            }
        }

        // Calculate isolated stake
        let mut isolated_stake = 0;
        for (name, node) in &topology.nodes {
            if !visited.contains(&name) && name != node_name {
                isolated_stake += node.stake;
            }
        }

        if isolated_stake > 0 {
            let percentage = (isolated_stake as f64 / total_stake as f64) * 100.0;
            critical_nodes.push(StakeIsolation {
                node: node_name.clone(),
                isolated_stake,
                percentage_of_total: percentage,
            });
        }
    }

    // Sort by percentage of stake isolated
    critical_nodes.sort_by(|a, b| {
        b.percentage_of_total
            .partial_cmp(&a.percentage_of_total)
            .unwrap()
    });
    critical_nodes
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
    let stake_weighted_latency = calculate_stake_weighted_latency(topology);
    let critical_nodes = find_critical_stake_nodes(topology);

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
        stake_weighted_latency_ms: stake_weighted_latency,
        critical_nodes,
    }
}

#[derive(Debug)]
pub struct HopStats {
    pub hop_number: usize,
    pub latencies: Vec<f64>,
}

pub fn analyze_hop_stats(topology: &Topology, start_node: &str) -> Vec<HopStats> {
    let mut hop_stats = Vec::new();
    let mut visited = HashSet::new();

    // Initialize with start node
    let mut current_level = vec![start_node.to_string()];
    visited.insert(start_node.to_string());

    // Add hop 0 with just the start node (0 latency)
    hop_stats.push(HopStats {
        hop_number: 0,
        latencies: vec![0.0],
    });

    let mut current_hop = 0;
    while !current_level.is_empty() {
        let mut next_level = Vec::new();
        let mut current_hop_latencies = Vec::new();

        // Find all unvisited neighbors of current level nodes
        for node in &current_level {
            if let Some(node_data) = topology.nodes.get(node) {
                for (neighbor, producer) in &node_data.producers {
                    if !visited.contains(neighbor) {
                        visited.insert(neighbor.clone());
                        // Store only the direct latency between these nodes
                        current_hop_latencies.push(producer.latency_ms);
                        next_level.push(neighbor.clone());
                    }
                }
            }
        }

        // If we found any new nodes, sort and add their latencies as a new hop
        if !current_hop_latencies.is_empty() {
            current_hop += 1;
            current_hop_latencies.sort_by(|a, b| a.partial_cmp(b).unwrap());
            hop_stats.push(HopStats {
                hop_number: current_hop,
                latencies: current_hop_latencies,
            });
        }

        if next_level.is_empty() {
            break;
        }

        current_level = next_level;
    }

    hop_stats
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
            },
        );
        node1_producers.insert(
            "node3".to_string(),
            Producer {
                latency_ms: 20.0,
                bandwidth_bytes_per_second: None,
            },
        );

        let mut node2_producers = IndexMap::new();
        node2_producers.insert(
            "node3".to_string(),
            Producer {
                latency_ms: 5.0,
                bandwidth_bytes_per_second: None,
            },
        );

        let mut node3_producers = IndexMap::new();
        node3_producers.insert(
            "node4".to_string(),
            Producer {
                latency_ms: 15.0,
                bandwidth_bytes_per_second: None,
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
                cpu_core_count: Some(8),
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
                cpu_core_count: Some(4),
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
                cpu_core_count: Some(16),
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
                cpu_core_count: Some(4),
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

    #[test]
    fn test_hop_analysis() {
        let topology = create_test_topology();
        let hop_stats = analyze_hop_stats(&topology, "node1");

        // Should have 3 hops total:
        // Hop 0: node1 (0ms)
        // Hop 1: direct connections from node1 to node2 (10ms) and node3 (20ms)
        // Hop 2: connection from node3 to node4 (15ms)
        assert_eq!(hop_stats.len(), 3);

        // Check hop 0
        let hop0 = &hop_stats[0];
        assert_eq!(hop0.hop_number, 0);
        assert_eq!(hop0.latencies.len(), 1);
        assert_eq!(hop0.latencies[0], 0.0);

        // Check hop 1 - direct latencies from node1
        let hop1 = &hop_stats[1];
        assert_eq!(hop1.hop_number, 1);
        assert_eq!(hop1.latencies.len(), 2);
        assert_eq!(hop1.latencies[0], 10.0); // node1 -> node2
        assert_eq!(hop1.latencies[1], 20.0); // node1 -> node3

        // Check hop 2 - direct latency from node3 to node4
        let hop2 = &hop_stats[2];
        assert_eq!(hop2.hop_number, 2);
        assert_eq!(hop2.latencies.len(), 1);
        assert_eq!(hop2.latencies[0], 15.0); // node3 -> node4
    }

    #[test]
    fn test_hop_analysis_isolated_node() {
        // Create a topology with an isolated node
        let mut nodes = IndexMap::new();

        nodes.insert(
            "node1".to_string(),
            Node {
                location: Location::Cluster {
                    cluster: Some("eu-central-1".to_string()),
                },
                stake: 100,
                producers: IndexMap::new(), // No connections
                cpu_core_count: Some(8),
            },
        );

        nodes.insert(
            "node2".to_string(),
            Node {
                location: Location::Cluster {
                    cluster: Some("us-east-1".to_string()),
                },
                stake: 0,
                producers: IndexMap::new(),
                cpu_core_count: Some(4),
            },
        );

        let topology = Topology { nodes };
        let hop_stats = analyze_hop_stats(&topology, "node1");

        // Should only have hop 0 with the start node
        assert_eq!(hop_stats.len(), 1);
        let hop0 = &hop_stats[0];
        assert_eq!(hop0.hop_number, 0);
        assert_eq!(hop0.latencies.len(), 1);
        assert_eq!(hop0.latencies[0], 0.0);
    }

    #[test]
    fn test_hop_analysis_cycle() {
        // Create a topology with a cycle: node1 -> node2 -> node3 -> node1
        let mut nodes = IndexMap::new();

        let mut node1_producers = IndexMap::new();
        node1_producers.insert(
            "node2".to_string(),
            Producer {
                latency_ms: 10.0,
                bandwidth_bytes_per_second: None,
            },
        );

        let mut node2_producers = IndexMap::new();
        node2_producers.insert(
            "node3".to_string(),
            Producer {
                latency_ms: 20.0,
                bandwidth_bytes_per_second: None,
            },
        );

        let mut node3_producers = IndexMap::new();
        node3_producers.insert(
            "node1".to_string(),
            Producer {
                latency_ms: 30.0,
                bandwidth_bytes_per_second: None,
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
                cpu_core_count: Some(8),
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
                cpu_core_count: Some(4),
            },
        );

        nodes.insert(
            "node3".to_string(),
            Node {
                location: Location::Cluster {
                    cluster: Some("ap-southeast-2".to_string()),
                },
                stake: 0,
                producers: node3_producers,
                cpu_core_count: Some(4),
            },
        );

        let topology = Topology { nodes };
        let hop_stats = analyze_hop_stats(&topology, "node1");

        // Should have 3 hops:
        // Hop 0: node1 (0ms)
        // Hop 1: direct connection from node1 to node2 (10ms)
        // Hop 2: direct connection from node2 to node3 (20ms)
        assert_eq!(hop_stats.len(), 3);

        // Check hop 0
        let hop0 = &hop_stats[0];
        assert_eq!(hop0.hop_number, 0);
        assert_eq!(hop0.latencies.len(), 1);
        assert_eq!(hop0.latencies[0], 0.0);

        // Check hop 1 - direct latency from node1 to node2
        let hop1 = &hop_stats[1];
        assert_eq!(hop1.hop_number, 1);
        assert_eq!(hop1.latencies.len(), 1);
        assert_eq!(hop1.latencies[0], 10.0);

        // Check hop 2 - direct latency from node2 to node3
        let hop2 = &hop_stats[2];
        assert_eq!(hop2.hop_number, 2);
        assert_eq!(hop2.latencies.len(), 1);
        assert_eq!(hop2.latencies[0], 20.0);
    }
}
