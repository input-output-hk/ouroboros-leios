#![allow(dead_code)]

use crate::models::{Latency, Node, Topology};
use delta_q::CDF;
use indexmap::IndexMap;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::collections::{HashMap, HashSet, VecDeque};

pub struct NetworkStats {
    pub total_nodes: usize,
    pub block_producers: usize,
    pub relay_nodes: usize,
    pub total_connections: usize,
    pub avg_connections: f64,
    pub clustering_coefficient: f64,
    pub network_diameter: usize,
    pub avg_latency_ms: Latency,
    pub max_latency_ms: Latency,
    pub bidirectional_connections: usize,
    pub asymmetry_ratio: f64,
    pub stake_weighted_latency_ms: Latency,
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

fn calculate_latency_stats(topology: &Topology) -> (Latency, Latency) {
    let mut total_latency = Latency::zero();
    let mut max_latency = Latency::zero();
    let mut connection_count = 0;

    for node in topology.nodes.values() {
        for producer in node.producers.values() {
            total_latency += producer.latency_ms;
            max_latency = max_latency.max(producer.latency_ms);
            connection_count += 1;
        }
    }

    let avg_latency = if connection_count > 0 {
        total_latency / connection_count as f64
    } else {
        Latency::zero()
    };

    (avg_latency, max_latency)
}

fn calculate_stake_weighted_latency(topology: &Topology) -> Latency {
    let mut weighted_sum = Latency::zero();
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
        Latency::zero()
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
    pub latencies: Vec<Latency>,
}

pub struct ReversedTopology {
    pub nodes: IndexMap<String, Node>,
}

/// Reverses the topology by swapping the source and destination of each connection
pub fn reverse_topology(topology: &Topology) -> ReversedTopology {
    // Start by creating reversed nodes with the same nodes but empty producers
    let mut reversed_nodes: IndexMap<String, Node> = topology
        .nodes
        .iter()
        .map(|(node_name, node)| {
            (
                node_name.clone(),
                Node {
                    location: node.location.clone(),
                    stake: node.stake,
                    cpu_core_count: node.cpu_core_count,
                    producers: IndexMap::new(),
                },
            )
        })
        .collect();

    // For each node in the original topology, reverse the edges
    for (node_name, node) in &topology.nodes {
        for (producer_name, producer) in &node.producers {
            // In the reversed topology, add a connection from producer_name to node_name
            reversed_nodes
                .get_mut(producer_name)
                .expect("Producer node doesn't exist in the topology")
                .producers
                .insert(node_name.clone(), producer.clone());
        }
    }

    ReversedTopology {
        nodes: reversed_nodes,
    }
}

pub fn analyze_hop_stats(topology: &ReversedTopology, start_node: &str) -> Vec<HopStats> {
    let mut hop_stats = Vec::new();
    let mut visited = HashSet::new();

    // Initialize with start node
    let mut current_level = vec![start_node.to_string()];
    visited.insert(start_node.to_string());

    // Add hop 0 with just the start node (0 latency)
    hop_stats.push(HopStats {
        hop_number: 0,
        latencies: vec![Latency::zero()],
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

pub struct ShortestPathLink {
    pub node: String,
    pub latency: Latency,
    pub total: Latency,
    pub hops: usize,
}

pub fn shortest_paths(
    topology: &ReversedTopology,
    start_node: &str,
) -> HashMap<String, ShortestPathLink> {
    // Min-heap to select the node with the smallest cumulative latency
    let mut heap = BinaryHeap::new();
    // Map to keep track of the shortest known distances to each node
    let mut distances = HashMap::new();
    // Map to store the shortest path links
    let mut shortest_paths = HashMap::new();

    // Initialize the distance to the start node as 0 and push it to the heap
    distances.insert(start_node.to_string(), Latency::zero());
    heap.push(Reverse((Latency::zero(), 0usize, start_node.to_string())));

    while let Some(Reverse((current_dist, current_hops, current_node))) = heap.pop() {
        // If we've already found a better path, skip processing this node
        if current_dist > distances[&current_node] {
            continue;
        }

        // Examine neighbors of the current node
        if let Some(node_data) = topology.nodes.get(&current_node) {
            for (neighbor, producer) in &node_data.producers {
                let new_dist = current_dist + producer.latency_ms;

                // If a shorter path to the neighbor is found
                if new_dist < *distances.get(neighbor).unwrap_or(&Latency::infinity()) {
                    distances.insert(neighbor.clone(), new_dist);
                    heap.push(Reverse((new_dist, current_hops + 1, neighbor.clone())));

                    // Record the path
                    shortest_paths.insert(
                        neighbor.clone(),
                        ShortestPathLink {
                            node: current_node.clone(),
                            latency: producer.latency_ms,
                            total: new_dist,
                            hops: current_hops + 1,
                        },
                    );
                }
            }
        }
    }

    shortest_paths
}

#[derive(Debug)]
pub struct AllPathStats {
    pub reached_min: f32,
    pub reached_avg: f32,
    pub reached_max: f32,
    pub latency_min: CDF,
    pub latency_avg: CDF,
    pub latency_max: CDF,
    inputs: f32,
    latencies: f32,
}

impl AllPathStats {
    pub fn new_with_empty(n: usize) -> Self {
        let reached_min = if n == 0 { f32::INFINITY } else { 0.0 };
        Self {
            reached_min,
            reached_avg: 0.0,
            reached_max: 0.0,
            latency_min: CDF::top(),
            latency_avg: CDF::default(),
            latency_max: CDF::bottom(),
            inputs: n as f32,
            latencies: 0.0,
        }
    }

    pub fn add_hop_stats(&mut self, mut hop_stats: HopStats) {
        let reached = hop_stats.latencies.len() as f32;
        hop_stats.latencies.sort();
        let scale = 1.0 / reached as f32;
        let latency = hop_stats
            .latencies
            .into_iter()
            .enumerate()
            .map(|(i, l)| (l.as_f32(), (i as f32 + 1.0) * scale))
            .collect::<CDF>();

        self.reached_min = f32::min(self.reached_min, reached);
        self.reached_avg = (self.reached_avg * self.inputs + reached) / (self.inputs + 1.0);
        self.reached_max = f32::max(self.reached_max, reached);
        self.inputs += 1.0;

        self.latency_min = self.latency_min.min(&latency);
        self.latency_avg = self
            .latency_avg
            .choice(self.latencies / (self.latencies + 1.0), &latency)
            .expect("Failed to add latency");
        self.latency_max = self.latency_max.max(&latency);
        self.latencies += 1.0;
    }

    pub fn add_hop_reached(&mut self, reached: f32) {
        self.reached_min = f32::min(self.reached_min, reached);
        self.reached_avg = (self.reached_avg * self.inputs + reached) / (self.inputs + 1.0);
        self.reached_max = f32::max(self.reached_max, reached);
        self.inputs += 1.0;
    }
}

/// This function analyzes the topology by
/// - getting the hop state for each node
/// - folding the contained per-hop stats into an AllPathStats aggregation
pub fn analyze_all_paths(topology: &Topology) -> Vec<AllPathStats> {
    let reversed_topology = reverse_topology(topology);
    let mut all_path_stats = Vec::<AllPathStats>::new();
    for (idx, node) in reversed_topology.nodes.keys().enumerate() {
        let hop_stats = analyze_hop_stats(&reversed_topology, node);
        for idx in hop_stats.len()..all_path_stats.len() {
            all_path_stats[idx].add_hop_reached(0.0);
        }
        for hop_stats in hop_stats {
            if all_path_stats.len() <= hop_stats.hop_number {
                all_path_stats.push(AllPathStats::new_with_empty(idx));
            }
            all_path_stats[hop_stats.hop_number].add_hop_stats(hop_stats);
        }
    }
    all_path_stats
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
                latency_ms: 10.0.try_into().unwrap(),
                bandwidth_bytes_per_second: None,
            },
        );
        node1_producers.insert(
            "node3".to_string(),
            Producer {
                latency_ms: 20.0.try_into().unwrap(),
                bandwidth_bytes_per_second: None,
            },
        );

        let mut node2_producers = IndexMap::new();
        node2_producers.insert(
            "node3".to_string(),
            Producer {
                latency_ms: 5.0.try_into().unwrap(),
                bandwidth_bytes_per_second: None,
            },
        );

        let mut node3_producers = IndexMap::new();
        node3_producers.insert(
            "node4".to_string(),
            Producer {
                latency_ms: 15.0.try_into().unwrap(),
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
        assert!((stats.avg_latency_ms.as_f64() - 12.5).abs() < f64::EPSILON);
        assert!((stats.max_latency_ms.as_f64() - 20.0).abs() < f64::EPSILON);
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
        // test topology is already reversed
        let topology = ReversedTopology {
            nodes: topology.nodes,
        };
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
        assert_eq!(hop0.latencies[0], Latency::zero());

        // Check hop 1 - direct latencies from node1
        let hop1 = &hop_stats[1];
        assert_eq!(hop1.hop_number, 1);
        assert_eq!(hop1.latencies.len(), 2);
        assert_eq!(hop1.latencies[0].as_f64(), 10.0); // node1 -> node2
        assert_eq!(hop1.latencies[1].as_f64(), 20.0); // node1 -> node3

        // Check hop 2 - direct latency from node3 to node4
        let hop2 = &hop_stats[2];
        assert_eq!(hop2.hop_number, 2);
        assert_eq!(hop2.latencies.len(), 1);
        assert_eq!(hop2.latencies[0].as_f64(), 15.0); // node3 -> node4
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

        let topology = ReversedTopology { nodes };
        let hop_stats = analyze_hop_stats(&topology, "node1");

        // Should only have hop 0 with the start node
        assert_eq!(hop_stats.len(), 1);
        let hop0 = &hop_stats[0];
        assert_eq!(hop0.hop_number, 0);
        assert_eq!(hop0.latencies.len(), 1);
        assert_eq!(hop0.latencies[0].as_f64(), 0.0);
    }

    #[test]
    fn test_hop_analysis_cycle() {
        // Create a topology with a cycle: node1 -> node2 -> node3 -> node1
        let mut nodes = IndexMap::new();

        let mut node1_producers = IndexMap::new();
        node1_producers.insert(
            "node2".to_string(),
            Producer {
                latency_ms: 10.0.try_into().unwrap(),
                bandwidth_bytes_per_second: None,
            },
        );

        let mut node2_producers = IndexMap::new();
        node2_producers.insert(
            "node3".to_string(),
            Producer {
                latency_ms: 20.0.try_into().unwrap(),
                bandwidth_bytes_per_second: None,
            },
        );

        let mut node3_producers = IndexMap::new();
        node3_producers.insert(
            "node1".to_string(),
            Producer {
                latency_ms: 30.0.try_into().unwrap(),
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

        let topology = ReversedTopology { nodes };
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
        assert_eq!(hop0.latencies[0].as_f64(), 0.0);

        // Check hop 1 - direct latency from node1 to node2
        let hop1 = &hop_stats[1];
        assert_eq!(hop1.hop_number, 1);
        assert_eq!(hop1.latencies.len(), 1);
        assert_eq!(hop1.latencies[0].as_f64(), 10.0);

        // Check hop 2 - direct latency from node2 to node3
        let hop2 = &hop_stats[2];
        assert_eq!(hop2.hop_number, 2);
        assert_eq!(hop2.latencies.len(), 1);
        assert_eq!(hop2.latencies[0].as_f64(), 20.0);
    }
}
