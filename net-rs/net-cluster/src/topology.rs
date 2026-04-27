//! Random network topology generation.
//!
//! Generates a connected random graph with configurable degree, port
//! allocation, latency assignment, and stake distribution.

use rand::prelude::*;
use serde::Serialize;

use crate::config::ClusterConfig;

/// A peer link from one node to another.
#[derive(Debug, Clone, Serialize)]
pub struct PeerLink {
    /// Address of the peer (e.g. "127.0.0.1:30001").
    pub address: String,
    /// Simulated inbound delay in milliseconds.
    pub inbound_delay_ms: u64,
}

/// Per-node topology information.
#[derive(Debug, Clone, Serialize)]
pub struct NodeTopology {
    /// Index in the cluster (0..num_nodes).
    pub index: usize,
    /// Human-readable node ID ("node-0", "node-1", ...).
    pub node_id: String,
    /// Listen address ("127.0.0.1:{port}").
    pub listen_address: String,
    /// Listen port.
    pub listen_port: u16,
    /// Stake share for this node.
    pub stake: u64,
    /// Deterministic PRNG seed for this node.
    pub seed: u64,
    /// Outbound peer connections (not serialized — use `edges` instead).
    #[serde(skip)]
    pub peers: Vec<PeerLink>,
}

/// An undirected edge in the topology.
#[derive(Debug, Clone, Serialize)]
pub struct Edge {
    pub from: usize,
    pub to: usize,
    pub latency_ms: u64,
}

/// Complete cluster topology.
#[derive(Debug, Clone, Serialize)]
pub struct Topology {
    pub nodes: Vec<NodeTopology>,
    pub edges: Vec<Edge>,
}

/// Generate a random cluster topology from the given config.
///
/// The `total_stake` parameter comes from the base config and is divided
/// among nodes according to the stake distribution strategy.
pub fn generate(config: &ClusterConfig, total_stake: u64) -> Topology {
    let n = config.num_nodes;
    let mut rng = match config.seed {
        Some(s) => StdRng::seed_from_u64(s),
        None => StdRng::from_entropy(),
    };

    // Step 1: Build random graph edges.
    let edges = build_random_graph(n, config.degree, config, &mut rng);

    // Step 2: Distribute stake.
    let stakes = distribute_stake(n, total_stake, &config.stake_distribution);

    // Step 3: Build node topologies.
    let mut nodes: Vec<NodeTopology> = (0..n)
        .map(|i| {
            let port = config.base_port + i as u16;
            NodeTopology {
                index: i,
                node_id: format!("node-{i}"),
                listen_address: format!("127.0.0.1:{port}"),
                listen_port: port,
                stake: stakes[i],
                seed: config.seed.unwrap_or(0) + i as u64,
                peers: Vec::new(),
            }
        })
        .collect();

    // Step 4: Convert edges to peer links (directional: from → to only).
    // Accepted connections run duplex (both client + server protocols),
    // so only one direction per edge is needed.
    for edge in &edges {
        let to_addr = nodes[edge.to].listen_address.clone();
        nodes[edge.from].peers.push(PeerLink {
            address: to_addr,
            inbound_delay_ms: edge.latency_ms,
        });
    }

    // Step 5: Inject external peers.
    for ext in &config.external_peers {
        let count = ext.inject_into_nodes.min(n);
        let chosen: Vec<usize> = (0..n)
            .collect::<Vec<_>>()
            .partial_shuffle(&mut rng, count)
            .0
            .to_vec();
        for &i in &chosen {
            nodes[i].peers.push(PeerLink {
                address: ext.address.clone(),
                inbound_delay_ms: 0,
            });
        }
    }

    Topology { nodes, edges }
}

/// Build a random undirected graph with target degree, ensuring connectivity.
fn build_random_graph(
    n: usize,
    degree: usize,
    config: &ClusterConfig,
    rng: &mut StdRng,
) -> Vec<Edge> {
    if n <= 1 {
        return Vec::new();
    }

    // Adjacency set for dedup.
    let mut adj: Vec<std::collections::HashSet<usize>> = vec![std::collections::HashSet::new(); n];
    let mut edges = Vec::new();

    // For each node, try to connect to `degree` random others.
    for i in 0..n {
        let mut candidates: Vec<usize> =
            (0..n).filter(|&j| j != i && !adj[i].contains(&j)).collect();
        candidates.shuffle(rng);

        let needed = degree.saturating_sub(adj[i].len());
        for &j in candidates.iter().take(needed) {
            let latency = rng.gen_range(config.min_latency_ms..=config.max_latency_ms);
            adj[i].insert(j);
            adj[j].insert(i);
            edges.push(Edge {
                from: i,
                to: j,
                latency_ms: latency,
            });
        }
    }

    // Ensure connectivity: find connected components and bridge them.
    let components = find_components(n, &adj);
    if components.len() > 1 {
        for pair in components.windows(2) {
            let a = pair[0][0];
            let b = pair[1][0];
            if !adj[a].contains(&b) {
                let latency = rng.gen_range(config.min_latency_ms..=config.max_latency_ms);
                adj[a].insert(b);
                adj[b].insert(a);
                edges.push(Edge {
                    from: a,
                    to: b,
                    latency_ms: latency,
                });
            }
        }
    }

    edges
}

/// Find connected components via BFS.
fn find_components(n: usize, adj: &[std::collections::HashSet<usize>]) -> Vec<Vec<usize>> {
    let mut visited = vec![false; n];
    let mut components = Vec::new();

    for start in 0..n {
        if visited[start] {
            continue;
        }
        let mut component = Vec::new();
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(start);
        visited[start] = true;
        while let Some(node) = queue.pop_front() {
            component.push(node);
            for &neighbor in &adj[node] {
                if !visited[neighbor] {
                    visited[neighbor] = true;
                    queue.push_back(neighbor);
                }
            }
        }
        components.push(component);
    }

    components
}

/// Default fraction of nodes that are zero-stake relays under
/// `mainnet-shaped`. Derived from analysis of
/// data/simulation/pseudo-mainnet/topology-v2.yaml: 534 / 750 = 0.712.
const MAINNET_RELAY_FRACTION: f64 = 0.71;

/// Distribute stake among nodes.
///
/// Strategies:
/// - `"equal"`: every node gets `total_stake / n`.
/// - `"mainnet-shaped"`: `MAINNET_RELAY_FRACTION` of the nodes get stake 0
///   (relays); the remaining nodes (pools) split the total uniformly. This
///   captures the dominant feature of Cardano mainnet's stake distribution
///   — most nodes are zero-stake relays, with a saturated pool tail that's
///   nearly uniform (slope ≈ -0.06 in log-rank). Pools occupy the lower
///   indices so node-0..node-(pool_count-1) are pools.
fn distribute_stake(n: usize, total_stake: u64, strategy: &str) -> Vec<u64> {
    match strategy {
        "equal" => {
            let per_node = total_stake / n as u64;
            let remainder = total_stake % n as u64;
            let mut stakes: Vec<u64> = vec![per_node; n];
            // Give remainder to the last node.
            if let Some(last) = stakes.last_mut() {
                *last += remainder;
            }
            stakes
        }
        "mainnet-shaped" => {
            let relay_count = ((n as f64) * MAINNET_RELAY_FRACTION).round() as usize;
            let relay_count = relay_count.min(n.saturating_sub(1));
            let pool_count = n - relay_count;
            if pool_count == 0 {
                return vec![0; n];
            }
            let per_pool = total_stake / pool_count as u64;
            let remainder = total_stake % pool_count as u64;
            let mut stakes = Vec::with_capacity(n);
            for i in 0..pool_count {
                let extra = if (i as u64) < remainder { 1 } else { 0 };
                stakes.push(per_pool + extra);
            }
            stakes.extend(std::iter::repeat_n(0, relay_count));
            stakes
        }
        _ => {
            // Unknown strategy: fall back to equal.
            tracing::warn!("unknown stake distribution '{strategy}', falling back to equal");
            distribute_stake(n, total_stake, "equal")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_config(num_nodes: usize, degree: usize) -> ClusterConfig {
        ClusterConfig {
            num_nodes,
            degree,
            min_latency_ms: 10,
            max_latency_ms: 100,
            base_config: "test.toml".to_string(),
            base_port: 30000,
            seed: Some(42),
            ..ClusterConfig::default()
        }
    }

    #[test]
    fn test_single_node() {
        let config = test_config(1, 0);
        let topo = generate(&config, 1000);
        assert_eq!(topo.nodes.len(), 1);
        assert!(topo.edges.is_empty());
        assert_eq!(topo.nodes[0].stake, 1000);
    }

    #[test]
    fn test_two_nodes() {
        let config = test_config(2, 1);
        let topo = generate(&config, 1000);
        assert_eq!(topo.nodes.len(), 2);
        assert!(!topo.edges.is_empty());
        // Directional: only the `from` node has a peer link.
        let total_peers: usize = topo.nodes.iter().map(|n| n.peers.len()).sum();
        assert_eq!(total_peers, topo.edges.len());
    }

    #[test]
    fn test_connectivity() {
        let config = test_config(10, 2);
        let topo = generate(&config, 10000);

        // Verify connectivity via BFS from node 0.
        let adj = build_adjacency(&topo);
        let components = find_components(10, &adj);
        assert_eq!(components.len(), 1, "graph should be connected");
    }

    #[test]
    fn test_port_allocation() {
        let config = test_config(5, 2);
        let topo = generate(&config, 5000);
        for (i, node) in topo.nodes.iter().enumerate() {
            assert_eq!(node.listen_port, 30000 + i as u16);
            assert_eq!(node.node_id, format!("node-{i}"));
        }
    }

    #[test]
    fn test_stake_distribution_equal() {
        let stakes = distribute_stake(3, 1000, "equal");
        assert_eq!(stakes, vec![333, 333, 334]);
    }

    #[test]
    fn test_stake_distribution_mainnet_shaped_relay_split() {
        // 100 nodes × 0.71 = 71 relays, 29 pools.
        let stakes = distribute_stake(100, 1_000_000, "mainnet-shaped");
        let zero_count = stakes.iter().filter(|s| **s == 0).count();
        let pool_count = stakes.iter().filter(|s| **s > 0).count();
        assert_eq!(zero_count, 71);
        assert_eq!(pool_count, 29);
    }

    #[test]
    fn test_stake_distribution_mainnet_shaped_total_preserved() {
        let total = 12_697_141_247u64;
        let stakes = distribute_stake(750, total, "mainnet-shaped");
        assert_eq!(stakes.iter().sum::<u64>(), total);
    }

    #[test]
    fn test_stake_distribution_mainnet_shaped_pools_first() {
        let stakes = distribute_stake(10, 1_000_000, "mainnet-shaped");
        // Pools occupy low indices; relays follow.
        let mut seen_zero = false;
        for s in &stakes {
            if *s == 0 {
                seen_zero = true;
            } else {
                assert!(!seen_zero, "pool encountered after relay");
            }
        }
    }

    #[test]
    fn test_stake_distribution_mainnet_shaped_small_n() {
        // 2 nodes, 0.71 fraction → would round to 1 relay, but min 1 pool.
        let stakes = distribute_stake(2, 1000, "mainnet-shaped");
        assert_eq!(stakes.len(), 2);
        assert_eq!(stakes.iter().sum::<u64>(), 1000);
        assert_eq!(stakes.iter().filter(|s| **s > 0).count(), 1);
    }

    #[test]
    fn test_stake_distribution_mainnet_shaped_pools_nearly_uniform() {
        // Within the pool prefix, stakes differ by at most 1 (rounding remainder).
        let stakes = distribute_stake(100, 1_000_007, "mainnet-shaped");
        let pool_stakes: Vec<u64> = stakes.iter().copied().filter(|s| *s > 0).collect();
        let min = *pool_stakes.iter().min().unwrap();
        let max = *pool_stakes.iter().max().unwrap();
        assert!(max - min <= 1, "expected near-uniform, got {min}..{max}");
    }

    #[test]
    fn test_latency_range() {
        let config = test_config(5, 3);
        let topo = generate(&config, 5000);
        for edge in &topo.edges {
            assert!(edge.latency_ms >= 10);
            assert!(edge.latency_ms <= 100);
        }
    }

    #[test]
    fn test_deterministic_with_seed() {
        let config = test_config(5, 2);
        let topo1 = generate(&config, 5000);
        let topo2 = generate(&config, 5000);
        assert_eq!(topo1.edges.len(), topo2.edges.len());
        for (e1, e2) in topo1.edges.iter().zip(topo2.edges.iter()) {
            assert_eq!(e1.from, e2.from);
            assert_eq!(e1.to, e2.to);
            assert_eq!(e1.latency_ms, e2.latency_ms);
        }
    }

    #[test]
    fn test_external_peers() {
        let mut config = test_config(5, 2);
        config
            .external_peers
            .push(crate::config::ExternalPeerConfig {
                address: "relay.example.com:3001".to_string(),
                inject_into_nodes: 2,
            });
        let topo = generate(&config, 5000);
        let count = topo
            .nodes
            .iter()
            .filter(|n| {
                n.peers
                    .iter()
                    .any(|p| p.address == "relay.example.com:3001")
            })
            .count();
        assert_eq!(count, 2);
    }

    /// Helper: rebuild adjacency from topology edges.
    fn build_adjacency(topo: &Topology) -> Vec<std::collections::HashSet<usize>> {
        let n = topo.nodes.len();
        let mut adj = vec![std::collections::HashSet::new(); n];
        for edge in &topo.edges {
            adj[edge.from].insert(edge.to);
            adj[edge.to].insert(edge.from);
        }
        adj
    }
}
