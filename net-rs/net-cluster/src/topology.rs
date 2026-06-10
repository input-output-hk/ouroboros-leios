//! Cluster topology generation.
//!
//! Two sources, selected by [`crate::config::TopologySource`]:
//!
//! - [`generate_random`] — random connected graph (legacy default); honours
//!   `num_nodes` / `degree` / `min_latency_ms` / `max_latency_ms` /
//!   `stake_distribution`.
//! - [`load_from_yaml`] — read a v3/v4-style topology YAML
//!   (`data/simulation/pseudo-mainnet/topology-v4-*.yaml`); honours each
//!   node's `stake` directly and each link's `latency-ms` after clamping
//!   negatives to zero and rounding to whole milliseconds (the inbound
//!   delay model is integer-millisecond).  Geographic placement and
//!   per-link bandwidth in the YAML are accepted-and-ignored.
//!
//! Both paths return the same [`Topology`] shape, which downstream code
//! (overlay generation, port allocation, behaviour assignment) consumes
//! uniformly.

use std::path::Path;

use rand::prelude::*;
use serde::Serialize;

use crate::config::{BehaviourSelection, ClusterConfig};
use crate::raw_topology::{self, RawTopology};

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
    /// Behaviour spec installed at startup, or `None` for honest.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub behaviour: Option<shared_consensus::behaviour::BehaviourSpec>,
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
    /// Sum of `nodes[*].stake` — written into each per-node overlay TOML
    /// as `production.total_stake` so the Praos lottery threshold
    /// (`stake_i / total_stake`) is computed against the cluster's
    /// actual stake total rather than whatever value the base config
    /// happens to carry.
    ///
    /// In random mode this equals the `total_stake` passed to
    /// [`generate_random`] (the random `distribute_stake` is sum-preserving),
    /// so behaviour is unchanged.  In YAML mode this is the sum of the
    /// YAML's per-node `stake` fields, which is critical: a v4 YAML
    /// carries real mainnet ADA values (~1e8 per pool), and if
    /// `total_stake` stays at the base config's synthetic `1000` the
    /// per-node win probability saturates and every node produces a
    /// block every slot.
    pub total_stake: u64,
}

/// Generate a random cluster topology from the given config.
///
/// The `total_stake` parameter comes from the base config and is divided
/// among nodes according to the stake distribution strategy.  Reads the
/// random-mode knobs from `config.topology_random`; the caller selects this
/// path when `config.topology_source` is `Random`.
pub fn generate_random(config: &ClusterConfig, total_stake: u64) -> Topology {
    let crate::config::RandomTopologyConfig {
        num_nodes,
        degree,
        min_latency_ms,
        max_latency_ms,
        stake_distribution,
    } = &config.topology_random;
    let n = *num_nodes;
    let mut rng = match config.seed {
        Some(s) => StdRng::seed_from_u64(s),
        None => StdRng::from_entropy(),
    };

    // Step 1: Build random graph edges.
    let edges = build_random_graph(n, *degree, *min_latency_ms, *max_latency_ms, &mut rng);

    // Step 2: Distribute stake.
    let stakes = distribute_stake(n, total_stake, stake_distribution);

    // Step 3: Build node topologies.
    let behaviour_set = resolve_behaviour_nodes(config, &stakes);
    let mut nodes: Vec<NodeTopology> = (0..n)
        .map(|i| {
            let port = config.base_port + i as u16;
            let behaviour = if config.behaviour.is_some() && behaviour_set.contains(&i) {
                config.behaviour.clone()
            } else {
                None
            };
            NodeTopology {
                index: i,
                node_id: format!("node-{i}"),
                listen_address: format!("127.0.0.1:{port}"),
                listen_port: port,
                stake: stakes[i],
                seed: config.seed.unwrap_or(0) + i as u64,
                behaviour,
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

    // `distribute_stake` is sum-preserving so this equals the input
    // `total_stake`; recomputing keeps the invariant local.
    let cluster_total_stake = nodes.iter().map(|n| n.stake).sum();
    Topology {
        nodes,
        edges,
        total_stake: cluster_total_stake,
    }
}

/// Load a cluster topology from a v3/v4-style YAML file.
///
/// The YAML is parsed into [`RawTopology`] (see [`crate::raw_topology`]) and
/// then converted into the same [`Topology`] shape produced by [`generate_random`].
/// Per-node fields:
///
/// - `node_id`, `index`: synthesised as `node-{i}` over the loaded slice
///   (the YAML's own IDs are *not* reused as host identifiers — see below).
/// - `listen_address`: `127.0.0.1:{base_port + i}` — same scheme as the
///   random path, so every YAML node maps onto a localhost port.
/// - `stake`: read verbatim from the YAML's per-node `stake` field.
/// - `seed`: `config.seed.unwrap_or(0) + i`, matching the random path.
///
/// Per-link fields:
///
/// - `producers` arrays in the YAML become directed `Edge` entries.
///   `link.latency_ms` (f64) is clamped to `>= 0.0` and rounded to the
///   nearest whole millisecond before storing as `u64` — net-core's
///   inbound-delay model is integer-millisecond.  A one-time warning
///   fires if any link has a noticeable fractional component (>0.05 ms)
///   so operators know sub-ms precision is being dropped.
/// - `bandwidth-bytes-per-second` is **accepted-and-ignored** — net-core
///   has no per-peer bandwidth shaping yet.  A one-time warning fires if
///   any link carries a value, so the dropped data isn't silent.
///
/// If `node_limit` is set we take the *first N* nodes in YAML iteration
/// order (the v4 generator emits them stake-rank descending, so this is
/// effectively top-N by stake).  Producer edges pointing at nodes beyond
/// the cutoff are dropped.
pub fn load_from_yaml(
    config: &ClusterConfig,
    path: &Path,
    node_limit: Option<usize>,
) -> Result<Topology, Box<dyn std::error::Error + Send + Sync>> {
    let raw = raw_topology::load_from_path(path)?;
    build_from_raw(config, raw, node_limit)
}

/// Internal worker: convert a `RawTopology` into a cluster `Topology`.
/// Factored out so tests can feed in a parsed YAML without touching disk.
fn build_from_raw(
    config: &ClusterConfig,
    raw: RawTopology,
    node_limit: Option<usize>,
) -> Result<Topology, Box<dyn std::error::Error + Send + Sync>> {
    let limit = node_limit.unwrap_or(usize::MAX);
    let kept_ids: Vec<&String> = raw.nodes.keys().take(limit).collect();
    let kept_count = kept_ids.len();

    // Reject the empty cases up-front.  Two ways to arrive here:
    // 1. YAML has no nodes at all.
    // 2. YAML has nodes but `node_limit = Some(0)` discarded all of them.
    // Either way, downstream (port allocation, overlay generation,
    // num_nodes override in main.rs) would silently produce a 0-node
    // cluster that boots and does nothing — surface it as an error
    // instead.
    if kept_count == 0 {
        return Err(format!(
            "topology YAML produced zero nodes (yaml_nodes={}, node_limit={:?})",
            raw.nodes.len(),
            node_limit,
        )
        .into());
    }

    let id_to_index: std::collections::HashMap<&str, usize> = kept_ids
        .iter()
        .enumerate()
        .map(|(i, id)| (id.as_str(), i))
        .collect();

    // ---- Pass 1: build NodeTopology entries (no peers yet) ----------------
    let stakes: Vec<u64> = kept_ids
        .iter()
        .map(|id| raw.nodes[id.as_str()].stake)
        .collect();
    let behaviour_set = resolve_behaviour_nodes(config, &stakes);

    let mut nodes: Vec<NodeTopology> = (0..kept_count)
        .map(|i| {
            let port = config.base_port + i as u16;
            let behaviour = if config.behaviour.is_some() && behaviour_set.contains(&i) {
                config.behaviour.clone()
            } else {
                None
            };
            NodeTopology {
                index: i,
                node_id: format!("node-{i}"),
                listen_address: format!("127.0.0.1:{port}"),
                listen_port: port,
                stake: stakes[i],
                seed: config.seed.unwrap_or(0) + i as u64,
                behaviour,
                peers: Vec::new(),
            }
        })
        .collect();

    // ---- Pass 2: build edges + peer links from the YAML producers ---------
    // Edges are directed (one direction per `producers` entry) and emitted
    // in **YAML insertion order** — outer loop over `raw.nodes`, inner
    // loop over each node's `producers`.  Both are `IndexMap`s which
    // preserve YAML order, so the resulting `edges` / per-node `peers`
    // vectors are deterministic given the YAML file.  Skipped:
    // - destinations beyond `node_limit`
    // - self-loops (shouldn't appear in well-formed topologies)
    let mut edges: Vec<Edge> = Vec::new();
    let mut frac_latency_warned = false;
    let mut bandwidth_warned = false;
    let mut dropped_targets: u64 = 0;

    for (src_id, raw_node) in raw.nodes.iter().take(kept_count) {
        let &src = id_to_index
            .get(src_id.as_str())
            .expect("src is in kept set");

        for (dst_id, link) in &raw_node.producers {
            let Some(&dst) = id_to_index.get(dst_id.as_str()) else {
                dropped_targets += 1;
                continue; // destination was capped out by node_limit
            };
            if src == dst {
                continue; // skip self-loops
            }

            // Latency: f64 ms in the YAML, u64 ms in net-core.  Round
            // (not truncate) so 45.6 → 46.  Warn once if any link
            // carried a non-trivial fractional component (>0.05 ms), so
            // operators know precision is being dropped.
            let latency_f = link.latency_ms.max(0.0);
            let latency_ms = latency_f.round() as u64;
            if !frac_latency_warned && latency_f.fract().abs() > 0.05 {
                tracing::warn!(
                    yaml_latency = latency_f,
                    rounded = latency_ms,
                    "topology YAML contains fractional latency-ms values; rounding to whole ms (further warnings suppressed)"
                );
                frac_latency_warned = true;
            }

            if link.bandwidth_bytes_per_second.is_some() && !bandwidth_warned {
                tracing::warn!(
                    "topology YAML contains bandwidth-bytes-per-second values; \
                     net-cluster does not currently model per-peer bandwidth and will ignore them"
                );
                bandwidth_warned = true;
            }

            edges.push(Edge {
                from: src,
                to: dst,
                latency_ms,
            });
            let to_addr = nodes[dst].listen_address.clone();
            nodes[src].peers.push(PeerLink {
                address: to_addr,
                inbound_delay_ms: latency_ms,
            });
        }
    }

    if dropped_targets > 0 {
        tracing::info!(
            kept_nodes = kept_count,
            yaml_nodes = raw.nodes.len(),
            dropped_edge_targets = dropped_targets,
            "topology YAML truncated by node_limit; producer edges pointing at dropped nodes were skipped"
        );
    }

    // ---- Pass 3: inject external peers ------------------------------------
    // Same shape as the random path, but the RNG is seeded fresh here:
    // unlike the random path there's no prior `build_random_graph` to
    // advance the RNG, so we derive the YAML-mode seed by offsetting
    // `config.seed` (or falling back to entropy).  Determinism for YAML
    // mode is therefore tied to `config.seed`, not to any graph-gen
    // history.
    let n = nodes.len();
    if !config.external_peers.is_empty() {
        let mut rng = match config.seed {
            Some(s) => StdRng::seed_from_u64(s.wrapping_add(0xEA70_BEEF)),
            None => StdRng::from_entropy(),
        };
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
    }

    // Sum of the loaded per-node stakes — overwrites the base config's
    // `total_stake`.  Critical for YAML mode where the YAML carries real
    // mainnet ADA values; without this each node's `stake / total_stake`
    // ratio explodes and the Praos lottery saturates.
    let total_stake = nodes.iter().map(|n| n.stake).sum();
    Ok(Topology {
        nodes,
        edges,
        total_stake,
    })
}

/// Build a random undirected graph with target degree, ensuring connectivity.
fn build_random_graph(
    n: usize,
    degree: usize,
    min_latency_ms: u64,
    max_latency_ms: u64,
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
            let latency = rng.gen_range(min_latency_ms..=max_latency_ms);
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
                let latency = rng.gen_range(min_latency_ms..=max_latency_ms);
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

/// Resolve the set of node indices that should run the configured
/// per-node behaviour.
///
/// Walks the [`BehaviourSelection`] variant on the cluster config; all
/// stake-aware variants ignore zero-stake nodes (relays under
/// `mainnet-shaped`).  Selections are deterministic for a given seed
/// so re-runs land on the same nodes:
///
/// - [`All`] — every node in the cluster.
/// - [`Nodes`] — verbatim list of indices.
/// - [`StakeRandom`] — `count` random stake-bearing nodes; the RNG is
///   seeded from [`ClusterConfig::seed`] (defaulting to `0` when
///   absent).
/// - [`StakeOrdered`] — first `count` stake-bearing nodes by stake
///   descending, ties broken by index ascending.
/// - [`StakeFraction`] — smallest prefix of stake-bearing nodes whose
///   cumulative stake covers `fraction` of total cluster stake (same
///   prefix discipline as [`StakeOrdered`]).
///
/// `None` (no selection set) returns the empty set even when
/// `behaviour` is `Some` — to attach to every node, use
/// `{ kind = "all" }`.
///
/// [`All`]: BehaviourSelection::All
/// [`Nodes`]: BehaviourSelection::Nodes
/// [`StakeRandom`]: BehaviourSelection::StakeRandom
/// [`StakeOrdered`]: BehaviourSelection::StakeOrdered
/// [`StakeFraction`]: BehaviourSelection::StakeFraction
fn resolve_behaviour_nodes(
    config: &ClusterConfig,
    stakes: &[u64],
) -> std::collections::BTreeSet<usize> {
    use std::collections::BTreeSet;
    let Some(selection) = &config.behaviour_selection else {
        return BTreeSet::new();
    };
    resolve_selection(selection, stakes, config.seed)
}

/// Resolve a [`BehaviourSelection`] to the concrete set of node
/// indices it picks.  Pure helper reused at startup (via
/// [`resolve_behaviour_nodes`]) and at runtime (when the cluster
/// orchestrator translates a `POST /api/attack` request to per-node
/// stdin writes).
pub fn resolve_selection(
    selection: &BehaviourSelection,
    stakes: &[u64],
    seed: Option<u64>,
) -> std::collections::BTreeSet<usize> {
    use std::collections::BTreeSet;
    match selection {
        BehaviourSelection::All => (0..stakes.len()).collect(),
        BehaviourSelection::Nodes { indices } => indices
            .iter()
            .copied()
            .filter(|&i| i < stakes.len())
            .collect(),
        BehaviourSelection::StakeOrdered { count } => {
            stake_ranked(stakes).into_iter().take(*count).collect()
        }
        BehaviourSelection::StakeRandom { count } => {
            let mut bearers: Vec<usize> = stakes
                .iter()
                .enumerate()
                .filter(|(_, &s)| s > 0)
                .map(|(i, _)| i)
                .collect();
            let mut rng = StdRng::seed_from_u64(seed.unwrap_or(0));
            bearers.shuffle(&mut rng);
            bearers.into_iter().take(*count).collect()
        }
        BehaviourSelection::StakeFraction { fraction } => {
            let total: u128 = stakes.iter().map(|&s| s as u128).sum();
            if total == 0 {
                return BTreeSet::new();
            }
            let f = fraction.clamp(0.0, 1.0);
            let target = (total as f64 * f).ceil() as u128;
            let mut chosen = BTreeSet::new();
            let mut acc: u128 = 0;
            for (idx, stake) in stake_ranked_with_stake(stakes) {
                if acc >= target {
                    break;
                }
                chosen.insert(idx);
                acc += stake as u128;
            }
            chosen
        }
    }
}

/// Stake-bearing nodes sorted by stake descending, ties broken by
/// index ascending.  Returns indices only; pair with
/// [`stake_ranked_with_stake`] when you also need the stake.
fn stake_ranked(stakes: &[u64]) -> Vec<usize> {
    stake_ranked_with_stake(stakes)
        .into_iter()
        .map(|(i, _)| i)
        .collect()
}

fn stake_ranked_with_stake(stakes: &[u64]) -> Vec<(usize, u64)> {
    let mut ranked: Vec<(usize, u64)> = stakes
        .iter()
        .enumerate()
        .filter(|(_, &s)| s > 0)
        .map(|(i, &s)| (i, s))
        .collect();
    ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    ranked
}

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
            topology_source: crate::config::TopologySource::Random,
            topology_random: crate::config::RandomTopologyConfig {
                num_nodes,
                degree,
                min_latency_ms: 10,
                max_latency_ms: 100,
                stake_distribution: "equal".to_string(),
            },
            base_config: "test.toml".to_string(),
            base_port: 30000,
            seed: Some(42),
            ..ClusterConfig::default()
        }
    }

    #[test]
    fn test_single_node() {
        let config = test_config(1, 0);
        let topo = generate_random(&config, 1000);
        assert_eq!(topo.nodes.len(), 1);
        assert!(topo.edges.is_empty());
        assert_eq!(topo.nodes[0].stake, 1000);
    }

    #[test]
    fn test_two_nodes() {
        let config = test_config(2, 1);
        let topo = generate_random(&config, 1000);
        assert_eq!(topo.nodes.len(), 2);
        assert!(!topo.edges.is_empty());
        // Directional: only the `from` node has a peer link.
        let total_peers: usize = topo.nodes.iter().map(|n| n.peers.len()).sum();
        assert_eq!(total_peers, topo.edges.len());
    }

    #[test]
    fn test_connectivity() {
        let config = test_config(10, 2);
        let topo = generate_random(&config, 10000);

        // Verify connectivity via BFS from node 0.
        let adj = build_adjacency(&topo);
        let components = find_components(10, &adj);
        assert_eq!(components.len(), 1, "graph should be connected");
    }

    #[test]
    fn test_port_allocation() {
        let config = test_config(5, 2);
        let topo = generate_random(&config, 5000);
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

    // -- resolve_behaviour_nodes ----------------------------------------------

    fn cfg_with_selection(selection: BehaviourSelection) -> ClusterConfig {
        ClusterConfig {
            behaviour_selection: Some(selection),
            ..ClusterConfig::default()
        }
    }

    #[test]
    fn resolve_none_returns_empty() {
        let cfg = ClusterConfig::default();
        let set = resolve_behaviour_nodes(&cfg, &[1, 1, 1]);
        assert!(set.is_empty());
    }

    #[test]
    fn resolve_all_picks_every_node() {
        let cfg = cfg_with_selection(BehaviourSelection::All);
        let set = resolve_behaviour_nodes(&cfg, &[0, 5, 0, 5, 0]);
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn resolve_nodes_verbatim() {
        let cfg = cfg_with_selection(BehaviourSelection::Nodes {
            indices: vec![1, 3],
        });
        let set = resolve_behaviour_nodes(&cfg, &[1, 1, 1, 1]);
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![1, 3]);
    }

    #[test]
    fn resolve_stake_ordered_filters_zero_stake_and_takes_top_n() {
        let cfg = cfg_with_selection(BehaviourSelection::StakeOrdered { count: 2 });
        let stakes = vec![10, 100, 50, 0, 200];
        let set = resolve_behaviour_nodes(&cfg, &stakes);
        // Sorted desc by stake: 4 (200), 1 (100), 2 (50), 0 (10); top 2 = {1, 4}.
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![1, 4]);
    }

    #[test]
    fn resolve_stake_ordered_count_zero_returns_empty() {
        let cfg = cfg_with_selection(BehaviourSelection::StakeOrdered { count: 0 });
        let set = resolve_behaviour_nodes(&cfg, &[10, 10, 10]);
        assert!(set.is_empty());
    }

    #[test]
    fn resolve_stake_ordered_count_exceeds_pool_takes_all_bearers() {
        let cfg = cfg_with_selection(BehaviourSelection::StakeOrdered { count: 99 });
        let stakes = vec![10, 0, 20, 0, 30];
        let set = resolve_behaviour_nodes(&cfg, &stakes);
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0, 2, 4]);
    }

    #[test]
    fn resolve_stake_random_is_deterministic_for_seed() {
        let stakes = vec![10, 0, 20, 0, 30, 0, 40, 0, 50];
        let mk = |seed: u64| -> std::collections::BTreeSet<usize> {
            let cfg = ClusterConfig {
                seed: Some(seed),
                behaviour_selection: Some(BehaviourSelection::StakeRandom { count: 2 }),
                ..ClusterConfig::default()
            };
            resolve_behaviour_nodes(&cfg, &stakes)
        };
        // Re-runs with the same seed produce the same set.
        assert_eq!(mk(42), mk(42));
        // Distinct seeds usually produce distinct sets (no determinism
        // requirement, but at least demonstrate the seed matters).
        let a = mk(42);
        let b = mk(43);
        assert_ne!(a, b, "seed should change the selection");
        // Returned set is always a subset of stake-bearers and never
        // includes zero-stake indices.
        let bearers: std::collections::BTreeSet<usize> = [0, 2, 4, 6, 8].into_iter().collect();
        for node in &a {
            assert!(bearers.contains(node));
        }
    }

    #[test]
    fn resolve_stake_random_count_zero_returns_empty() {
        let cfg = cfg_with_selection(BehaviourSelection::StakeRandom { count: 0 });
        let set = resolve_behaviour_nodes(&cfg, &[10, 20, 30]);
        assert!(set.is_empty());
    }

    #[test]
    fn resolve_stake_fraction_picks_smallest_prefix_covering_target() {
        // 5 pools, equal stake.  fraction 0.4 → need 40% = 2 pools.
        let cfg = cfg_with_selection(BehaviourSelection::StakeFraction { fraction: 0.4 });
        let stakes = vec![100, 100, 100, 100, 100];
        let set = resolve_behaviour_nodes(&cfg, &stakes);
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0, 1]);
    }

    #[test]
    fn resolve_stake_fraction_with_uneven_pools() {
        // Stakes [10, 100, 50, 200] sorted desc: 200, 100, 50, 10 (indices 3, 1, 2, 0).
        // Total = 360.  fraction 0.5 → target 180.
        // After 200 alone (index 3) we already exceed 180 → stop.
        let cfg = cfg_with_selection(BehaviourSelection::StakeFraction { fraction: 0.5 });
        let stakes = vec![10, 100, 50, 200];
        let set = resolve_behaviour_nodes(&cfg, &stakes);
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![3]);
    }

    #[test]
    fn resolve_stake_fraction_skips_relays() {
        // mainnet-shaped: pools at low indices, zero-stake relays elsewhere.
        let cfg = cfg_with_selection(BehaviourSelection::StakeFraction { fraction: 0.3 });
        let stakes = vec![100, 100, 100, 0, 0, 0, 0];
        let set = resolve_behaviour_nodes(&cfg, &stakes);
        // total 300, target 90 → one pool (100) covers it.
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0]);
    }

    #[test]
    fn resolve_stake_fraction_zero_returns_empty() {
        let cfg = cfg_with_selection(BehaviourSelection::StakeFraction { fraction: 0.0 });
        let set = resolve_behaviour_nodes(&cfg, &[100, 100]);
        assert!(set.is_empty());
    }

    #[test]
    fn resolve_stake_fraction_one_picks_all_bearers() {
        let cfg = cfg_with_selection(BehaviourSelection::StakeFraction { fraction: 1.0 });
        let stakes = vec![10, 0, 20, 0, 30];
        let set = resolve_behaviour_nodes(&cfg, &stakes);
        assert_eq!(set.iter().copied().collect::<Vec<_>>(), vec![0, 2, 4]);
    }

    #[test]
    fn test_latency_range() {
        let config = test_config(5, 3);
        let topo = generate_random(&config, 5000);
        for edge in &topo.edges {
            assert!(edge.latency_ms >= 10);
            assert!(edge.latency_ms <= 100);
        }
    }

    #[test]
    fn test_deterministic_with_seed() {
        let config = test_config(5, 2);
        let topo1 = generate_random(&config, 5000);
        let topo2 = generate_random(&config, 5000);
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
        let topo = generate_random(&config, 5000);
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

    // --- YAML-loaded topology --------------------------------------------------

    /// Small hand-written v4-style YAML fixture: 4 nodes, mixed stakes,
    /// asymmetric producer edges, one self-loop (which must be skipped),
    /// one fractional latency, one explicit bandwidth value.
    const YAML_FIXTURE: &str = r#"
nodes:
  node-0:
    stake: 1000
    location: [10.0, 49.7]
    producers:
      node-1:
        latency-ms: 45.3
        bandwidth-bytes-per-second: 125000000
      node-2:
        latency-ms: 12.0
      node-3:
        latency-ms: 200.0
      node-0:                   # self-loop (must be skipped)
        latency-ms: 0.0
  node-1:
    stake: 500
    location: [-77.5, 38.9]
    producers:
      node-0:
        latency-ms: 45.6        # rounds to 46
      node-2:
        latency-ms: 50.0
  node-2:
    stake: 0
    location: [120.0, 30.0]
    producers:
      node-0:
        latency-ms: 12.0
  node-3:
    stake: 250
    location: [-3.0, 51.5]
    producers: {}
"#;

    fn yaml_test_config() -> ClusterConfig {
        // Note: when YAML mode is exercised through `build_from_raw` we
        // don't actually need to set `topology_source = "yaml"` — the
        // builder doesn't read it — but we keep the default Random here
        // so the rest of the ClusterConfig stays valid.
        ClusterConfig {
            base_config: "test.toml".to_string(),
            base_port: 31000,
            seed: Some(7),
            ..ClusterConfig::default()
        }
    }

    fn parse_yaml_fixture() -> crate::raw_topology::RawTopology {
        serde_yaml::from_str(YAML_FIXTURE).unwrap()
    }

    #[test]
    fn yaml_basic_shape() {
        let config = yaml_test_config();
        let raw = parse_yaml_fixture();
        let topo = build_from_raw(&config, raw, None).unwrap();

        // 4 nodes loaded; ports allocated linearly from base_port.
        assert_eq!(topo.nodes.len(), 4);
        for (i, n) in topo.nodes.iter().enumerate() {
            assert_eq!(n.index, i);
            assert_eq!(n.node_id, format!("node-{i}"));
            assert_eq!(n.listen_port, 31000 + i as u16);
            assert_eq!(n.listen_address, format!("127.0.0.1:{}", 31000 + i as u16));
        }

        // Stakes flow through verbatim.
        assert_eq!(topo.nodes[0].stake, 1000);
        assert_eq!(topo.nodes[1].stake, 500);
        assert_eq!(topo.nodes[2].stake, 0);
        assert_eq!(topo.nodes[3].stake, 250);

        // Edges: 3 from node-0 (self-loop skipped) + 2 from node-1 + 1 from
        // node-2 + 0 from node-3 = 6 total.
        assert_eq!(topo.edges.len(), 6);

        // Self-loop must not appear.
        assert!(topo.edges.iter().all(|e| e.from != e.to));
    }

    #[test]
    fn yaml_latency_rounds_to_whole_ms() {
        let config = yaml_test_config();
        let raw = parse_yaml_fixture();
        let topo = build_from_raw(&config, raw, None).unwrap();

        // 45.3 → 45, 12.0 → 12, 200.0 → 200, 45.6 → 46.
        let n1_link = topo
            .edges
            .iter()
            .find(|e| e.from == 0 && e.to == 1)
            .unwrap();
        assert_eq!(n1_link.latency_ms, 45);
        let back_link = topo
            .edges
            .iter()
            .find(|e| e.from == 1 && e.to == 0)
            .unwrap();
        assert_eq!(back_link.latency_ms, 46);

        // PeerLink.inbound_delay_ms mirrors the edge latency.
        let pl = topo.nodes[0]
            .peers
            .iter()
            .find(|p| p.address.ends_with(":31001"))
            .unwrap();
        assert_eq!(pl.inbound_delay_ms, 45);
    }

    #[test]
    fn yaml_node_limit_truncates_and_drops_external_edges() {
        let config = yaml_test_config();
        let raw = parse_yaml_fixture();
        let topo = build_from_raw(&config, raw, Some(2)).unwrap();

        // Only the first two YAML nodes survive.
        assert_eq!(topo.nodes.len(), 2);
        // Edges from node-0 that pointed at node-2 / node-3 are dropped;
        // only the node-0 → node-1 edge remains.  Plus node-1 → node-0.
        assert_eq!(topo.edges.len(), 2);
        let pairs: Vec<_> = topo.edges.iter().map(|e| (e.from, e.to)).collect();
        assert!(pairs.contains(&(0, 1)));
        assert!(pairs.contains(&(1, 0)));
    }

    #[test]
    fn yaml_empty_topology_is_rejected() {
        // Empty `nodes:` map → no nodes to load → error.
        let config = yaml_test_config();
        let raw: crate::raw_topology::RawTopology = serde_yaml::from_str("nodes: {}\n").unwrap();
        let err = build_from_raw(&config, raw, None).unwrap_err();
        assert!(
            err.to_string().contains("zero nodes"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn yaml_node_limit_zero_is_rejected() {
        // Non-empty YAML but `node_limit = Some(0)` discards everything.
        // Previously this silently produced an empty `Topology`, which
        // then propagated as `num_nodes = 0` through main.rs and the
        // cluster booted with no children.  Must be a hard error.
        let config = yaml_test_config();
        let raw = parse_yaml_fixture();
        let err = build_from_raw(&config, raw, Some(0)).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("zero nodes"), "unexpected error: {msg}");
        assert!(
            msg.contains("node_limit=Some(0)") || msg.contains("Some(0)"),
            "error should mention the node_limit value, got: {msg}"
        );
    }

    #[test]
    fn yaml_external_peers_still_injected() {
        let mut config = yaml_test_config();
        config
            .external_peers
            .push(crate::config::ExternalPeerConfig {
                address: "relay.example.com:3001".to_string(),
                inject_into_nodes: 2,
            });
        let raw = parse_yaml_fixture();
        let topo = build_from_raw(&config, raw, None).unwrap();
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

    #[test]
    fn yaml_load_is_deterministic_for_same_seed() {
        let config = yaml_test_config();
        let raw1 = parse_yaml_fixture();
        let raw2 = parse_yaml_fixture();
        let topo1 = build_from_raw(&config, raw1, None).unwrap();
        let topo2 = build_from_raw(&config, raw2, None).unwrap();
        assert_eq!(topo1.edges.len(), topo2.edges.len());
        for (e1, e2) in topo1.edges.iter().zip(topo2.edges.iter()) {
            assert_eq!(e1.from, e2.from);
            assert_eq!(e1.to, e2.to);
            assert_eq!(e1.latency_ms, e2.latency_ms);
        }
    }

    #[test]
    fn yaml_behaviour_selection_honoured() {
        // StakeOrdered{count=2} should attach to nodes 0 and 1 (the two
        // highest stakes among the four in YAML_FIXTURE: 1000 > 500 > 250 > 0).
        let mut config = yaml_test_config();
        config.behaviour = Some(shared_consensus::behaviour::BehaviourSpec::Honest);
        config.behaviour_selection =
            Some(crate::config::BehaviourSelection::StakeOrdered { count: 2 });
        let raw = parse_yaml_fixture();
        let topo = build_from_raw(&config, raw, None).unwrap();
        assert!(topo.nodes[0].behaviour.is_some());
        assert!(topo.nodes[1].behaviour.is_some());
        assert!(topo.nodes[2].behaviour.is_none()); // stake = 0, not eligible
        assert!(topo.nodes[3].behaviour.is_none()); // stake = 250, but count=2
    }

    /// Regression test: when the YAML uses numeric IDs (`node-0`, `node-1`,
    /// …, `node-12`) in stake-rank-descending order, `node_limit = 3` must
    /// keep `node-0`, `node-1`, `node-2` (the three highest stakes) — not
    /// some lexicographic mix like `node-0`, `node-1`, `node-10`.
    ///
    /// This is what would have caught the `BTreeMap` ordering bug — the
    /// hand-written A/B/C fixture above happens to iterate identically
    /// in any ordered map.
    #[test]
    fn yaml_numeric_ids_node_limit_takes_top_by_yaml_order() {
        // 12 nodes, stakes 12000, 11000, …, 1000 in YAML order.
        let yaml = {
            let mut s = String::from("nodes:\n");
            for i in 0..12 {
                s.push_str(&format!(
                    "  node-{i}:\n    stake: {}\n    producers: {{}}\n",
                    12_000 - i * 1_000
                ));
            }
            s
        };
        let raw: crate::raw_topology::RawTopology = serde_yaml::from_str(&yaml).unwrap();

        let config = ClusterConfig {
            base_config: "test.toml".to_string(),
            base_port: 32000,
            seed: Some(7),
            ..ClusterConfig::default()
        };
        let topo = build_from_raw(&config, raw, Some(3)).unwrap();

        // Three nodes, stakes 12000, 11000, 10000 — the top three in YAML
        // order.  Lexicographic order would give 12000, 11000, 2000 (from
        // node-0, node-1, node-10).
        assert_eq!(topo.nodes.len(), 3);
        let stakes: Vec<u64> = topo.nodes.iter().map(|n| n.stake).collect();
        assert_eq!(stakes, vec![12_000, 11_000, 10_000]);
    }

    #[test]
    fn yaml_total_stake_is_sum_of_loaded_stakes() {
        // YAML mode must compute `total_stake` from the actual loaded
        // nodes — not inherit the base config's value — so the Praos
        // lottery ratio is sane.  The fixture has stakes 1000+500+0+250
        // = 1750.
        let config = yaml_test_config();
        let raw = parse_yaml_fixture();
        let topo = build_from_raw(&config, raw, None).unwrap();
        assert_eq!(topo.total_stake, 1750);
    }

    #[test]
    fn yaml_total_stake_respects_node_limit() {
        // With node_limit = 2, only the first two YAML nodes count
        // toward total_stake.  Fixture: node-A (1000) + node-B (700).
        // Wait — yaml_test_config uses the fixture with stakes
        // 1000/500/0/250.  node_limit = 2 → 1000 + 500 = 1500.
        let config = yaml_test_config();
        let raw = parse_yaml_fixture();
        let topo = build_from_raw(&config, raw, Some(2)).unwrap();
        assert_eq!(topo.total_stake, 1500);
    }

    #[test]
    fn random_topology_total_stake_equals_input() {
        // Sanity check for the random path: distribute_stake is
        // sum-preserving, so Topology.total_stake should equal the
        // input total_stake.
        let config = test_config(5, 2);
        let topo = generate_random(&config, 12_345);
        assert_eq!(topo.total_stake, 12_345);
    }

    #[test]
    fn yaml_load_from_path_round_trip() {
        // End-to-end: write the fixture to a temp file and load via the
        // public entry point.
        let tmp = tempfile::tempdir().unwrap();
        let path = tmp.path().join("topology.yaml");
        std::fs::write(&path, YAML_FIXTURE).unwrap();
        let config = yaml_test_config();
        let topo = load_from_yaml(&config, &path, None).unwrap();
        assert_eq!(topo.nodes.len(), 4);
        assert_eq!(topo.edges.len(), 6);
    }
}
