use std::{
    collections::{HashSet, VecDeque},
    fmt::Display,
    time::Duration,
};

use anyhow::{anyhow, bail, Result};
use netsim_async::geo::{self, Location};
use serde::{Deserialize, Serialize};

use crate::probability::FloatDistribution;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NodeId(usize);
impl Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl NodeId {
    pub fn to_inner(self) -> usize {
        self.0
    }
    pub fn new(value: usize) -> Self {
        Self(value)
    }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "distribution", rename_all = "snake_case")]
pub enum DistributionConfig {
    Normal { mean: f64, std_dev: f64 },
    Exp { lambda: f64, scale: Option<f64> },
    LogNormal { mu: f64, sigma: f64 },
}
impl From<DistributionConfig> for FloatDistribution {
    fn from(value: DistributionConfig) -> Self {
        match value {
            DistributionConfig::Normal { mean, std_dev } => {
                FloatDistribution::normal(mean, std_dev)
            }
            DistributionConfig::Exp { lambda, scale } => {
                FloatDistribution::scaled_exp(lambda, scale.unwrap_or(1.))
            }
            DistributionConfig::LogNormal { mu, sigma } => FloatDistribution::log_normal(mu, sigma),
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RawConfig {
    pub seed: Option<u64>,
    pub timescale: Option<f64>,
    pub slots: Option<u64>,
    #[serde(default, skip_serializing_if = "HashSet::is_empty")]
    pub trace_nodes: HashSet<NodeId>,
    pub nodes: Vec<RawNodeConfig>,
    pub links: Vec<RawLinkConfig>,
    pub block_generation_probability: f64,
    pub ib_generation_probability: f64,
    pub eb_generation_probability: f64,
    pub vote_probability: f64,
    pub vote_threshold: u64,
    pub max_block_size: u64,
    pub max_tx_size: u64,
    pub stage_length: u64,
    pub deliver_stage_count: u64,
    pub uniform_ib_generation: bool,
    pub max_ib_size: u64,
    pub max_ib_requests_per_peer: usize,
    pub ib_shards: u64,
    pub one_vote_per_vrf: bool,
    pub transaction_frequency_ms: DistributionConfig,
    pub transaction_size_bytes: DistributionConfig,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RawNodeConfig {
    pub location: (f64, f64),
    pub stake: Option<u64>,
    pub region: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RawLinkConfig {
    pub nodes: (usize, usize),
    pub latency_ms: Option<u64>,
}

impl From<RawConfig> for SimConfiguration {
    fn from(value: RawConfig) -> Self {
        let timescale = value.timescale.unwrap_or(1.0);
        let mut nodes: Vec<NodeConfiguration> = value
            .nodes
            .into_iter()
            .enumerate()
            .map(|(index, raw)| NodeConfiguration {
                id: NodeId::new(index),
                location: to_netsim_location(raw.location),
                stake: raw.stake.unwrap_or_default(),
                peers: vec![],
            })
            .collect();
        let mut links = vec![];
        for link in value.links {
            let (id1, id2) = link.nodes;
            nodes[id1].peers.push(NodeId::new(id2));
            nodes[id2].peers.push(NodeId::new(id1));
            links.push(LinkConfiguration {
                nodes: (NodeId::new(id1), NodeId::new(id2)),
                latency: compute_latency(nodes[id1].location, nodes[id2].location, link.latency_ms),
            });
        }
        Self {
            seed: value.seed.unwrap_or_default(),
            timescale,
            slots: value.slots,
            nodes,
            trace_nodes: value.trace_nodes,
            links,
            block_generation_probability: value.block_generation_probability,
            ib_generation_probability: value.ib_generation_probability,
            eb_generation_probability: value.eb_generation_probability,
            vote_probability: value.vote_probability,
            vote_threshold: value.vote_threshold,
            max_block_size: value.max_block_size,
            max_tx_size: value.max_tx_size,
            stage_length: value.stage_length,
            deliver_stage_count: value.deliver_stage_count,
            uniform_ib_generation: value.uniform_ib_generation,
            max_ib_size: value.max_ib_size,
            max_ib_requests_per_peer: value.max_ib_requests_per_peer,
            ib_shards: value.ib_shards,
            one_vote_per_vrf: value.one_vote_per_vrf,
            transaction_frequency_ms: value.transaction_frequency_ms.into(),
            transaction_size_bytes: value.transaction_size_bytes.into(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SimConfiguration {
    pub seed: u64,
    pub slots: Option<u64>,
    pub timescale: f64,
    pub trace_nodes: HashSet<NodeId>,
    pub nodes: Vec<NodeConfiguration>,
    pub links: Vec<LinkConfiguration>,
    pub block_generation_probability: f64,
    pub ib_generation_probability: f64,
    pub eb_generation_probability: f64,
    pub vote_probability: f64,
    pub vote_threshold: u64,
    pub max_block_size: u64,
    pub max_tx_size: u64,
    pub stage_length: u64,
    pub deliver_stage_count: u64,
    pub uniform_ib_generation: bool,
    pub max_ib_size: u64,
    pub max_ib_requests_per_peer: usize,
    pub ib_shards: u64,
    pub one_vote_per_vrf: bool,
    pub transaction_frequency_ms: FloatDistribution,
    pub transaction_size_bytes: FloatDistribution,
}

impl SimConfiguration {
    pub fn validate(&self) -> Result<()> {
        // The graph must be nonempty and fully connected,
        // and every link must be between two nodes which exist
        let mut connected_nodes = HashSet::new();
        let mut self_connected_nodes = vec![];
        let mut frontier = VecDeque::new();
        let first_node = self
            .nodes
            .first()
            .ok_or_else(|| anyhow!("Graph must not be empty!"))?;
        frontier.push_back(first_node);
        while let Some(node) = frontier.pop_front() {
            if connected_nodes.insert(node.id) {
                for peer_id in &node.peers {
                    if node.id == *peer_id {
                        self_connected_nodes.push(node.id);
                    }
                    let peer = self
                        .nodes
                        .get(peer_id.0)
                        .ok_or_else(|| anyhow!("Node {peer_id} not found!"))?;
                    frontier.push_back(peer);
                }
            }
        }
        if !self_connected_nodes.is_empty() {
            bail!(
                "{} node(s) are connected to themselves!",
                self_connected_nodes.len()
            );
        }
        if connected_nodes.len() < self.nodes.len() {
            bail!("Graph must be fully connected!");
        }
        Ok(())
    }
}

fn to_netsim_location((lat, long): (f64, f64)) -> Location {
    ((lat * 10000.) as i64, (long * 10000.) as u64)
}

fn compute_latency(loc1: Location, loc2: Location, explicit: Option<u64>) -> Duration {
    if let Some(ms) = explicit {
        return Duration::from_millis(ms);
    }
    let geo_latency = geo::latency_between_locations(loc1, loc2, 1.)
        .map(|l| l.to_duration())
        .unwrap_or(Duration::ZERO);
    let extra_latency = Duration::from_millis(5);
    geo_latency + extra_latency
}

#[derive(Debug, Clone)]
pub struct NodeConfiguration {
    pub id: NodeId,
    pub location: Location,
    pub stake: u64,
    pub peers: Vec<NodeId>,
}

#[derive(Debug, Clone)]
pub struct LinkConfiguration {
    pub nodes: (NodeId, NodeId),
    pub latency: Duration,
}
