use std::{
    collections::{HashSet, VecDeque},
    fmt::Display,
    time::Duration,
};

use anyhow::{anyhow, bail, Result};
use netsim_async::geo::{self, Location};
use num_traits::One as _;
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

#[derive(Debug, Deserialize)]
#[serde(tag = "distribution", rename_all = "kebab-case")]
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

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct RawParameters {
    pub leios_stage_length_slots: u64,
    pub leios_stage_active_voting_slots: u64,

    pub tx_generation_distribution: DistributionConfig,
    pub tx_size_bytes_distribution: DistributionConfig,
    pub tx_validation_cpu_time_ms: f64,
    pub tx_max_size_bytes: u64,

    pub rb_generation_probability: f64,
    pub rb_generation_cpu_time_ms: f64,
    pub rb_head_validation_cpu_time_ms: f64,
    pub rb_head_size_bytes: u64,
    pub rb_body_max_size_bytes: u64,

    pub rb_body_legacy_praos_payload_validation_cpu_time_ms_constant: f64,
    pub rb_body_legacy_praos_payload_validation_cpu_time_ms_per_byte: f64,

    pub ib_generation_probability: f64,
    pub ib_generation_cpu_time_ms: f64,
    pub ib_head_size_bytes: u64,
    pub ib_head_validation_cpu_time_ms: f64,
    pub ib_body_validation_cpu_time_ms_constant: f64,
    pub ib_body_validation_cpu_time_ms_per_byte: f64,
    pub ib_body_max_size_bytes: u64,
    #[serde(default = "u64::one")]
    pub ib_shards: u64,

    pub eb_generation_probability: f64,
    pub eb_generation_cpu_time_ms: f64,
    pub eb_validation_cpu_time_ms: f64,
    pub eb_size_bytes_constant: u64,
    pub eb_size_bytes_per_ib: u64,

    pub vote_generation_probability: f64,
    pub vote_generation_cpu_time_ms_constant: f64,
    pub vote_generation_cpu_time_ms_per_ib: f64,
    pub vote_validation_cpu_time_ms: f64,
    pub vote_threshold: u64,
    pub vote_one_eb_per_vrf_win: bool,
    pub vote_size_bytes_constant: u64,
    pub vote_size_bytes_per_node: u64,

    pub cert_generation_cpu_time_ms_constant: f64,
    pub cert_generation_cpu_time_ms_per_node: f64,
    pub cert_validation_cpu_time_ms_constant: f64,
    pub cert_validation_cpu_time_ms_per_node: f64,
    pub cert_size_bytes_constant: u64,
    pub cert_size_bytes_per_node: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RawTopology {
    pub nodes: Vec<RawNodeConfig>,
    pub links: Vec<RawLinkConfig>,
}

pub struct Topology {
    pub nodes: Vec<NodeConfiguration>,
    pub links: Vec<LinkConfiguration>,
}

impl Topology {
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

impl From<RawTopology> for Topology {
    fn from(value: RawTopology) -> Self {
        let mut nodes: Vec<NodeConfiguration> = value
            .nodes
            .into_iter()
            .enumerate()
            .map(|(index, raw)| NodeConfiguration {
                id: NodeId::new(index),
                location: to_netsim_location(raw.location),
                stake: raw.stake.unwrap_or_default(),
                cpu_multiplier: raw.cpu_multiplier,
                cores: raw.cores,
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
        Self { nodes, links }
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RawNodeConfig {
    pub location: (f64, f64),
    pub stake: Option<u64>,
    pub region: Option<String>,
    #[serde(default = "f64::one", skip_serializing_if = "f64::is_one")]
    pub cpu_multiplier: f64,
    #[serde(default)]
    pub cores: Option<u64>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RawLinkConfig {
    pub nodes: (usize, usize),
    pub latency_ms: Option<u64>,
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
    pub max_ib_size: u64,
    pub max_ib_requests_per_peer: usize,
    pub ib_shards: u64,
    pub one_vote_per_vrf: bool,
    pub tx_validation_cpu_time: Duration,
    pub block_generation_cpu_time: Duration,
    pub block_validation_cpu_time: Duration,
    pub certificate_generation_cpu_time: Duration,
    pub certificate_validation_cpu_time: Duration,
    pub ib_generation_cpu_time: Duration,
    pub ib_validation_cpu_time: Duration,
    pub eb_generation_cpu_time: Duration,
    pub eb_validation_cpu_time: Duration,
    pub vote_generation_cpu_time: Duration,
    pub vote_validation_cpu_time: Duration,
    pub transaction_frequency_ms: FloatDistribution,
    pub transaction_size_bytes: FloatDistribution,
}

impl SimConfiguration {
    pub fn build(params: RawParameters, topology: Topology) -> Self {
        Self {
            seed: 0,
            timescale: 1.0,
            slots: None,
            nodes: topology.nodes,
            trace_nodes: HashSet::new(),
            links: topology.links,
            block_generation_probability: params.rb_generation_probability,
            ib_generation_probability: params.ib_generation_probability,
            eb_generation_probability: params.eb_generation_probability,
            vote_probability: params.vote_generation_probability,
            vote_threshold: params.vote_threshold,
            max_block_size: params.rb_body_max_size_bytes,
            max_tx_size: params.tx_max_size_bytes,
            stage_length: params.leios_stage_length_slots,
            max_ib_size: params.ib_body_max_size_bytes,
            max_ib_requests_per_peer: 1,
            ib_shards: params.ib_shards,
            one_vote_per_vrf: params.vote_one_eb_per_vrf_win,
            tx_validation_cpu_time: duration_ms(params.tx_validation_cpu_time_ms),
            block_generation_cpu_time: duration_ms(params.rb_generation_cpu_time_ms),
            block_validation_cpu_time: duration_ms(
                params.rb_body_legacy_praos_payload_validation_cpu_time_ms_constant,
            ),
            certificate_generation_cpu_time: duration_ms(
                params.cert_generation_cpu_time_ms_constant,
            ),
            certificate_validation_cpu_time: duration_ms(
                params.cert_validation_cpu_time_ms_constant,
            ),
            ib_generation_cpu_time: duration_ms(params.ib_generation_cpu_time_ms),
            ib_validation_cpu_time: duration_ms(params.ib_body_validation_cpu_time_ms_constant),
            eb_generation_cpu_time: duration_ms(params.eb_generation_cpu_time_ms),
            eb_validation_cpu_time: duration_ms(params.eb_validation_cpu_time_ms),
            vote_generation_cpu_time: duration_ms(params.vote_generation_cpu_time_ms_constant),
            vote_validation_cpu_time: duration_ms(params.vote_validation_cpu_time_ms),
            transaction_frequency_ms: params.tx_generation_distribution.into(),
            transaction_size_bytes: params.tx_size_bytes_distribution.into(),
        }
    }
}

fn duration_ms(ms: f64) -> Duration {
    Duration::from_secs_f64(ms / 1000.0)
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
    pub cpu_multiplier: f64,
    pub cores: Option<u64>,
    pub peers: Vec<NodeId>,
}

#[derive(Debug, Clone)]
pub struct LinkConfiguration {
    pub nodes: (NodeId, NodeId),
    pub latency: Duration,
}
