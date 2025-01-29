use std::{
    collections::{BTreeMap, HashSet, VecDeque},
    fmt::Display,
    time::Duration,
};

use anyhow::{anyhow, bail, Result};
use num_traits::One as _;
use serde::{Deserialize, Serialize};

use crate::probability::FloatDistribution;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
    // Leios protocol configuration
    pub leios_stage_length_slots: u64,
    pub leios_stage_active_voting_slots: u64,

    // Transaction configuration
    pub tx_generation_distribution: DistributionConfig,
    pub tx_size_bytes_distribution: DistributionConfig,
    pub tx_validation_cpu_time_ms: f64,
    pub tx_max_size_bytes: u64,

    // Ranking block configuration
    pub rb_generation_probability: f64,
    pub rb_generation_cpu_time_ms: f64,
    pub rb_head_validation_cpu_time_ms: f64,
    // pub rb_head_size_bytes: u64,
    pub rb_body_max_size_bytes: u64,

    pub rb_body_legacy_praos_payload_validation_cpu_time_ms_constant: f64,
    pub rb_body_legacy_praos_payload_validation_cpu_time_ms_per_byte: f64,

    // Input block configuration
    pub ib_generation_probability: f64,
    pub ib_generation_cpu_time_ms: f64,
    // pub ib_head_size_bytes: u64,
    pub ib_head_validation_cpu_time_ms: f64,
    pub ib_body_validation_cpu_time_ms_constant: f64,
    pub ib_body_validation_cpu_time_ms_per_byte: f64,
    pub ib_body_max_size_bytes: u64,
    #[serde(default = "u64::one")]
    pub ib_shards: u64,

    // Endorsement block configuration
    pub eb_generation_probability: f64,
    pub eb_generation_cpu_time_ms: f64,
    pub eb_validation_cpu_time_ms: f64,
    // pub eb_size_bytes_constant: u64,
    // pub eb_size_bytes_per_ib: u64,

    // Vote configuration
    pub vote_generation_probability: f64,
    pub vote_generation_cpu_time_ms_constant: f64,
    pub vote_generation_cpu_time_ms_per_ib: f64,
    pub vote_validation_cpu_time_ms: f64,
    pub vote_threshold: u64,
    // pub vote_size_bytes_constant: u64,
    // pub vote_size_bytes_per_node: u64,

    // Certificate configuration
    pub cert_generation_cpu_time_ms_constant: f64,
    pub cert_generation_cpu_time_ms_per_node: f64,
    pub cert_validation_cpu_time_ms_constant: f64,
    pub cert_validation_cpu_time_ms_per_node: f64,
    // pub cert_size_bytes_constant: u64,
    // pub cert_size_bytes_per_node: u64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RawLegacyTopology {
    pub nodes: Vec<RawNodeConfig>,
    pub links: Vec<RawLinkConfig>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct RawTopology {
    pub nodes: BTreeMap<String, RawNode>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct RawNode {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stake: Option<u64>,
    pub location: RawNodeLocation,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cpu_core_count: Option<u64>,
    pub producers: BTreeMap<String, RawLinkInfo>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case", untagged)]
pub enum RawNodeLocation {
    Cluster { cluster: String },
    Coords((f64, f64)),
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct RawLinkInfo {
    pub latency_ms: f64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub bandwidth_bytes_per_second: Option<u64>,
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
                for peer_id in &node.consumers {
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

impl From<RawLegacyTopology> for Topology {
    fn from(value: RawLegacyTopology) -> Self {
        let mut nodes: Vec<NodeConfiguration> = value
            .nodes
            .into_iter()
            .enumerate()
            .map(|(index, raw)| NodeConfiguration {
                id: NodeId::new(index),
                name: format!("node-{index}"),
                stake: raw.stake.unwrap_or_default(),
                cpu_multiplier: raw.cpu_multiplier,
                cores: raw.cores,
                consumers: vec![],
            })
            .collect();
        let mut links = vec![];
        for link in value.links {
            let (id1, id2) = link.nodes;
            nodes[id1].consumers.push(NodeId::new(id2));
            nodes[id2].consumers.push(NodeId::new(id1));
            links.push(LinkConfiguration {
                nodes: (NodeId::new(id1), NodeId::new(id2)),
                latency: Duration::from_millis(link.latency_ms),
            });
        }
        Self { nodes, links }
    }
}

impl From<RawTopology> for Topology {
    fn from(value: RawTopology) -> Self {
        let mut node_ids = BTreeMap::new();
        let mut nodes = BTreeMap::new();
        for (index, (name, node)) in value.nodes.iter().enumerate() {
            let id = NodeId::new(index);
            node_ids.insert(name.clone(), id);
            nodes.insert(
                id,
                NodeConfiguration {
                    id,
                    name: name.clone(),
                    stake: node.stake.unwrap_or_default(),
                    cpu_multiplier: 1.0,
                    cores: node.cpu_core_count,
                    consumers: vec![],
                },
            );
        }
        let mut links = BTreeMap::new();
        for (consumer_name, raw_node) in value.nodes.into_iter() {
            let consumer_id = *node_ids.get(&consumer_name).unwrap();

            for (producer_name, producer_info) in raw_node.producers {
                let producer_id = *node_ids.get(&producer_name).unwrap();
                nodes
                    .get_mut(&producer_id)
                    .unwrap()
                    .consumers
                    .push(consumer_id);
                let mut ids = [consumer_id, producer_id];
                ids.sort();
                links.insert(
                    ids,
                    LinkConfiguration {
                        nodes: (ids[0], ids[1]),
                        latency: duration_ms(producer_info.latency_ms),
                    },
                );
            }
        }
        let links = links.into_values().collect();
        Self {
            nodes: nodes.into_values().collect(),
            links,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RawNodeConfig {
    pub location: (f64, f64),
    pub stake: Option<u64>,
    pub region: Option<String>,
    #[serde(default = "f64::one", skip_serializing_if = "f64::is_one")]
    pub cpu_multiplier: f64,
    #[serde(default)]
    pub cores: Option<u64>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RawLinkConfig {
    pub nodes: (usize, usize),
    pub latency_ms: u64,
}

#[derive(Debug, Clone)]
pub(crate) struct CpuTimeConfig {
    pub tx_validation: Duration,
    pub rb_generation: Duration,
    pub rb_validation_constant: Duration,
    pub rb_validation_per_byte: Duration,
    pub ib_generation: Duration,
    pub ib_head_validation: Duration,
    pub ib_body_validation_constant: Duration,
    pub ib_body_validation_per_byte: Duration,
    pub eb_generation: Duration,
    pub eb_validation: Duration,
    pub vote_generation_constant: Duration,
    pub vote_generation_per_ib: Duration,
    pub vote_validation: Duration,
    pub cert_generation_constant: Duration,
    pub cert_generation_per_node: Duration,
    pub cert_validation_constant: Duration,
    pub cert_validation_per_node: Duration,
}
impl CpuTimeConfig {
    fn new(params: &RawParameters) -> Self {
        Self {
            tx_validation: duration_ms(params.tx_validation_cpu_time_ms),
            rb_generation: duration_ms(params.rb_generation_cpu_time_ms),
            rb_validation_constant: duration_ms(
                params.rb_head_validation_cpu_time_ms
                    + params.rb_body_legacy_praos_payload_validation_cpu_time_ms_constant,
            ),
            rb_validation_per_byte: duration_ms(
                params.rb_body_legacy_praos_payload_validation_cpu_time_ms_per_byte,
            ),
            ib_generation: duration_ms(params.ib_generation_cpu_time_ms),
            ib_head_validation: duration_ms(params.ib_head_validation_cpu_time_ms),
            ib_body_validation_constant: duration_ms(
                params.ib_body_validation_cpu_time_ms_constant,
            ),
            ib_body_validation_per_byte: duration_ms(
                params.ib_body_validation_cpu_time_ms_per_byte,
            ),
            eb_generation: duration_ms(params.eb_generation_cpu_time_ms),
            eb_validation: duration_ms(params.eb_validation_cpu_time_ms),
            vote_generation_constant: duration_ms(params.vote_generation_cpu_time_ms_constant),
            vote_generation_per_ib: duration_ms(params.vote_generation_cpu_time_ms_per_ib),
            vote_validation: duration_ms(params.vote_validation_cpu_time_ms),
            cert_generation_constant: duration_ms(params.cert_generation_cpu_time_ms_constant),
            cert_generation_per_node: duration_ms(params.cert_generation_cpu_time_ms_per_node),
            cert_validation_constant: duration_ms(params.cert_validation_cpu_time_ms_constant),
            cert_validation_per_node: duration_ms(params.cert_validation_cpu_time_ms_per_node),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SimConfiguration {
    pub seed: u64,
    pub slots: Option<u64>,
    pub trace_nodes: HashSet<NodeId>,
    pub nodes: Vec<NodeConfiguration>,
    pub links: Vec<LinkConfiguration>,
    pub stage_length: u64,
    pub(crate) block_generation_probability: f64,
    pub(crate) ib_generation_probability: f64,
    pub(crate) eb_generation_probability: f64,
    pub(crate) vote_probability: f64,
    pub(crate) vote_threshold: u64,
    pub(crate) vote_slot_length: u64,
    pub(crate) max_block_size: u64,
    pub(crate) max_tx_size: u64,
    pub(crate) max_ib_size: u64,
    pub(crate) max_ib_requests_per_peer: usize,
    pub(crate) ib_shards: u64,
    pub(crate) cpu_times: CpuTimeConfig,
    pub(crate) transaction_frequency_ms: FloatDistribution,
    pub(crate) transaction_size_bytes: FloatDistribution,
}

impl SimConfiguration {
    pub fn build(params: RawParameters, topology: Topology) -> Self {
        Self {
            seed: 0,
            slots: None,
            nodes: topology.nodes,
            trace_nodes: HashSet::new(),
            links: topology.links,
            block_generation_probability: params.rb_generation_probability,
            ib_generation_probability: params.ib_generation_probability,
            eb_generation_probability: params.eb_generation_probability,
            vote_probability: params.vote_generation_probability,
            vote_threshold: params.vote_threshold,
            vote_slot_length: params.leios_stage_active_voting_slots,
            max_block_size: params.rb_body_max_size_bytes,
            max_tx_size: params.tx_max_size_bytes,
            stage_length: params.leios_stage_length_slots,
            max_ib_size: params.ib_body_max_size_bytes,
            max_ib_requests_per_peer: 1,
            ib_shards: params.ib_shards,
            cpu_times: CpuTimeConfig::new(&params),
            transaction_frequency_ms: params.tx_generation_distribution.into(),
            transaction_size_bytes: params.tx_size_bytes_distribution.into(),
        }
    }
}

fn duration_ms(ms: f64) -> Duration {
    Duration::from_secs_f64(ms / 1000.0)
}

#[derive(Debug, Clone)]
pub struct NodeConfiguration {
    pub id: NodeId,
    pub name: String,
    pub stake: u64,
    pub cpu_multiplier: f64,
    pub cores: Option<u64>,
    pub consumers: Vec<NodeId>,
}

#[derive(Debug, Clone)]
pub struct LinkConfiguration {
    pub nodes: (NodeId, NodeId),
    pub latency: Duration,
}
