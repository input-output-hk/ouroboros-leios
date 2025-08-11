use std::{
    collections::{BTreeMap, HashSet, VecDeque},
    fmt::Display,
    sync::{Arc, atomic::AtomicU64},
    time::Duration,
};

use anyhow::{Result, anyhow, bail};
use rand::Rng;
use rand_chacha::ChaCha20Rng;
use rand_distr::Distribution;
use serde::{Deserialize, Serialize};

use crate::{
    clock::Timestamp,
    model::{Transaction, TransactionId},
    probability::FloatDistribution,
};

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

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(tag = "distribution", rename_all = "kebab-case")]
pub enum DistributionConfig {
    Normal { mean: f64, std_dev: f64 },
    Exp { lambda: f64, scale: Option<f64> },
    LogNormal { mu: f64, sigma: f64 },
    Constant { value: f64 },
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
            DistributionConfig::Constant { value } => FloatDistribution::constant(value),
        }
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct RawParameters {
    // Simulation Configuration
    pub leios_variant: LeiosVariant,
    pub relay_strategy: RelayStrategy,
    pub simulate_transactions: bool,
    pub timestamp_resolution_ms: f64,

    // Leios protocol configuration
    pub leios_stage_length_slots: u64,
    pub leios_stage_active_voting_slots: u64,
    pub leios_late_ib_inclusion: bool,
    pub leios_header_diffusion_time_ms: f64,
    pub leios_ib_generation_time_ms: f64,
    pub leios_mempool_sampling_strategy: MempoolSamplingStrategy,
    pub leios_mempool_aggressive_pruning: bool,
    pub praos_chain_quality: u64,
    pub praos_fallback_enabled: bool,
    pub linear_vote_stage_length_slots: u64,
    pub linear_diffuse_stage_length_slots: u64,
    pub linear_eb_propagation_criteria: EBPropagationCriteria,

    // Transaction configuration
    pub tx_generation_distribution: DistributionConfig,
    pub tx_size_bytes_distribution: DistributionConfig,
    pub tx_overcollateralization_factor_distribution: DistributionConfig,
    pub tx_validation_cpu_time_ms: f64,
    pub tx_max_size_bytes: u64,
    pub tx_conflict_fraction: Option<f64>,
    pub tx_start_time: Option<f64>,
    pub tx_stop_time: Option<f64>,

    // Ranking block configuration
    pub rb_generation_probability: f64,
    pub rb_generation_cpu_time_ms: f64,
    pub rb_head_validation_cpu_time_ms: f64,
    pub rb_head_size_bytes: u64,
    pub rb_body_max_size_bytes: u64,

    pub rb_body_legacy_praos_payload_validation_cpu_time_ms_constant: f64,
    pub rb_body_legacy_praos_payload_validation_cpu_time_ms_per_byte: f64,
    pub rb_body_legacy_praos_payload_avg_size_bytes: u64,

    // Input block configuration
    pub ib_generation_probability: f64,
    pub ib_generation_cpu_time_ms: f64,
    pub ib_shards: u64,
    pub ib_shard_period_length_slots: u64,
    pub ib_shard_group_count: u64,
    pub ib_head_size_bytes: u64,
    pub ib_head_validation_cpu_time_ms: f64,
    pub ib_body_validation_cpu_time_ms_constant: f64,
    pub ib_body_validation_cpu_time_ms_per_byte: f64,
    pub ib_body_avg_size_bytes: u64,
    pub ib_body_max_size_bytes: u64,
    pub ib_diffusion_strategy: DiffusionStrategy,
    pub ib_diffusion_max_bodies_to_request: u64,

    // Endorsement block configuration
    pub eb_generation_probability: f64,
    pub eb_generation_cpu_time_ms: f64,
    pub eb_validation_cpu_time_ms: f64,
    pub eb_header_validation_cpu_time_ms: f64,
    pub eb_body_validation_cpu_time_ms_constant: f64,
    pub eb_body_validation_cpu_time_ms_per_byte: f64,
    pub eb_size_bytes_constant: u64,
    pub eb_size_bytes_per_ib: u64,
    pub eb_max_age_slots: u64,
    pub eb_referenced_txs_max_size_bytes: u64,
    pub eb_body_avg_size_bytes: u64,
    pub eb_include_txs_from_previous_stage: bool,

    // Vote configuration
    pub vote_generation_probability: f64,
    pub vote_generation_cpu_time_ms_constant: f64,
    pub vote_generation_cpu_time_ms_per_tx: f64,
    pub vote_generation_cpu_time_ms_per_ib: f64,
    pub vote_validation_cpu_time_ms: f64,
    pub vote_threshold: u64,
    pub vote_bundle_size_bytes_constant: u64,
    pub vote_bundle_size_bytes_per_eb: u64,

    // Certificate configuration
    pub cert_generation_cpu_time_ms_constant: f64,
    pub cert_generation_cpu_time_ms_per_node: f64,
    pub cert_validation_cpu_time_ms_constant: f64,
    pub cert_validation_cpu_time_ms_per_node: f64,
    pub cert_size_bytes_constant: u64,
    pub cert_size_bytes_per_node: u64,

    // attacks,
    pub late_eb_attack: Option<RawLateEBAttackConfig>,
    pub late_tx_attack: Option<RawLateTXAttackConfig>,
}

#[derive(Debug, Copy, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum DiffusionStrategy {
    PeerOrder,
    FreshestFirst,
    OldestFirst,
}

#[derive(Debug, Copy, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum LeiosVariant {
    Short,
    Full,
    FullWithoutIbs,
    FullWithTxReferences,
    Linear,
    LinearWithTxReferences,
}

#[derive(Debug, Copy, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum RelayStrategy {
    RequestFromAll,
    RequestFromFirst,
}

#[derive(Debug, Copy, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum MempoolSamplingStrategy {
    OrderedById,
    Random,
}

#[derive(Debug, Copy, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum EBPropagationCriteria {
    EbReceived,
    TxsReceived,
    FullyValid,
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct RawLateEBAttackConfig {
    pub attackers: NodeSelection,
    pub propagation_delay_ms: f64,
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct RawLateTXAttackConfig {
    pub attackers: NodeSelection,
    pub attack_probability: f64,
    pub tx_generation_distribution: DistributionConfig,
    pub tx_start_time: Option<f64>,
    pub tx_stop_time: Option<f64>,
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NodeSelection {
    Nodes(HashSet<String>),
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tx_conflict_fraction: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tx_generation_weight: Option<u64>,
    pub producers: BTreeMap<String, RawLinkInfo>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub adversarial: Option<RawNodeBehaviour>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub behaviours: Vec<RawNodeBehaviour>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case", tag = "behaviour")]
pub enum RawNodeBehaviour {
    IbEquivocation,
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

    pub fn select(
        &mut self,
        selection: &NodeSelection,
    ) -> impl Iterator<Item = &mut NodeConfiguration> {
        let mut nodes = vec![];
        match selection {
            NodeSelection::Nodes(names) => {
                nodes.extend(
                    self.nodes
                        .iter_mut()
                        .filter(|node| names.contains(&node.name)),
                );
            }
        }
        nodes.into_iter()
    }
}

impl From<RawTopology> for Topology {
    fn from(value: RawTopology) -> Self {
        let mut node_ids = BTreeMap::new();
        let mut nodes = BTreeMap::new();
        for (index, (name, node)) in value.nodes.iter().enumerate() {
            let id = NodeId::new(index);
            node_ids.insert(name.clone(), id);
            let mut behaviours = NodeBehaviours::parse(&node.adversarial, &node.behaviours);
            behaviours.generate_conflicts = node.tx_conflict_fraction;
            nodes.insert(
                id,
                NodeConfiguration {
                    id,
                    name: name.clone(),
                    stake: node.stake.unwrap_or_default(),
                    cpu_multiplier: 1.0,
                    cores: node.cpu_core_count,
                    tx_conflict_fraction: node.tx_conflict_fraction,
                    tx_generation_weight: node.tx_generation_weight,
                    consumers: vec![],
                    behaviours,
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
                        bandwidth_bps: producer_info.bandwidth_bytes_per_second,
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

#[derive(Debug, Clone)]
pub(crate) struct CpuTimeConfig {
    pub tx_validation: Duration,
    pub rb_generation: Duration,
    pub rb_head_validation: Duration,
    pub rb_body_validation_constant: Duration,
    pub rb_validation_per_byte: Duration,
    pub ib_generation: Duration,
    pub ib_head_validation: Duration,
    pub ib_body_validation_constant: Duration,
    pub ib_body_validation_per_byte: Duration,
    pub eb_generation: Duration,
    pub eb_validation: Duration,
    pub eb_header_validation: Duration,
    pub eb_body_validation_constant: Duration,
    pub eb_body_validation_per_byte: Duration,
    pub vote_generation_constant: Duration,
    pub vote_generation_per_tx: Duration,
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
            rb_head_validation: duration_ms(params.rb_head_validation_cpu_time_ms),
            rb_body_validation_constant: duration_ms(
                params.rb_body_legacy_praos_payload_validation_cpu_time_ms_constant,
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
            eb_header_validation: duration_ms(params.eb_header_validation_cpu_time_ms),
            eb_body_validation_constant: duration_ms(
                params.eb_body_validation_cpu_time_ms_constant,
            ),
            eb_body_validation_per_byte: duration_ms(
                params.eb_body_validation_cpu_time_ms_per_byte,
            ),
            vote_generation_constant: duration_ms(params.vote_generation_cpu_time_ms_constant),
            vote_generation_per_tx: duration_ms(params.vote_generation_cpu_time_ms_per_tx),
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
pub(crate) struct BlockSizeConfig {
    variant: LeiosVariant,
    pub block_header: u64,
    cert_constant: u64,
    cert_per_node: u64,
    pub ib_header: u64,
    eb_constant: u64,
    eb_per_ib: u64,
    vote_constant: u64,
    vote_per_eb: u64,
}

impl BlockSizeConfig {
    fn new(params: &RawParameters) -> Self {
        Self {
            variant: params.leios_variant,
            block_header: params.rb_head_size_bytes,
            cert_constant: params.cert_size_bytes_constant,
            cert_per_node: params.cert_size_bytes_per_node,
            ib_header: params.ib_head_size_bytes,
            eb_constant: params.eb_size_bytes_constant,
            eb_per_ib: params.eb_size_bytes_per_ib,
            vote_constant: params.vote_bundle_size_bytes_constant,
            vote_per_eb: params.vote_bundle_size_bytes_per_eb,
        }
    }

    pub fn cert(&self, nodes: usize) -> u64 {
        self.cert_constant + self.cert_per_node * nodes as u64
    }

    pub fn ib_payload(&self, txs: &[Arc<Transaction>]) -> u64 {
        match self.variant {
            LeiosVariant::FullWithTxReferences => txs.len() as u64 * self.eb_per_ib,
            _ => txs.iter().map(|tx| tx.bytes).sum(),
        }
    }

    pub fn eb(&self, txs: usize, ibs: usize, ebs: usize) -> u64 {
        self.eb_constant + self.eb_per_ib * (txs + ibs + ebs) as u64
    }

    pub fn linear_eb(&self, txs: &[Arc<Transaction>]) -> u64 {
        let body_size = match self.variant {
            LeiosVariant::LinearWithTxReferences => txs.len() as u64 * self.eb_per_ib,
            _ => txs.iter().map(|tx| tx.bytes).sum::<u64>(),
        };
        self.eb_constant + body_size
    }

    pub fn vote_bundle(&self, ebs: usize) -> u64 {
        self.vote_constant + self.vote_per_eb * ebs as u64
    }
}

#[derive(Debug, Clone)]
pub(crate) enum TransactionConfig {
    Real(RealTransactionConfig),
    Mock(MockTransactionConfig),
}

impl TransactionConfig {
    fn new(params: &RawParameters) -> Self {
        if params.simulate_transactions {
            Self::Real(RealTransactionConfig {
                next_id: Arc::new(AtomicU64::new(0)),
                input_id: Arc::new(AtomicU64::new(0)),
                ib_shards: params.ib_shards,
                max_size: params.tx_max_size_bytes,
                frequency_ms: params.tx_generation_distribution.into(),
                size_bytes: params.tx_size_bytes_distribution.into(),
                overcollateralization_factor: params
                    .tx_overcollateralization_factor_distribution
                    .into(),
                conflict_fraction: params.tx_conflict_fraction.unwrap_or_default(),
                start_time: params
                    .tx_start_time
                    .map(|t| Timestamp::zero() + Duration::from_secs_f64(t)),
                stop_time: params
                    .tx_stop_time
                    .map(|t| Timestamp::zero() + Duration::from_secs_f64(t)),
            })
        } else {
            Self::Mock(MockTransactionConfig {
                next_id: Arc::new(AtomicU64::new(0)),
                ib_size: params.ib_body_avg_size_bytes,
                rb_size: params.rb_body_legacy_praos_payload_avg_size_bytes,
                eb_size: params.eb_body_avg_size_bytes,
            })
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct RealTransactionConfig {
    next_id: Arc<AtomicU64>,
    input_id: Arc<AtomicU64>,
    ib_shards: u64,
    pub max_size: u64,
    pub frequency_ms: FloatDistribution,
    pub size_bytes: FloatDistribution,
    pub overcollateralization_factor: FloatDistribution,
    pub conflict_fraction: f64,
    pub start_time: Option<Timestamp>,
    pub stop_time: Option<Timestamp>,
}

impl RealTransactionConfig {
    pub fn new_tx(&self, rng: &mut ChaCha20Rng, conflict_fraction: Option<f64>) -> Transaction {
        use std::sync::atomic::Ordering::Relaxed;
        let id = TransactionId::new(self.next_id.fetch_add(1, Relaxed));
        let shard = rng.random_range(0..self.ib_shards);
        let bytes = (self.size_bytes.sample(rng) as u64).min(self.max_size);
        let input_id = if rng.random_bool(conflict_fraction.unwrap_or(self.conflict_fraction)) {
            // conflict, use id from before
            self.input_id.load(Relaxed)
        } else {
            // no conflict, use new id
            self.input_id.fetch_add(1, Relaxed) + 1
        };
        let overcollateralization_factor = self.overcollateralization_factor.sample(rng) as u64;
        Transaction {
            id,
            shard,
            bytes,
            input_id,
            overcollateralization_factor,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct MockTransactionConfig {
    next_id: Arc<AtomicU64>,
    pub ib_size: u64,
    pub rb_size: u64,
    pub eb_size: u64,
}

impl MockTransactionConfig {
    pub fn mock_tx(&self, bytes: u64) -> Transaction {
        let id = self
            .next_id
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Transaction {
            id: TransactionId::new(id),
            shard: 0,
            bytes,
            input_id: id,
            overcollateralization_factor: 0,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct AttackConfig {
    pub(crate) late_eb: Option<LateEBAttackConfig>,
    pub(crate) late_tx: Option<LateTXAttackConfig>,
}
impl AttackConfig {
    fn build(params: &RawParameters, topology: &mut Topology) -> Self {
        if let Some(late_tx) = &params.late_tx_attack {
            for attacker in topology.select(&late_tx.attackers) {
                attacker.behaviours.withhold_txs = true;
            }
        }
        Self {
            late_eb: params
                .late_eb_attack
                .as_ref()
                .map(|raw| LateEBAttackConfig::build(raw, topology)),
            late_tx: params
                .late_tx_attack
                .as_ref()
                .map(|raw| LateTXAttackConfig::build(raw, topology, params)),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct LateEBAttackConfig {
    pub(crate) attackers: HashSet<NodeId>,
    pub(crate) propagation_delay: Duration,
}

impl LateEBAttackConfig {
    fn build(raw: &RawLateEBAttackConfig, topology: &mut Topology) -> Self {
        let attackers = topology
            .select(&raw.attackers)
            .map(|node| node.id)
            .collect();
        Self {
            attackers,
            propagation_delay: duration_ms(raw.propagation_delay_ms),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct LateTXAttackConfig {
    pub(crate) probability: f64,
    pub(crate) txs_to_generate: FloatDistribution,
    pub(crate) start_time: Option<Timestamp>,
    pub(crate) stop_time: Option<Timestamp>,
}

impl LateTXAttackConfig {
    fn build(raw: &RawLateTXAttackConfig, topology: &mut Topology, params: &RawParameters) -> Self {
        for attacker in topology.select(&raw.attackers) {
            attacker.behaviours.withhold_txs = true;
        }
        Self {
            probability: raw.attack_probability,
            txs_to_generate: raw.tx_generation_distribution.into(),
            start_time: raw
                .tx_start_time
                .or(params.tx_start_time)
                .map(|t| Timestamp::zero() + Duration::from_secs_f64(t)),
            stop_time: raw
                .tx_stop_time
                .or(params.tx_stop_time)
                .map(|t| Timestamp::zero() + Duration::from_secs_f64(t)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SimConfiguration {
    pub seed: u64,
    pub timestamp_resolution: Duration,
    pub slots: Option<u64>,
    pub emit_conformance_events: bool,
    pub aggregate_events: bool,
    pub trace_nodes: HashSet<NodeId>,
    pub nodes: Vec<NodeConfiguration>,
    pub links: Vec<LinkConfiguration>,
    pub stage_length: u64,
    pub max_eb_age: u64,
    pub late_ib_inclusion: bool,
    pub variant: LeiosVariant,
    pub vote_threshold: u64,
    pub(crate) total_stake: u64,
    pub(crate) praos_fallback: bool,
    pub(crate) header_diffusion_time: Duration,
    pub(crate) ib_generation_time: Duration,
    pub(crate) relay_strategy: RelayStrategy,
    pub(crate) mempool_strategy: MempoolSamplingStrategy,
    pub(crate) mempool_aggressive_pruning: bool,
    pub(crate) praos_chain_quality: u64,
    pub(crate) block_generation_probability: f64,
    pub(crate) ib_generation_probability: f64,
    pub(crate) eb_generation_probability: f64,
    pub(crate) vote_probability: f64,
    pub(crate) vote_slot_length: u64,
    pub(crate) eb_include_txs_from_previous_stage: bool,
    pub(crate) linear_vote_stage_length: u64,
    pub(crate) linear_diffuse_stage_length: u64,
    pub(crate) linear_eb_propagation_criteria: EBPropagationCriteria,
    pub(crate) max_block_size: u64,
    pub(crate) max_ib_size: u64,
    pub(crate) max_eb_size: u64,
    pub(crate) ib_diffusion_strategy: DiffusionStrategy,
    pub(crate) max_ib_requests_per_peer: usize,
    pub(crate) ib_shards: u64,
    pub(crate) ib_shard_period_slots: u64,
    pub(crate) ib_shard_groups: u64,
    pub(crate) cpu_times: CpuTimeConfig,
    pub(crate) sizes: BlockSizeConfig,
    pub(crate) transactions: TransactionConfig,
    pub(crate) attacks: AttackConfig,
}

impl SimConfiguration {
    pub fn build(params: RawParameters, mut topology: Topology) -> Result<Self> {
        if params.ib_shards % params.ib_shard_group_count != 0 {
            bail!(
                "ib-shards ({}) is not divisible by ib-shard-group-count ({})",
                params.ib_shards,
                params.ib_shard_group_count
            );
        }
        if matches!(params.leios_variant, LeiosVariant::FullWithoutIbs)
            && params.ib_shard_group_count != 1
            && params.ib_shard_period_length_slots % params.leios_stage_length_slots != 0
        {
            bail!(
                "Invalid sharding configuration. EBs are generated every {} slot(s). This sim is configured to choose EB shards from 1 of {} groups, using a different group every {} slot(s). Some groups would never be chosen.",
                params.leios_stage_length_slots,
                params.ib_shard_group_count,
                params.ib_shard_period_length_slots
            );
        }
        let total_stake = topology.nodes.iter().map(|n| n.stake).sum();
        let attacks = AttackConfig::build(&params, &mut topology);
        Ok(Self {
            seed: 0,
            timestamp_resolution: duration_ms(params.timestamp_resolution_ms),
            slots: None,
            emit_conformance_events: false,
            aggregate_events: false,
            trace_nodes: HashSet::new(),
            nodes: topology.nodes,
            links: topology.links,
            stage_length: params.leios_stage_length_slots,
            max_eb_age: params.eb_max_age_slots,
            late_ib_inclusion: params.leios_late_ib_inclusion,
            variant: params.leios_variant,
            total_stake,
            praos_fallback: params.praos_fallback_enabled,
            header_diffusion_time: duration_ms(params.leios_header_diffusion_time_ms),
            ib_generation_time: duration_ms(params.leios_ib_generation_time_ms),
            relay_strategy: params.relay_strategy,
            mempool_strategy: params.leios_mempool_sampling_strategy,
            mempool_aggressive_pruning: params.leios_mempool_aggressive_pruning,
            praos_chain_quality: params.praos_chain_quality,
            block_generation_probability: params.rb_generation_probability,
            ib_generation_probability: params.ib_generation_probability,
            eb_generation_probability: params.eb_generation_probability,
            vote_probability: params.vote_generation_probability,
            vote_threshold: params.vote_threshold,
            vote_slot_length: params.leios_stage_active_voting_slots,
            eb_include_txs_from_previous_stage: params.eb_include_txs_from_previous_stage,
            linear_vote_stage_length: params.linear_vote_stage_length_slots,
            linear_diffuse_stage_length: params.linear_diffuse_stage_length_slots,
            linear_eb_propagation_criteria: params.linear_eb_propagation_criteria,
            max_block_size: params.rb_body_max_size_bytes,
            max_ib_size: params.ib_body_max_size_bytes,
            max_eb_size: params.eb_referenced_txs_max_size_bytes,
            ib_diffusion_strategy: params.ib_diffusion_strategy,
            max_ib_requests_per_peer: params.ib_diffusion_max_bodies_to_request as usize,
            ib_shards: params.ib_shards,
            ib_shard_period_slots: params.ib_shard_period_length_slots,
            ib_shard_groups: params.ib_shard_group_count,
            cpu_times: CpuTimeConfig::new(&params),
            sizes: BlockSizeConfig::new(&params),
            transactions: TransactionConfig::new(&params),
            attacks,
        })
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
    pub tx_conflict_fraction: Option<f64>,
    pub tx_generation_weight: Option<u64>,
    pub consumers: Vec<NodeId>,
    pub behaviours: NodeBehaviours,
}

#[derive(Debug, Clone)]
pub struct LinkConfiguration {
    pub nodes: (NodeId, NodeId),
    pub latency: Duration,
    pub bandwidth_bps: Option<u64>,
}

#[derive(Debug, Clone, Default)]
pub struct NodeBehaviours {
    pub ib_equivocation: bool,
    pub withhold_txs: bool,
    pub generate_conflicts: Option<f64>,
}

impl NodeBehaviours {
    fn parse(adversarial: &Option<RawNodeBehaviour>, behaviours: &[RawNodeBehaviour]) -> Self {
        let mut result = NodeBehaviours::default();
        for behaviour in adversarial.iter().chain(behaviours) {
            match behaviour {
                RawNodeBehaviour::IbEquivocation => {
                    result.ib_equivocation = true;
                }
            }
        }
        result
    }
}
