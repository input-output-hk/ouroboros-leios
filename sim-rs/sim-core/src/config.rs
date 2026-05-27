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
use tracing::info;

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

#[derive(Debug, Clone, Default, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Engine {
    /// Tokio-based async actor system with virtual clock coordination
    #[default]
    Actor,
    /// Sequential discrete event simulation with BSP parallelism
    Sequential,
}

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ShardStrategy {
    /// Simple round-robin by node ID
    #[default]
    RoundRobin,
    /// Round-robin but keeps 0-latency-connected nodes on the same shard
    ZeroLatencyClusters,
    /// K-means clustering by geographic coordinates to maximize cross-shard latency
    Geographic,
    /// Agglomerative clustering: merge lowest-latency pairs first (Kruskal-style)
    MinLatencyClusters,
    /// Min-cut partitioning: recursive bisection with Kernighan-Lin refinement
    MinCut,
}

/// Which stock policy in `shared_consensus::fetch` to use for a given traffic
/// class.  Mirrors net-rs's `FetchPolicyKind` so YAML configs round-
/// trip between the two consumers.
#[derive(Debug, Clone, Copy, Default, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum FetchPolicyKind {
    /// Single-peer pick by lowest measured RTT.  Matches shared-consensus's
    /// `LeiosState::new` default.
    #[default]
    LowestRtt,
    /// Fan out to `n` lowest-RTT candidates.  Omitting `n` fans to
    /// every candidate (`BroadcastN::all()`); `n = 1` mimics LowestRtt.
    Broadcast {
        #[serde(default)]
        n: Option<usize>,
    },
    /// Suppress this class of fetch entirely.  Only meaningful for
    /// `eb-txs` (organic tx diffusion fills the gap); the other
    /// classes have no fallback and will stall.
    NoFetch,
}

/// Per-traffic-class fetch-policy selection for the shared-consensus adapter.
/// Defaults map onto `LeiosState::new`'s constructor: every class
/// uses `LowestRttFirst` with a zero-RTT oracle (sim drives fetches
/// via its own Message enum; the policy still picks which peer).
#[derive(Debug, Clone, Copy, Default, Deserialize, Serialize)]
pub struct FetchPolicy {
    #[serde(default)]
    pub block: FetchPolicyKind,
    #[serde(default)]
    pub eb: FetchPolicyKind,
    #[serde(default)]
    pub eb_txs: FetchPolicyKind,
    #[serde(default)]
    pub votes: FetchPolicyKind,
}

impl FetchPolicyKind {
    pub fn into_block_policy(self) -> Box<dyn shared_consensus::fetch::BlockFetchPolicy + Send + Sync> {
        use shared_consensus::fetch::{BroadcastN, LowestRttFirst, NoFetch};
        match self {
            FetchPolicyKind::LowestRtt => Box::new(LowestRttFirst),
            FetchPolicyKind::Broadcast { n } => Box::new(BroadcastN {
                n: n.unwrap_or(usize::MAX),
            }),
            FetchPolicyKind::NoFetch => Box::new(NoFetch),
        }
    }

    pub fn into_eb_policy(self) -> Box<dyn shared_consensus::fetch::EbFetchPolicy + Send + Sync> {
        use shared_consensus::fetch::{BroadcastN, LowestRttFirst, NoFetch};
        match self {
            FetchPolicyKind::LowestRtt => Box::new(LowestRttFirst),
            FetchPolicyKind::Broadcast { n } => Box::new(BroadcastN {
                n: n.unwrap_or(usize::MAX),
            }),
            FetchPolicyKind::NoFetch => Box::new(NoFetch),
        }
    }

    pub fn into_eb_txs_policy(self) -> Box<dyn shared_consensus::fetch::EbTxsFetchPolicy + Send + Sync> {
        use shared_consensus::fetch::{BroadcastN, LowestRttFirst, NoFetch};
        match self {
            FetchPolicyKind::LowestRtt => Box::new(LowestRttFirst),
            FetchPolicyKind::Broadcast { n } => Box::new(BroadcastN {
                n: n.unwrap_or(usize::MAX),
            }),
            FetchPolicyKind::NoFetch => Box::new(NoFetch),
        }
    }

    pub fn into_vote_policy(self) -> Box<dyn shared_consensus::fetch::VoteFetchPolicy + Send + Sync> {
        use shared_consensus::fetch::{BroadcastN, LowestRttFirst, NoFetch};
        match self {
            FetchPolicyKind::LowestRtt => Box::new(LowestRttFirst),
            FetchPolicyKind::Broadcast { n } => Box::new(BroadcastN {
                n: n.unwrap_or(usize::MAX),
            }),
            FetchPolicyKind::NoFetch => Box::new(NoFetch),
        }
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case")]
pub struct RawParameters {
    // Simulation Configuration
    #[serde(default)]
    pub seed: u64,
    pub leios_variant: LeiosVariant,
    pub relay_strategy: RelayStrategy,
    pub simulate_transactions: bool,
    #[serde(default = "default_tcp_congestion_control")]
    pub tcp_congestion_control: bool,
    pub timestamp_resolution_ms: f64,
    #[serde(default = "default_shard_count")]
    pub shard_count: usize,
    #[serde(default)]
    pub shard_strategy: ShardStrategy,
    /// Max shard size as percentage of average (for min-latency-clusters). Default 200.
    #[serde(default = "default_shard_max_size_pct")]
    pub shard_max_size_pct: u64,
    #[serde(default)]
    pub engine: Engine,
    /// Minimum simultaneous events before using rayon parallelism in the sequential engine.
    #[serde(default = "default_parallel_threshold")]
    pub parallel_threshold: usize,

    // Leios protocol configuration
    pub leios_stage_length_slots: u64,
    pub leios_stage_active_voting_slots: u64,
    pub leios_late_ib_inclusion: bool,
    pub leios_header_diffusion_time_ms: f64,
    pub leios_ib_generation_time_ms: f64,
    pub leios_mempool_sampling_strategy: MempoolSamplingStrategy,
    pub leios_mempool_aggressive_pruning: bool,
    pub leios_mempool_size_bytes: Option<u64>,
    pub leios_tx_generated_backlog_max_size: Option<usize>,
    pub leios_tx_peer_backlog_max_size: Option<usize>,
    pub praos_chain_quality: u64,
    pub praos_fallback_enabled: bool,
    pub linear_vote_stage_length_slots: u64,
    pub linear_diffuse_stage_length_slots: u64,
    pub linear_eb_propagation_criteria: EBPropagationCriteria,
    pub linear_tx_max_age_slots: Option<u64>,

    // Fetch routing (shared-consensus adapter only)
    /// Per-traffic-class fetch-policy selection.  Defaults to
    /// `lowest-rtt` for every class (matching `LeiosState::new`).
    /// Mirrors net-rs's `FetchPolicyConfig` shape.  Only consumed by
    /// the shared-consensus adapter; `linear_leios.rs` has its own diffusion path.
    #[serde(default)]
    pub fetch_policy: FetchPolicy,

    /// Should a voter retry across slots of the CIP-0164 voting
    /// window when an in-window vote attempt didn't succeed?  Covers
    /// both retry paths:
    ///
    /// - transient predicate failure (`WrongEB` / `LateRBHeader` /
    ///   `MissingTX`) — a later slot may see chain-tip / mempool
    ///   state that flips the predicate to success;
    /// - lottery loss (no PV seat, no NPV win) — the NPV trial re-runs
    ///   with a fresh per-slot VRF input.
    ///
    /// Default `true` matches the CIP reading.  `false` gives a
    /// single decision per `(voter, EB)` and one NPV trial — matches
    /// `linear_leios.rs`'s single-shot lottery behaviour.  Useful for
    /// like-for-like comparisons.  shared-consensus adapter only.
    #[serde(default = "default_retry_vote_in_window")]
    pub retry_vote_in_window: bool,

    // Transaction configuration
    pub tx_generation_distribution: DistributionConfig,
    pub tx_size_bytes_distribution: DistributionConfig,
    pub tx_overcollateralization_factor_distribution: DistributionConfig,
    pub tx_validation_cpu_time_ms: f64,
    pub tx_validation_cpu_time_ms_per_byte: f64,
    pub tx_max_size_bytes: u64,
    pub tx_conflict_fraction: Option<f64>,
    pub tx_start_time: Option<f64>,
    pub tx_stop_time: Option<f64>,
    /// When set, the sequential engine batches all TX generation events within this window
    /// into a single timestamp, independent of timestamp-resolution-ms.
    pub tx_batch_window_ms: Option<f64>,

    // Ranking block configuration
    pub rb_generation_probability: f64,
    pub rb_generation_cpu_time_ms: f64,
    pub rb_head_validation_cpu_time_ms: f64,
    pub rb_head_size_bytes: u64,
    pub rb_body_max_size_bytes: u64,

    pub rb_body_legacy_praos_payload_validation_cpu_time_ms_constant: f64,
    pub rb_body_legacy_praos_payload_validation_cpu_time_ms_per_byte: f64,
    pub rb_body_legacy_praos_payload_avg_size_bytes: u64,

    /// CPU cost to apply an RB to ledger state (UTXO mutation, after
    /// the body-validation signature/structure check has passed).
    /// Scales by tx count; defaults are minimal-but-nonzero so the
    /// `PraosState::on_block_applied` accounting fires without
    /// skewing throughput.  (`shared-consensus` adapter only — `linear_leios`
    /// collapses validate+apply into one step.)
    #[serde(default = "default_rb_apply_cpu_time_ms")]
    pub rb_apply_cpu_time_ms: f64,
    #[serde(default = "default_rb_apply_cpu_time_ms_per_tx")]
    pub rb_apply_cpu_time_ms_per_tx: f64,

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

    /// CPU cost to apply an EB closure to ledger state — the EB's
    /// referenced txs land on-chain via the certifying RB's
    /// endorsement.  Parallel pathway to `rb_apply_cpu_time_ms` and
    /// gates mempool-prune of the EB's tx set.  (`shared-consensus` adapter
    /// only.)
    #[serde(default = "default_eb_apply_cpu_time_ms")]
    pub eb_apply_cpu_time_ms: f64,
    #[serde(default = "default_eb_apply_cpu_time_ms_per_tx")]
    pub eb_apply_cpu_time_ms_per_tx: f64,

    // Vote configuration
    //
    // The two voter-count fields are the expected size of the
    // persistent / non-persistent voter committees per EB.  Historic
    // YAML keys `persistent-vote-generation-probability` /
    // `non-persistent-vote-generation-probability` are still accepted
    // (the values were always voter counts, never probabilities; the
    // old names date from a pre-CIP-0164 framing).  Linear sums them
    // into one VRF-lottery probability; shared-consensus uses them directly as
    // PV / NPV committee sizes for `CommitteeSelection::WfaLs`.
    #[serde(alias = "persistent-vote-generation-probability")]
    pub persistent_voters: f64,
    #[serde(alias = "non-persistent-vote-generation-probability")]
    pub non_persistent_voters: f64,
    pub persistent_vote_generation_cpu_time_ms: f64,
    pub non_persistent_vote_generation_cpu_time_ms: f64,
    pub vote_generation_cpu_time_ms_per_tx: f64,
    pub vote_generation_cpu_time_ms_per_ib: f64,
    pub persistent_vote_validation_cpu_time_ms: f64,
    pub non_persistent_vote_validation_cpu_time_ms: f64,
    /// Fraction of expected total weight required for quorum
    /// (CIP-0164 default 0.75).  Replaces the old absolute
    /// `vote-threshold` knob — the threshold is now derived from the
    /// committee selection mode:
    ///
    /// - `wfa-ls`: threshold = `quorum_weight_fraction × (PV+NPV)`.
    /// - `everyone`: threshold = `quorum_weight_fraction × N`.
    /// - `top-stake-fraction` (CIP-164 PR #1196): threshold =
    ///   `quorum_weight_fraction × total_active_stake`, and per-voter
    ///   weight is stake (not vote count).
    #[serde(default = "default_quorum_weight_fraction")]
    pub quorum_weight_fraction: f64,
    pub vote_bundle_size_bytes_constant: u64,
    pub persistent_vote_bundle_size_bytes_per_eb: u64,
    pub non_persistent_vote_bundle_size_bytes_per_eb: u64,
    #[serde(default)]
    pub committee_selection_algorithm: CommitteeSelectionAlgorithm,
    #[serde(default = "default_committee_stake_fraction_threshold")]
    pub committee_stake_fraction_threshold: f64,

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

    /// Per-node consensus behaviours wired into the shared-consensus
    /// engine.  Each entry pairs a [`BehaviourSpec`] with a
    /// [`BehaviourSelection`] picking which nodes run it; overlapping
    /// selections compose via [`BehaviourSpec::Composite`].  Resolution
    /// is deterministic for a given `seed`.  Empty (default) means
    /// every node runs [`BehaviourSpec::Honest`].  Only consumed by the
    /// shared-consensus adapter; ignored by other engines.
    ///
    /// [`BehaviourSpec`]: shared_consensus::behaviour::BehaviourSpec
    /// [`BehaviourSelection`]: shared_consensus::behaviour::BehaviourSelection
    /// [`BehaviourSpec::Composite`]: shared_consensus::behaviour::BehaviourSpec::Composite
    /// [`BehaviourSpec::Honest`]: shared_consensus::behaviour::BehaviourSpec::Honest
    #[serde(default)]
    pub consensus_behaviours: Vec<ConsensusBehaviourEntry>,

    /// Global tcp-envelope defaults applied to every directed link in the
    /// topology that has a bandwidth_bps set. Per-link overrides in the
    /// topology YAML's `tcp-envelope` block layer on top of this.
    #[serde(default)]
    pub tcp_envelope: Option<RawTcpEnvelope>,
}

/// One row of [`RawParameters::consensus_behaviours`].
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case")]
pub struct ConsensusBehaviourEntry {
    pub spec: shared_consensus::behaviour::BehaviourSpec,
    pub selection: shared_consensus::behaviour::BehaviourSelection,
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
    SharedConsensus,
}

impl LeiosVariant {
    pub fn has_ibs(&self) -> bool {
        !matches!(
            self,
            Self::FullWithoutIbs
                | Self::Linear
                | Self::LinearWithTxReferences
                | Self::SharedConsensus
        )
    }
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

#[derive(Debug, Default, Copy, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum CommitteeSelectionAlgorithm {
    #[default]
    WfaLs,
    Everyone,
    TopStakeFraction,
}

fn default_committee_stake_fraction_threshold() -> f64 {
    0.95
}

fn default_quorum_weight_fraction() -> f64 {
    0.75
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
    StakeFraction(f64),
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
    #[serde(skip_serializing_if = "Option::is_none", default)]
    pub tcp_envelope: Option<RawTcpEnvelope>,
}

/// User-facing topology knobs for the analytic TCP envelope model. Every
/// field is an optional override on top of the
/// [`tcp_model::LinkEnvelopeCfg::defaults_for`] derivation. Durations use
/// the same `_ms` suffix convention as the surrounding topology schema.
///
/// Note: `mss_bytes` and `initial_cwnd_segments` do *not* re-derive
/// dependent fields like `cold_bw_depth` or `cold_release_ms` on their own.
/// Override those too if you change MSS or IW away from the defaults.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct RawTcpEnvelope {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub loss_prob_per_segment: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mss_bytes: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub initial_cwnd_segments: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub idle_reset_threshold_ms: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rto_ms: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub loss_bw_depth: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cold_bw_depth: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cold_release_ms: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cold_release_shape: Option<tcp_model::Curve>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub loss_release_ms: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub loss_release_shape: Option<tcp_model::Curve>,
}

impl RawTcpEnvelope {
    /// Apply this YAML block over a baseline [`tcp_model::LinkEnvelopeCfg`].
    /// Fields left as `None` keep the baseline value. Rejects values that
    /// would crash or NaN-poison downstream computations
    /// (`mss-bytes: 0`, `loss-prob-per-segment` outside `[0, 1]`).
    pub fn apply(&self, cfg: &mut tcp_model::LinkEnvelopeCfg) -> Result<()> {
        if let Some(v) = self.loss_prob_per_segment {
            if !(0.0..=1.0).contains(&v) {
                bail!("tcp-envelope.loss-prob-per-segment must be in [0, 1], got {v}");
            }
            cfg.loss_prob_per_segment = v;
        }
        if let Some(v) = self.mss_bytes {
            if v == 0 {
                bail!("tcp-envelope.mss-bytes must be > 0");
            }
            cfg.mss_bytes = v;
        }
        if let Some(v) = self.initial_cwnd_segments {
            cfg.initial_cwnd_segments = v;
        }
        if let Some(v) = self.idle_reset_threshold_ms {
            cfg.idle_reset_threshold = Duration::from_millis(v);
        }
        if let Some(v) = self.rto_ms {
            cfg.rto = Duration::from_millis(v);
        }
        if let Some(v) = self.loss_bw_depth {
            cfg.loss_bw_depth = v;
        }
        if let Some(v) = self.cold_bw_depth {
            cfg.cold_bw_depth = v;
        }
        if let Some(v) = self.cold_release_ms {
            cfg.cold_release = Duration::from_millis(v);
        }
        if let Some(v) = self.cold_release_shape {
            cfg.cold_release_shape = v;
        }
        if let Some(v) = self.loss_release_ms {
            cfg.loss_release = Duration::from_millis(v);
        }
        if let Some(v) = self.loss_release_shape {
            cfg.loss_release_shape = v;
        }
        Ok(())
    }
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

    pub fn select(&mut self, selection: &NodeSelection) -> Vec<&mut NodeConfiguration> {
        let mut nodes = vec![];
        match selection {
            NodeSelection::Nodes(names) => {
                nodes.extend(
                    self.nodes
                        .iter_mut()
                        .filter(|node| names.contains(&node.name)),
                );
            }
            NodeSelection::StakeFraction(fraction) => {
                let mut all_nodes = self.nodes.iter_mut().collect::<Vec<_>>();
                all_nodes.sort_by_key(|n| std::cmp::Reverse(n.stake));
                let total_stake = all_nodes.iter().map(|n| n.stake).sum::<u64>();
                let target_stake = ((total_stake as f64) * *fraction) as u64;
                let mut stake_so_far = 0;
                for node in all_nodes {
                    if stake_so_far >= target_stake {
                        break;
                    }
                    stake_so_far += node.stake;
                    nodes.push(node);
                }
            }
        }
        nodes
    }
}

impl From<RawTopology> for Topology {
    fn from(value: RawTopology) -> Self {
        Self::from_raw(value, None)
    }
}

impl Topology {
    /// Convert a raw topology, layering an optional global tcp-envelope under
    /// any per-link overrides. The final per-link envelope is computed as
    /// `defaults_for(latency, bps)` → apply `global` → apply per-link. Links
    /// without a bandwidth_bps or with zero latency get no envelope, even if
    /// a global cfg is supplied.
    pub fn from_raw(value: RawTopology, global: Option<&RawTcpEnvelope>) -> Self {
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
                    location: match &node.location {
                        RawNodeLocation::Coords(coords) => Some(*coords),
                        RawNodeLocation::Cluster { .. } => None,
                    },
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
                let latency = duration_ms(producer_info.latency_ms);
                let per_link = producer_info.tcp_envelope.as_ref();
                let tcp_envelope = match (global, per_link) {
                    (None, None) => None,
                    _ => producer_info.bandwidth_bytes_per_second.and_then(|bps| {
                        if bps == 0 || latency.is_zero() {
                            return None;
                        }
                        let mut cfg = tcp_model::LinkEnvelopeCfg::defaults_for(latency, bps);
                        if let Some(g) = global {
                            g.apply(&mut cfg)
                                .expect("invalid global tcp-envelope override");
                        }
                        if let Some(l) = per_link {
                            l.apply(&mut cfg)
                                .expect("invalid per-link tcp-envelope override");
                        }
                        Some(cfg)
                    }),
                };
                links.insert(
                    ids,
                    LinkConfiguration {
                        nodes: (ids[0], ids[1]),
                        latency,
                        bandwidth_bps: producer_info.bandwidth_bytes_per_second,
                        use_tcp: false,
                        tcp_envelope,
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

fn vote_weighted_average(params: &RawParameters, persistent: f64, non_persistent: f64) -> f64 {
    match params.committee_selection_algorithm {
        // Everyone and TopStakeFraction voters are all deterministically selected,
        // so they use persistent vote parameters (no eligibility proofs needed).
        CommitteeSelectionAlgorithm::Everyone
        | CommitteeSelectionAlgorithm::TopStakeFraction => persistent,
        CommitteeSelectionAlgorithm::WfaLs => {
            let total = params.persistent_voters + params.non_persistent_voters;
            if total == 0.0 {
                return 0.0;
            }
            let frac = params.persistent_voters / total;
            frac * persistent + (1.0 - frac) * non_persistent
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct CpuTimeConfig {
    pub tx_validation_constant: Duration,
    pub tx_validation_per_byte: Duration,
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
    pub rb_apply_constant: Duration,
    pub rb_apply_per_tx: Duration,
    pub eb_apply_constant: Duration,
    pub eb_apply_per_tx: Duration,
}
impl CpuTimeConfig {
    fn new(params: &RawParameters) -> Self {
        Self {
            tx_validation_constant: duration_ms(params.tx_validation_cpu_time_ms),
            tx_validation_per_byte: duration_ms(params.tx_validation_cpu_time_ms_per_byte),
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
            vote_generation_constant: duration_ms(vote_weighted_average(
                params,
                params.persistent_vote_generation_cpu_time_ms,
                params.non_persistent_vote_generation_cpu_time_ms,
            )),
            vote_generation_per_tx: duration_ms(params.vote_generation_cpu_time_ms_per_tx),
            vote_generation_per_ib: duration_ms(params.vote_generation_cpu_time_ms_per_ib),
            vote_validation: duration_ms(vote_weighted_average(
                params,
                params.persistent_vote_validation_cpu_time_ms,
                params.non_persistent_vote_validation_cpu_time_ms,
            )),
            cert_generation_constant: duration_ms(params.cert_generation_cpu_time_ms_constant),
            cert_generation_per_node: duration_ms(params.cert_generation_cpu_time_ms_per_node),
            cert_validation_constant: duration_ms(params.cert_validation_cpu_time_ms_constant),
            cert_validation_per_node: duration_ms(params.cert_validation_cpu_time_ms_per_node),
            rb_apply_constant: duration_ms(params.rb_apply_cpu_time_ms),
            rb_apply_per_tx: duration_ms(params.rb_apply_cpu_time_ms_per_tx),
            eb_apply_constant: duration_ms(params.eb_apply_cpu_time_ms),
            eb_apply_per_tx: duration_ms(params.eb_apply_cpu_time_ms_per_tx),
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
            vote_per_eb: vote_weighted_average(
                params,
                params.persistent_vote_bundle_size_bytes_per_eb as f64,
                params.non_persistent_vote_bundle_size_bytes_per_eb as f64,
            )
            .round() as u64,
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
            LeiosVariant::LinearWithTxReferences | LeiosVariant::SharedConsensus => {
                txs.len() as u64 * self.eb_per_ib
            }
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
    pub(crate) ib_shards: u64,
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
        let all_attackers = topology.select(&raw.attackers);
        info!(
            "Late EB attackers: {:?}",
            all_attackers.iter().map(|n| &n.name).collect::<Vec<_>>()
        );
        let attackers = all_attackers.into_iter().map(|node| node.id).collect();
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
        let all_attackers = topology.select(&raw.attackers);
        info!(
            "Late TX attackers: {:?}",
            all_attackers.iter().map(|n| &n.name).collect::<Vec<_>>()
        );
        for attacker in all_attackers {
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
    pub shard_count: usize,
    pub shard_strategy: ShardStrategy,
    pub shard_max_size_pct: u64,
    pub engine: Engine,
    pub parallel_threshold: usize,
    pub slots: Option<u64>,
    pub emit_conformance_events: bool,
    pub aggregate_events: bool,
    pub log_memory_stats: bool,
    pub fetch_policy: FetchPolicy,
    pub retry_vote_in_window: bool,
    pub trace_nodes: HashSet<NodeId>,
    pub nodes: Vec<NodeConfiguration>,
    pub links: Vec<LinkConfiguration>,
    pub stage_length: u64,
    pub max_eb_age: u64,
    pub late_ib_inclusion: bool,
    pub variant: LeiosVariant,
    /// Quorum fraction (CIP-0164 default 0.75).  Compare votes against
    /// `quorum_weight_fraction × expected_total_weight`.
    pub quorum_weight_fraction: f64,
    /// Quorum denominator in the units the relevant node implementation
    /// sums per-voter weights.  WfaLs/Everyone: seats or node count.
    /// TopStakeFraction (CIP-164 PR #1196): `total_stake`.
    pub expected_total_weight: u64,
    pub(crate) total_stake: u64,
    pub(crate) praos_fallback: bool,
    pub(crate) header_diffusion_time: Duration,
    pub(crate) ib_generation_time: Duration,
    pub(crate) relay_strategy: RelayStrategy,
    pub(crate) mempool_strategy: MempoolSamplingStrategy,
    pub(crate) mempool_aggressive_pruning: bool,
    pub(crate) mempool_size_bytes: u64,
    pub(crate) tx_generated_backlog_max_size: Option<usize>,
    pub(crate) tx_peer_backlog_max_size: Option<usize>,
    pub(crate) praos_chain_quality: u64,
    pub(crate) block_generation_probability: f64,
    pub(crate) ib_generation_probability: f64,
    pub(crate) eb_generation_probability: f64,
    pub(crate) committee_selection: CommitteeSelectionAlgorithm,
    pub(crate) committee_stake_fraction_threshold: f64,
    pub(crate) vote_eligible_nodes: HashSet<NodeId>,
    /// Sum of `persistent_voters + non_persistent_voters`.  Linear
    /// uses this as a single VRF-lottery probability per (voter, EB).
    pub(crate) vote_probability: f64,
    /// CIP-0164 PV / NPV committee sizes.  shared-consensus uses these
    /// directly via [`shared_consensus::config::CommitteeSelection::WfaLs`];
    /// linear collapses them into `vote_probability`.  Stored as
    /// f64 (PV/NPV can be non-integer); shared-consensus casts at the
    /// boundary.
    pub(crate) persistent_voters: f64,
    pub(crate) non_persistent_voters: f64,
    pub(crate) vote_slot_length: u64,
    pub(crate) eb_include_txs_from_previous_stage: bool,
    pub(crate) linear_vote_stage_length: u64,
    pub(crate) linear_diffuse_stage_length: u64,
    pub(crate) linear_eb_propagation_criteria: EBPropagationCriteria,
    pub(crate) linear_tx_max_age_slots: Option<u64>,
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
    /// TX generation batching window for the sequential engine.
    pub(crate) tx_batch_window: Option<Duration>,
    /// Shared network stats collector (set by sequential engine, read by nodes).
    pub network_stats: Option<Arc<crate::network::stats::NetworkStatsCollector>>,

    /// Per-node consensus behaviour assignment.  Resolved once at
    /// build time from [`RawParameters::consensus_behaviours`].  Nodes
    /// absent from the map run [`BehaviourSpec::Honest`] (the default
    /// installed by `LeiosState::new`).  Only consumed by the
    /// shared-consensus adapter.
    ///
    /// [`BehaviourSpec::Honest`]: shared_consensus::behaviour::BehaviourSpec::Honest
    pub(crate) consensus_behaviour_specs:
        BTreeMap<NodeId, shared_consensus::behaviour::BehaviourSpec>,
}

impl SimConfiguration {
    /// Absolute quorum threshold in the units the local node
    /// implementation sums per-voter weights — derived from
    /// `quorum_weight_fraction × expected_total_weight`.  Replaces the
    /// old absolute `vote_threshold` config; downstream consumers
    /// (sim-cli liveness telemetry, per-variant endorsement gates) call
    /// this where they previously read the field.
    pub fn vote_threshold(&self) -> u64 {
        // Ceiling so an integer threshold compared against integer
        // voted weights enforces `Σ weight ≥ τ × total` exactly —
        // truncating a 2.25 product to 2 would accept 2/3 = 67% under
        // a τ = 75% quorum.  Mirrors shared-consensus aggregation.
        (self.quorum_weight_fraction * self.expected_total_weight as f64).ceil() as u64
    }

    pub fn build(params: RawParameters, mut topology: Topology) -> Result<Self> {
        if !params.ib_shards.is_multiple_of(params.ib_shard_group_count) {
            bail!(
                "ib-shards ({}) is not divisible by ib-shard-group-count ({})",
                params.ib_shards,
                params.ib_shard_group_count
            );
        }
        if matches!(params.leios_variant, LeiosVariant::FullWithoutIbs)
            && params.ib_shard_group_count != 1
            && !params
                .ib_shard_period_length_slots
                .is_multiple_of(params.leios_stage_length_slots)
        {
            bail!(
                "Invalid sharding configuration. EBs are generated every {} slot(s). This sim is configured to choose EB shards from 1 of {} groups, using a different group every {} slot(s). Some groups would never be chosen.",
                params.leios_stage_length_slots,
                params.ib_shard_group_count,
                params.ib_shard_period_length_slots
            );
        }
        let total_stake: u64 = topology.nodes.iter().map(|n| n.stake).sum();
        let consensus_behaviour_specs = resolve_consensus_behaviours(
            &params.consensus_behaviours,
            &topology.nodes,
            params.seed,
        );
        let attacks = AttackConfig::build(&params, &mut topology);
        let vote_eligible_nodes = match params.committee_selection_algorithm {
            CommitteeSelectionAlgorithm::WfaLs | CommitteeSelectionAlgorithm::Everyone => {
                HashSet::new()
            }
            CommitteeSelectionAlgorithm::TopStakeFraction => {
                // σ_c > τ — CIP-164 PR #1196.  At equality or below
                // the committee cannot meet the stake quorum even
                // with unanimous participation.
                if params.committee_stake_fraction_threshold <= params.quorum_weight_fraction {
                    bail!(
                        "top-stake-fraction committee covers σ_c={} of stake which is ≤ \
                         quorum-weight-fraction τ={}; certification is unreachable \
                         (CIP-164 PR #1196 requires σ_c > τ)",
                        params.committee_stake_fraction_threshold,
                        params.quorum_weight_fraction,
                    );
                }
                let threshold =
                    (total_stake as f64 * params.committee_stake_fraction_threshold) as u64;
                let mut nodes_by_stake: Vec<_> =
                    topology.nodes.iter().map(|n| (n.id, n.stake)).collect();
                nodes_by_stake.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
                let mut cumulative = 0u64;
                nodes_by_stake
                    .into_iter()
                    .take_while(|&(_, stake)| {
                        if cumulative >= threshold {
                            return false;
                        }
                        cumulative += stake;
                        true
                    })
                    .map(|(id, _)| id)
                    .collect()
            }
        };
        // Quorum denominator matches the per-voter weight unit each
        // node implementation sums.  WfaLs: persistent + non-persistent
        // expected vote weight.  Everyone: one seat per topology node.
        // TopStakeFraction: total active stake (PR #1196).
        let expected_total_weight: u64 = match params.committee_selection_algorithm {
            CommitteeSelectionAlgorithm::WfaLs => {
                // PV / NPV are f64 in the config; round to the nearest
                // integer rather than truncating so a configured 600.7
                // doesn't quietly become 600 and so a fractional sub-1
                // pair doesn't zero the denominator and trivialise the
                // threshold.
                (params.persistent_voters + params.non_persistent_voters).round() as u64
            }
            CommitteeSelectionAlgorithm::Everyone => topology.nodes.len() as u64,
            CommitteeSelectionAlgorithm::TopStakeFraction => total_stake,
        };
        Ok(Self {
            seed: params.seed,
            timestamp_resolution: duration_ms(params.timestamp_resolution_ms),
            shard_count: params.shard_count.max(1),
            shard_strategy: params.shard_strategy.clone(),
            shard_max_size_pct: params.shard_max_size_pct,
            engine: params.engine.clone(),
            parallel_threshold: params.parallel_threshold,
            slots: None,
            emit_conformance_events: false,
            aggregate_events: false,
            log_memory_stats: false,
            fetch_policy: params.fetch_policy,
            retry_vote_in_window: params.retry_vote_in_window,
            trace_nodes: HashSet::new(),
            nodes: topology.nodes,
            links: topology.links.into_iter().map(|mut lc| {
                lc.use_tcp = params.tcp_congestion_control;
                lc
            }).collect(),
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
            mempool_size_bytes: params.leios_mempool_size_bytes.unwrap_or(u64::MAX),
            tx_generated_backlog_max_size: params.leios_tx_generated_backlog_max_size,
            tx_peer_backlog_max_size: params.leios_tx_peer_backlog_max_size,
            praos_chain_quality: params.praos_chain_quality,
            block_generation_probability: params.rb_generation_probability,
            ib_generation_probability: params.ib_generation_probability,
            eb_generation_probability: params.eb_generation_probability,
            committee_selection: params.committee_selection_algorithm,
            committee_stake_fraction_threshold: params.committee_stake_fraction_threshold,
            vote_eligible_nodes,
            vote_probability: params.persistent_voters + params.non_persistent_voters,
            persistent_voters: params.persistent_voters,
            non_persistent_voters: params.non_persistent_voters,
            quorum_weight_fraction: params.quorum_weight_fraction,
            expected_total_weight,
            vote_slot_length: params.leios_stage_active_voting_slots,
            eb_include_txs_from_previous_stage: params.eb_include_txs_from_previous_stage,
            linear_vote_stage_length: params.linear_vote_stage_length_slots,
            linear_diffuse_stage_length: params.linear_diffuse_stage_length_slots,
            linear_eb_propagation_criteria: params.linear_eb_propagation_criteria,
            linear_tx_max_age_slots: params.linear_tx_max_age_slots,
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
            tx_batch_window: params.tx_batch_window_ms.map(duration_ms),
            network_stats: None,
            consensus_behaviour_specs,
        })
    }
}

/// Resolve `[(spec, selection)]` against the node list in `NodeId`
/// order.  Stakes are read in the same order, so the
/// `BTreeMap<usize, BehaviourSpec>` returned by
/// [`shared_consensus::behaviour::resolve_specs`] maps directly onto
/// `NodeId`s.
fn resolve_consensus_behaviours(
    items: &[ConsensusBehaviourEntry],
    nodes: &[NodeConfiguration],
    seed: u64,
) -> BTreeMap<NodeId, shared_consensus::behaviour::BehaviourSpec> {
    if items.is_empty() {
        return BTreeMap::new();
    }
    // NodeIds are assigned by topology enumeration order; assert that
    // for the slice we receive so the index translation below is sound.
    debug_assert!(
        nodes.iter().enumerate().all(|(i, n)| n.id.to_inner() == i),
        "expected NodeConfiguration ordering by NodeId"
    );
    let stakes: Vec<u64> = nodes.iter().map(|n| n.stake).collect();
    let pairs: Vec<(
        shared_consensus::behaviour::BehaviourSpec,
        shared_consensus::behaviour::BehaviourSelection,
    )> = items
        .iter()
        .map(|e| (e.spec.clone(), e.selection.clone()))
        .collect();
    shared_consensus::behaviour::resolve_specs(&pairs, &stakes, Some(seed))
        .into_iter()
        .map(|(idx, spec)| (nodes[idx].id, spec))
        .collect()
}

fn duration_ms(ms: f64) -> Duration {
    Duration::from_secs_f64(ms / 1000.0)
}

fn default_tcp_congestion_control() -> bool {
    false
}

fn default_shard_count() -> usize {
    1
}

fn default_shard_max_size_pct() -> u64 {
    200
}

fn default_parallel_threshold() -> usize {
    10
}

fn default_retry_vote_in_window() -> bool {
    true
}

fn default_rb_apply_cpu_time_ms() -> f64 {
    0.5
}

fn default_rb_apply_cpu_time_ms_per_tx() -> f64 {
    0.05
}

fn default_eb_apply_cpu_time_ms() -> f64 {
    0.5
}

fn default_eb_apply_cpu_time_ms_per_tx() -> f64 {
    0.05
}
#[derive(Debug, Clone)]
pub struct NodeConfiguration {
    pub id: NodeId,
    pub name: String,
    pub stake: u64,
    pub location: Option<(f64, f64)>,
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
    /// Use the TCP congestion-window model for this link instead of the
    /// simple bandwidth-sharing model.
    pub use_tcp: bool,
    pub tcp_envelope: Option<tcp_model::LinkEnvelopeCfg>,
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

#[cfg(test)]
mod consensus_behaviour_tests {
    use super::*;
    use shared_consensus::behaviour::{BehaviourSelection, BehaviourSpec};

    fn node(id: usize, name: &str, stake: u64) -> NodeConfiguration {
        NodeConfiguration {
            id: NodeId::new(id),
            name: name.to_string(),
            stake,
            location: None,
            cpu_multiplier: 1.0,
            cores: None,
            tx_conflict_fraction: None,
            tx_generation_weight: None,
            consumers: Vec::new(),
            behaviours: NodeBehaviours::default(),
        }
    }

    #[test]
    fn empty_items_returns_empty_map() {
        let nodes = vec![node(0, "a", 1), node(1, "b", 1)];
        let out = resolve_consensus_behaviours(&[], &nodes, 0);
        assert!(out.is_empty());
    }

    #[test]
    fn stake_fraction_maps_to_correct_node_ids() {
        let nodes = vec![
            node(0, "a", 100),
            node(1, "b", 100),
            node(2, "c", 100),
            node(3, "d", 0), // relay
        ];
        let items = vec![ConsensusBehaviourEntry {
            spec: BehaviourSpec::LazyVoter {
                reason: shared_consensus::leios::NoVoteReason::Declined,
            },
            selection: BehaviourSelection::StakeFraction { fraction: 0.4 },
        }];
        let out = resolve_consensus_behaviours(&items, &nodes, 0);
        // total 300, target 120 → cover with 2 nodes (100 + 100).
        let picked: Vec<NodeId> = out.keys().copied().collect();
        assert_eq!(picked, vec![NodeId::new(0), NodeId::new(1)]);
        for (_, spec) in &out {
            assert!(matches!(spec, BehaviourSpec::LazyVoter { .. }));
        }
    }

    #[test]
    fn overlapping_selections_compose_per_node() {
        let nodes = vec![node(0, "a", 100), node(1, "b", 100)];
        let items = vec![
            ConsensusBehaviourEntry {
                spec: BehaviourSpec::LazyVoter {
                    reason: shared_consensus::leios::NoVoteReason::Declined,
                },
                selection: BehaviourSelection::All,
            },
            ConsensusBehaviourEntry {
                spec: BehaviourSpec::RbHeaderEquivocator { ways: 2 },
                selection: BehaviourSelection::Nodes { indices: vec![0] },
            },
        ];
        let out = resolve_consensus_behaviours(&items, &nodes, 0);
        match out.get(&NodeId::new(0)) {
            Some(BehaviourSpec::Composite { children }) => {
                assert_eq!(children.len(), 2);
                assert!(matches!(children[0], BehaviourSpec::LazyVoter { .. }));
                assert!(matches!(
                    children[1],
                    BehaviourSpec::RbHeaderEquivocator { ways: 2 }
                ));
            }
            other => panic!("expected Composite at node 0, got {:?}", other),
        }
        assert!(matches!(
            out.get(&NodeId::new(1)),
            Some(BehaviourSpec::LazyVoter { .. })
        ));
    }

    #[test]
    fn stake_random_is_deterministic_across_calls() {
        let nodes: Vec<_> = (0..10)
            .map(|i| node(i, &format!("n{i}"), if i % 2 == 0 { 100 } else { 0 }))
            .collect();
        let items = vec![ConsensusBehaviourEntry {
            spec: BehaviourSpec::LazyVoter {
                reason: shared_consensus::leios::NoVoteReason::Declined,
            },
            selection: BehaviourSelection::StakeRandom { count: 2 },
        }];
        let a = resolve_consensus_behaviours(&items, &nodes, 42);
        let b = resolve_consensus_behaviours(&items, &nodes, 42);
        let c = resolve_consensus_behaviours(&items, &nodes, 43);
        assert_eq!(a.keys().collect::<Vec<_>>(), b.keys().collect::<Vec<_>>());
        assert_ne!(a.keys().collect::<Vec<_>>(), c.keys().collect::<Vec<_>>());
        // never picks zero-stake nodes
        for id in a.keys() {
            assert!(id.to_inner() % 2 == 0);
        }
    }
}

#[cfg(test)]
mod tcp_envelope_tests {
    use super::*;
    use tcp_model::Curve;

    fn parsed(yaml: &str) -> RawTcpEnvelope {
        serde_yaml::from_str(yaml).expect("parse failure")
    }

    #[test]
    fn empty_block_is_all_none() {
        let env = parsed("{}");
        assert!(env.loss_prob_per_segment.is_none());
        assert!(env.cold_release_shape.is_none());
    }

    #[test]
    fn kebab_case_fields_parse() {
        let env = parsed(
            "
            loss-prob-per-segment: 0.001
            mss-bytes: 1500
            initial-cwnd-segments: 16
            idle-reset-threshold-ms: 250
            rto-ms: 200
            loss-bw-depth: 0.75
            cold-bw-depth: 0.1
            cold-release-ms: 500
            cold-release-shape: linear
            loss-release-ms: 2000
            loss-release-shape: geometric
            ",
        );
        assert_eq!(env.loss_prob_per_segment, Some(0.001));
        assert_eq!(env.mss_bytes, Some(1500));
        assert_eq!(env.initial_cwnd_segments, Some(16));
        assert_eq!(env.idle_reset_threshold_ms, Some(250));
        assert_eq!(env.rto_ms, Some(200));
        assert_eq!(env.loss_bw_depth, Some(0.75));
        assert_eq!(env.cold_bw_depth, Some(0.1));
        assert_eq!(env.cold_release_ms, Some(500));
        assert_eq!(env.cold_release_shape, Some(Curve::Linear));
        assert_eq!(env.loss_release_ms, Some(2000));
        assert_eq!(env.loss_release_shape, Some(Curve::Geometric));
    }

    #[test]
    fn unknown_field_is_rejected() {
        let res: Result<RawTcpEnvelope, _> = serde_yaml::from_str("not-a-field: 1");
        assert!(res.is_err());
    }

    fn raw_topology_2node_with_bandwidth() -> RawTopology {
        let mut nodes = std::collections::BTreeMap::new();
        nodes.insert(
            "a".to_string(),
            RawNode {
                location: RawNodeLocation::Coords((0.0, 0.0)),
                cpu_core_count: None,
                tx_conflict_fraction: None,
                tx_generation_weight: None,
                stake: None,
                producers: std::collections::BTreeMap::new(),
                adversarial: None,
                behaviours: vec![],
            },
        );
        let mut b_producers = std::collections::BTreeMap::new();
        b_producers.insert(
            "a".to_string(),
            RawLinkInfo {
                latency_ms: 50.0,
                bandwidth_bytes_per_second: Some(1_000_000),
                tcp_envelope: None,
            },
        );
        nodes.insert(
            "b".to_string(),
            RawNode {
                location: RawNodeLocation::Coords((1.0, 1.0)),
                cpu_core_count: None,
                tx_conflict_fraction: None,
                tx_generation_weight: None,
                stake: None,
                producers: b_producers,
                adversarial: None,
                behaviours: vec![],
            },
        );
        RawTopology { nodes }
    }

    #[test]
    fn global_envelope_applies_to_every_link_without_per_link_override() {
        let global = RawTcpEnvelope {
            loss_prob_per_segment: Some(0.005),
            ..Default::default()
        };
        let topo = Topology::from_raw(raw_topology_2node_with_bandwidth(), Some(&global));
        assert_eq!(topo.links.len(), 1);
        let cfg = topo.links[0].tcp_envelope.as_ref().expect("envelope was attached");
        assert_eq!(cfg.loss_prob_per_segment, 0.005);
        // Untouched fields keep their physics-derived defaults.
        assert_eq!(cfg.mss_bytes, 1460);
    }

    #[test]
    fn no_global_and_no_per_link_means_no_envelope() {
        let topo = Topology::from_raw(raw_topology_2node_with_bandwidth(), None);
        assert_eq!(topo.links.len(), 1);
        assert!(topo.links[0].tcp_envelope.is_none());
    }

    #[test]
    fn per_link_override_layers_on_top_of_global() {
        let global = RawTcpEnvelope {
            loss_prob_per_segment: Some(0.005),
            rto_ms: Some(800),
            ..Default::default()
        };
        let mut raw = raw_topology_2node_with_bandwidth();
        raw.nodes.get_mut("b").unwrap().producers.get_mut("a").unwrap().tcp_envelope = Some(
            RawTcpEnvelope {
                rto_ms: Some(200), // per-link overrides global's 800
                ..Default::default()
            },
        );
        let topo = Topology::from_raw(raw, Some(&global));
        let cfg = topo.links[0].tcp_envelope.as_ref().unwrap();
        assert_eq!(cfg.loss_prob_per_segment, 0.005); // from global
        assert_eq!(cfg.rto, Duration::from_millis(200)); // per-link wins
    }

    #[test]
    fn apply_layers_overrides_on_top_of_defaults() {
        let yaml = "
            loss-prob-per-segment: 0.002
            rto-ms: 500
            cold-release-shape: linear
        ";
        let raw: RawTcpEnvelope = serde_yaml::from_str(yaml).unwrap();
        let mut cfg = tcp_model::LinkEnvelopeCfg::defaults_for(
            Duration::from_millis(150),
            1_000_000,
        );
        let baseline_cold_release = cfg.cold_release;
        raw.apply(&mut cfg).unwrap();
        assert_eq!(cfg.loss_prob_per_segment, 0.002);
        assert_eq!(cfg.rto, Duration::from_millis(500));
        assert_eq!(cfg.cold_release_shape, Curve::Linear);
        // Unmentioned fields keep their derived defaults.
        assert_eq!(cfg.cold_release, baseline_cold_release);
        assert_eq!(cfg.mss_bytes, 1460);
    }

    #[test]
    fn apply_rejects_invalid_mss_bytes() {
        let raw: RawTcpEnvelope = serde_yaml::from_str("mss-bytes: 0").unwrap();
        let mut cfg = tcp_model::LinkEnvelopeCfg::defaults_for(
            Duration::from_millis(150),
            1_000_000,
        );
        assert!(raw.apply(&mut cfg).is_err());
    }

    #[test]
    fn apply_rejects_loss_prob_outside_unit_interval() {
        let mut cfg = tcp_model::LinkEnvelopeCfg::defaults_for(
            Duration::from_millis(150),
            1_000_000,
        );
        let bad_low: RawTcpEnvelope =
            serde_yaml::from_str("loss-prob-per-segment: -0.1").unwrap();
        assert!(bad_low.apply(&mut cfg).is_err());
        let bad_high: RawTcpEnvelope =
            serde_yaml::from_str("loss-prob-per-segment: 1.5").unwrap();
        assert!(bad_high.apply(&mut cfg).is_err());
    }
}
