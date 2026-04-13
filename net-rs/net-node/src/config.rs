//! TOML-based configuration with layered loading via figment.
//!
//! Config files are loaded left-to-right via repeatable `--config` flags,
//! with later files overriding earlier ones. Individual values can be
//! overridden with `--set key=value`.

use std::collections::HashMap;

use figment::providers::{Format, Serialized, Toml};
use figment::Figment;
use rand::rngs::StdRng;
use rand::Rng;
use serde::{Deserialize, Serialize};

/// Dynamic (hot-reloadable) subset of node configuration.
///
/// These fields can be updated at runtime without restarting the node,
/// delivered via a `tokio::sync::watch` channel.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct DynamicConfig {
    pub rb_generation_probability: f64,
    pub eb_generation_probability: f64,
    pub vote_generation_probability: f64,
    pub rb_head_validation_ms: f64,
    pub rb_body_validation_ms_constant: f64,
    pub rb_body_validation_ms_per_byte: f64,
    pub eb_validation_ms: f64,
    pub vote_validation_ms: f64,
    pub tx_rate: f64,
}

/// Partial update for dynamic config fields. All fields are optional;
/// only present fields are applied. This is what arrives on stdin as JSON.
#[derive(Debug, Clone, Default, Deserialize, Serialize)]
pub struct DynamicConfigUpdate {
    pub rb_generation_probability: Option<f64>,
    pub eb_generation_probability: Option<f64>,
    pub vote_generation_probability: Option<f64>,
    pub rb_head_validation_ms: Option<f64>,
    pub rb_body_validation_ms_constant: Option<f64>,
    pub rb_body_validation_ms_per_byte: Option<f64>,
    pub eb_validation_ms: Option<f64>,
    pub vote_validation_ms: Option<f64>,
    pub tx_rate: Option<f64>,
}

impl DynamicConfig {
    /// Merge a partial update into this config. Only fields that are `Some`
    /// in the update are overwritten.
    pub fn apply_update(&mut self, update: &DynamicConfigUpdate) {
        if let Some(v) = update.rb_generation_probability {
            self.rb_generation_probability = v;
        }
        if let Some(v) = update.eb_generation_probability {
            self.eb_generation_probability = v;
        }
        if let Some(v) = update.vote_generation_probability {
            self.vote_generation_probability = v;
        }
        if let Some(v) = update.rb_head_validation_ms {
            self.rb_head_validation_ms = v;
        }
        if let Some(v) = update.rb_body_validation_ms_constant {
            self.rb_body_validation_ms_constant = v;
        }
        if let Some(v) = update.rb_body_validation_ms_per_byte {
            self.rb_body_validation_ms_per_byte = v;
        }
        if let Some(v) = update.eb_validation_ms {
            self.eb_validation_ms = v;
        }
        if let Some(v) = update.vote_validation_ms {
            self.vote_validation_ms = v;
        }
        if let Some(v) = update.tx_rate {
            self.tx_rate = v;
        }
    }
}

/// Peer connection configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct PeerConfig {
    /// Address to connect to (e.g. "127.0.0.1:3002").
    pub address: String,

    /// Simulated inbound delay in milliseconds (events from this peer are
    /// delayed before delivery to the node). None = no delay.
    pub inbound_delay_ms: Option<u64>,
}

/// Top-level node configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct NodeConfig {
    /// Human-readable node identifier (used in logs and telemetry).
    #[serde(default = "default_node_id")]
    pub node_id: String,

    /// Address to listen on for inbound connections. None = don't listen.
    pub listen_address: Option<String>,

    /// Network magic number (must match peers).
    #[serde(default = "default_network_magic")]
    pub network_magic: u64,

    /// Slot duration in milliseconds.
    #[serde(default = "default_slot_duration_ms")]
    pub slot_duration_ms: u64,

    /// Genesis time as Unix timestamp (seconds). All nodes in the network
    /// must use the same value.
    pub genesis_time_unix: u64,

    /// PRNG seed for deterministic behaviour. None = use entropy.
    pub seed: Option<u64>,

    /// Enable Leios protocols (LeiosNotify + LeiosFetch).
    #[serde(default)]
    pub leios_enabled: bool,

    /// Mux scheduler strategy.
    #[serde(default = "default_scheduler")]
    pub scheduler: String,

    /// Maximum number of managed peers.
    #[serde(default = "default_max_peers")]
    pub max_peers: usize,

    /// KeepAlive interval in seconds.
    #[serde(default = "default_keepalive_interval_secs")]
    pub keepalive_interval_secs: u64,

    /// Maximum blocks to retain in the chain store.
    #[serde(default = "default_chain_store_capacity")]
    pub chain_store_capacity: usize,

    /// Slot window for Leios announcement deduplication.
    #[serde(default = "default_leios_dedup_window")]
    pub leios_dedup_window: u64,

    /// Maximum concurrent inbound handshakes.
    #[serde(default = "default_max_handshaking")]
    pub max_handshaking: usize,

    /// Maximum connections per IP.
    #[serde(default = "default_max_connections_per_ip")]
    pub max_connections_per_ip: usize,

    /// Chain security parameter k — blocks deeper than this below the best
    /// tip are considered immutable and pruned from the chain tree.
    #[serde(default = "default_security_param_k")]
    pub security_param_k: u64,

    /// Block production settings.
    #[serde(default)]
    pub production: ProductionConfig,

    /// Transaction generation settings.
    #[serde(default)]
    pub transactions: TxConfig,

    /// Validation timing settings.
    #[serde(default)]
    pub validation: ValidationConfig,

    /// Telemetry configuration.
    #[serde(default)]
    pub telemetry: TelemetryConfig,

    /// Outbound peer list.
    #[serde(default)]
    pub peers: Vec<PeerConfig>,
}

// ---------------------------------------------------------------------------
// Committee selection (Leios voting)
// ---------------------------------------------------------------------------

/// Decision from committee selection: what kind of vote to produce (if any).
///
/// Persistent votes are smaller (~130B) because the voter's eligibility is
/// established per-epoch and doesn't need per-election proof. Non-persistent
/// votes are larger (~180B) because they include a 48-byte eligibility
/// signature proving the voter won the per-election sortition lottery.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VoteDecision {
    /// Node does not vote this election.
    NoVote,
    /// Epoch-stable voter (wFA persistent committee, EveryoneVotes, StakeCentile).
    PersistentVote,
    /// Per-election sortition winner (LS non-persistent voter in wFA+LS).
    NonPersistentVote,
}

/// Committee selection mechanism for Leios voting.
///
/// Determines which nodes vote and what type of vote they produce.
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum CommitteeSelection {
    /// CIP-0164 spec: weighted Fait Accompli persistent committee (wFA) +
    /// Local Sortition non-persistent voters (LS).
    ///
    /// Persistent voters: top stake holders (semi-permanent per-epoch).
    /// They always vote with small `PersistentVote` bodies.
    ///
    /// Non-persistent voters: elected per-election via VRF-like sortition
    /// using `vote_generation_probability`. They produce larger
    /// `NonPersistentVote` bodies that include an eligibility proof.
    WfaLs {
        /// Fraction of total stake held by the persistent committee.
        /// A node is persistent if `stake/total_stake >= 1.0 - this`.
        #[serde(default = "default_persistent_stake_fraction")]
        persistent_stake_fraction: f64,
    },

    /// All staked nodes vote on every EB.
    /// Eligibility is trivial and epoch-stable → `PersistentVote`.
    EveryoneVotes,

    /// Top centile of stake participates. E.g., 0.95 means include the
    /// largest stakers until 95% of total stake is covered. For uniform
    /// stake this approximates as a per-node probability.
    /// Eligibility is epoch-stable → `PersistentVote`.
    StakeCentile {
        /// Target fraction of total stake that should participate.
        #[serde(default = "default_top_centile")]
        top_centile_of_stake: f64,
    },
}

fn default_persistent_stake_fraction() -> f64 {
    0.3
}

fn default_top_centile() -> f64 {
    0.95
}

fn default_quorum_stake_fraction() -> f64 {
    0.75
}

fn default_persistent_vote_bytes() -> usize {
    130
}

fn default_non_persistent_vote_bytes() -> usize {
    180
}

impl Default for CommitteeSelection {
    fn default() -> Self {
        CommitteeSelection::WfaLs {
            persistent_stake_fraction: default_persistent_stake_fraction(),
        }
    }
}

impl CommitteeSelection {
    /// Decide whether this node votes and what type of vote to produce.
    ///
    /// - `stake`: this node's stake
    /// - `total_stake`: total network stake
    /// - `vote_probability`: per-election sortition probability (from DynamicConfig)
    /// - `rng`: random number generator for sortition lottery
    pub fn decide_vote(
        &self,
        stake: u64,
        total_stake: u64,
        vote_probability: f64,
        rng: &mut StdRng,
    ) -> VoteDecision {
        if stake == 0 || total_stake == 0 {
            return VoteDecision::NoVote;
        }
        let stake_fraction = stake as f64 / total_stake as f64;

        match self {
            CommitteeSelection::WfaLs {
                persistent_stake_fraction,
            } => {
                // Persistent: top-stake nodes always vote.
                if stake_fraction >= (1.0 - persistent_stake_fraction) {
                    return VoteDecision::PersistentVote;
                }
                // Non-persistent: per-election sortition lottery.
                let per_node = vote_probability * stake_fraction;
                if rng.gen::<f64>() < per_node {
                    VoteDecision::NonPersistentVote
                } else {
                    VoteDecision::NoVote
                }
            }
            CommitteeSelection::EveryoneVotes => VoteDecision::PersistentVote,
            CommitteeSelection::StakeCentile {
                top_centile_of_stake,
            } => {
                // Approximate: each node participates with probability
                // equal to the target centile. For uniform stake this
                // is exact; for skewed stake the cluster overlay can
                // compute a per-node threshold instead.
                if rng.gen::<f64>() < *top_centile_of_stake {
                    VoteDecision::PersistentVote
                } else {
                    VoteDecision::NoVote
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Production config
// ---------------------------------------------------------------------------

/// Block production configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ProductionConfig {
    /// This node's stake.
    #[serde(default)]
    pub stake: u64,

    /// Total network stake. Must be consistent across all nodes.
    #[serde(default = "default_total_stake")]
    pub total_stake: u64,

    /// Per-slot probability of producing a ranking block.
    #[serde(default = "default_rb_probability")]
    pub rb_generation_probability: f64,

    /// Per-stage probability of producing an endorser block (Leios).
    #[serde(default)]
    pub eb_generation_probability: f64,

    /// Per-stage probability of producing a vote (Leios).
    /// Used as the sortition lottery probability for WfaLs non-persistent voters.
    #[serde(default)]
    pub vote_generation_probability: f64,

    /// Leios stage length in slots.
    #[serde(default = "default_stage_length")]
    pub stage_length_slots: u64,

    /// Committee selection mechanism for Leios voting.
    #[serde(default)]
    pub committee_selection: CommitteeSelection,

    /// Size of a persistent vote body in bytes (no eligibility proof).
    #[serde(default = "default_persistent_vote_bytes")]
    pub persistent_vote_bytes: usize,

    /// Size of a non-persistent vote body in bytes (includes eligibility proof).
    #[serde(default = "default_non_persistent_vote_bytes")]
    pub non_persistent_vote_bytes: usize,

    /// Fraction of total stake required for quorum.
    #[serde(default = "default_quorum_stake_fraction")]
    pub quorum_stake_fraction: f64,

    /// CIP-0164 header diffusion parameter (Δhdr) in slots.
    #[serde(default = "default_delta_hdr")]
    pub leios_delta_hdr_slots: u64,

    /// CIP-0164 voting window (L_vote) in slots.
    #[serde(default = "default_vote_window")]
    pub leios_vote_window_slots: u64,

    /// CIP-0164 diffusion window (L_diff) in slots.
    #[serde(default = "default_diffuse_window")]
    pub leios_diffuse_window_slots: u64,

    /// Maximum bytes of transaction data in an RB body. When the mempool
    /// exceeds this, transactions go into an EB instead.
    #[serde(default = "default_rb_body_max_bytes")]
    pub rb_body_max_bytes: usize,
}

fn default_total_stake() -> u64 {
    1000
}

fn default_rb_probability() -> f64 {
    0.05
}

fn default_stage_length() -> u64 {
    20
}

fn default_delta_hdr() -> u64 {
    1
}

fn default_vote_window() -> u64 {
    5
}

fn default_diffuse_window() -> u64 {
    5
}

fn default_rb_body_max_bytes() -> usize {
    65_536
}

impl Default for ProductionConfig {
    fn default() -> Self {
        Self {
            stake: 0,
            total_stake: default_total_stake(),
            rb_generation_probability: default_rb_probability(),
            eb_generation_probability: 0.0,
            vote_generation_probability: 0.0,
            stage_length_slots: default_stage_length(),
            committee_selection: CommitteeSelection::default(),
            persistent_vote_bytes: default_persistent_vote_bytes(),
            non_persistent_vote_bytes: default_non_persistent_vote_bytes(),
            quorum_stake_fraction: default_quorum_stake_fraction(),
            leios_delta_hdr_slots: default_delta_hdr(),
            leios_vote_window_slots: default_vote_window(),
            leios_diffuse_window_slots: default_diffuse_window(),
            rb_body_max_bytes: default_rb_body_max_bytes(),
        }
    }
}

/// Transaction generation configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct TxConfig {
    /// Transaction generation rate (txs/sec, Poisson lambda). 0 = disabled.
    #[serde(default)]
    pub tx_rate: f64,

    /// Minimum transaction body size in bytes.
    #[serde(default = "default_tx_size_min")]
    pub tx_size_min: usize,

    /// Maximum transaction body size in bytes.
    #[serde(default = "default_tx_size_max")]
    pub tx_size_max: usize,

    /// Maximum number of transactions in the mempool.
    #[serde(default = "default_mempool_capacity")]
    pub mempool_capacity: usize,
}

fn default_tx_size_min() -> usize {
    250
}

fn default_tx_size_max() -> usize {
    16384
}

fn default_mempool_capacity() -> usize {
    10_000
}

impl Default for TxConfig {
    fn default() -> Self {
        Self {
            tx_rate: 0.0,
            tx_size_min: default_tx_size_min(),
            tx_size_max: default_tx_size_max(),
            mempool_capacity: default_mempool_capacity(),
        }
    }
}

/// Validation timing configuration.
///
/// Fake validation simulates CPU cost as `sleep(constant + per_byte * body_len)`.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ValidationConfig {
    /// Constant component of RB header validation (ms).
    #[serde(default = "default_rb_head_ms")]
    pub rb_head_validation_ms: f64,

    /// Constant component of RB body validation (ms).
    #[serde(default = "default_rb_body_ms_constant")]
    pub rb_body_validation_ms_constant: f64,

    /// Per-byte component of RB body validation (ms/byte).
    #[serde(default)]
    pub rb_body_validation_ms_per_byte: f64,

    /// Constant component of TX validation (ms).
    #[serde(default = "default_tx_validation_ms")]
    pub tx_validation_ms: f64,

    /// Per-byte component of TX validation (ms/byte).
    #[serde(default)]
    pub tx_validation_ms_per_byte: f64,

    /// Endorser block validation (ms).
    #[serde(default = "default_eb_validation_ms")]
    pub eb_validation_ms: f64,

    /// Vote validation (ms).
    #[serde(default = "default_vote_validation_ms")]
    pub vote_validation_ms: f64,
}

fn default_rb_head_ms() -> f64 {
    1.0
}
fn default_rb_body_ms_constant() -> f64 {
    1000.0
}
fn default_tx_validation_ms() -> f64 {
    0.5
}
fn default_eb_validation_ms() -> f64 {
    2.0
}
fn default_vote_validation_ms() -> f64 {
    1.0
}

impl Default for ValidationConfig {
    fn default() -> Self {
        Self {
            rb_head_validation_ms: default_rb_head_ms(),
            rb_body_validation_ms_constant: default_rb_body_ms_constant(),
            rb_body_validation_ms_per_byte: 0.0,
            tx_validation_ms: default_tx_validation_ms(),
            tx_validation_ms_per_byte: 0.0,
            eb_validation_ms: default_eb_validation_ms(),
            vote_validation_ms: default_vote_validation_ms(),
        }
    }
}

/// Telemetry configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct TelemetryConfig {
    /// Stats emission interval in seconds. 0 = disabled.
    #[serde(default = "default_stats_interval")]
    pub stats_interval_secs: u64,

    /// Event sinks.
    #[serde(default)]
    pub event_sinks: Vec<EventSinkConfig>,

    /// Stats sinks.
    #[serde(default)]
    pub stats_sinks: Vec<StatsSinkConfig>,
}

fn default_stats_interval() -> u64 {
    10
}

impl Default for TelemetryConfig {
    fn default() -> Self {
        Self {
            stats_interval_secs: default_stats_interval(),
            event_sinks: Vec::new(),
            stats_sinks: Vec::new(),
        }
    }
}

/// Event sink configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum EventSinkConfig {
    #[serde(rename = "file")]
    File { path: String },
    #[serde(rename = "http")]
    Http { url: String },
}

/// Stats sink configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum StatsSinkConfig {
    #[serde(rename = "log")]
    Log,
    #[serde(rename = "http")]
    Http { url: String },
}

// --- defaults ---

fn default_node_id() -> String {
    "node-0".to_string()
}

fn default_network_magic() -> u64 {
    764824073 // mainnet
}

fn default_slot_duration_ms() -> u64 {
    1000
}

fn default_scheduler() -> String {
    "priority-wfq".to_string()
}

fn default_max_peers() -> usize {
    20
}

fn default_keepalive_interval_secs() -> u64 {
    20
}

fn default_chain_store_capacity() -> usize {
    10_000
}

fn default_leios_dedup_window() -> u64 {
    1000
}

fn default_security_param_k() -> u64 {
    2160
}

fn default_max_handshaking() -> usize {
    64
}

fn default_max_connections_per_ip() -> usize {
    3
}

impl Default for NodeConfig {
    fn default() -> Self {
        Self {
            node_id: default_node_id(),
            listen_address: None,
            network_magic: default_network_magic(),
            slot_duration_ms: default_slot_duration_ms(),
            genesis_time_unix: 0,
            seed: None,
            leios_enabled: false,
            scheduler: default_scheduler(),
            max_peers: default_max_peers(),
            keepalive_interval_secs: default_keepalive_interval_secs(),
            chain_store_capacity: default_chain_store_capacity(),
            leios_dedup_window: default_leios_dedup_window(),
            security_param_k: default_security_param_k(),
            max_handshaking: default_max_handshaking(),
            max_connections_per_ip: default_max_connections_per_ip(),
            production: ProductionConfig::default(),
            transactions: TxConfig::default(),
            validation: ValidationConfig::default(),
            telemetry: TelemetryConfig::default(),
            peers: Vec::new(),
        }
    }
}

impl NodeConfig {
    /// Extract the dynamic (hot-reloadable) subset of this config.
    pub fn dynamic_config(&self) -> DynamicConfig {
        DynamicConfig {
            rb_generation_probability: self.production.rb_generation_probability,
            eb_generation_probability: self.production.eb_generation_probability,
            vote_generation_probability: self.production.vote_generation_probability,
            rb_head_validation_ms: self.validation.rb_head_validation_ms,
            rb_body_validation_ms_constant: self.validation.rb_body_validation_ms_constant,
            rb_body_validation_ms_per_byte: self.validation.rb_body_validation_ms_per_byte,
            eb_validation_ms: self.validation.eb_validation_ms,
            vote_validation_ms: self.validation.vote_validation_ms,
            tx_rate: self.transactions.tx_rate,
        }
    }
}

/// Load configuration from layered TOML files with CLI overrides.
///
/// Files are applied left-to-right (later files override earlier). Key=value
/// pairs from `--set` are applied last.
pub fn load(
    config_files: &[String],
    set_overrides: &[String],
) -> Result<NodeConfig, Box<dyn std::error::Error + Send + Sync>> {
    let mut figment = Figment::from(Serialized::defaults(NodeConfig::default()));

    for path in config_files {
        figment = figment.merge(Toml::file(path));
    }

    // Apply --set key=value overrides as a TOML fragment.
    if !set_overrides.is_empty() {
        let toml_fragment = set_overrides_to_toml(set_overrides)?;
        figment = figment.merge(Toml::string(&toml_fragment));
    }

    let config: NodeConfig = figment.extract()?;
    Ok(config)
}

/// Convert `["key=value", ...]` into a TOML string for figment merging.
fn set_overrides_to_toml(
    overrides: &[String],
) -> Result<String, Box<dyn std::error::Error + Send + Sync>> {
    let mut map: HashMap<String, String> = HashMap::new();
    for kv in overrides {
        let (key, value) = kv
            .split_once('=')
            .ok_or_else(|| format!("invalid --set format, expected key=value: {kv}"))?;
        map.insert(key.trim().to_string(), value.trim().to_string());
    }

    // Build a minimal TOML string. We let figment parse the values as TOML
    // literals (strings, numbers, booleans all work).
    let mut buf = String::new();
    for (key, value) in &map {
        // If the value looks like it needs quoting (not a number/bool), quote it.
        let needs_quote = value.parse::<f64>().is_err()
            && value.parse::<i64>().is_err()
            && value != "true"
            && value != "false";
        if needs_quote {
            buf.push_str(&format!("{key} = \"{value}\"\n"));
        } else {
            buf.push_str(&format!("{key} = {value}\n"));
        }
    }
    Ok(buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_config_is_valid() {
        let config = NodeConfig::default();
        assert_eq!(config.node_id, "node-0");
        assert_eq!(config.slot_duration_ms, 1000);
        assert_eq!(config.network_magic, 764824073);
    }

    #[test]
    fn empty_load_gives_defaults() {
        let config = load(&[], &[]).unwrap();
        assert_eq!(config.node_id, "node-0");
        assert_eq!(config.max_peers, 20);
    }

    #[test]
    fn set_overrides_numeric() {
        let config = load(&[], &["slot_duration_ms=500".to_string()]).unwrap();
        assert_eq!(config.slot_duration_ms, 500);
    }

    #[test]
    fn set_overrides_string() {
        let config = load(&[], &["node_id=test-node".to_string()]).unwrap();
        assert_eq!(config.node_id, "test-node");
    }

    #[test]
    fn set_overrides_bool() {
        let config = load(&[], &["leios_enabled=true".to_string()]).unwrap();
        assert!(config.leios_enabled);
    }

    #[test]
    fn dynamic_config_from_node_config() {
        let config = NodeConfig::default();
        let dyn_config = config.dynamic_config();
        assert_eq!(
            dyn_config.rb_generation_probability,
            config.production.rb_generation_probability
        );
        assert_eq!(
            dyn_config.rb_body_validation_ms_constant,
            config.validation.rb_body_validation_ms_constant
        );
        assert_eq!(dyn_config.tx_rate, config.transactions.tx_rate);
    }

    // -- Committee selection tests --

    fn make_rng(seed: u64) -> rand::rngs::StdRng {
        use rand::SeedableRng;
        rand::rngs::StdRng::seed_from_u64(seed)
    }

    #[test]
    fn wfa_ls_persistent_voter_always_votes() {
        // persistent_stake_fraction = 0.3 → persistent if stake_frac >= 0.7
        let cs = CommitteeSelection::WfaLs {
            persistent_stake_fraction: 0.3,
        };
        let mut rng = make_rng(42);
        // stake=800/1000 = 0.8 >= 0.7 → always persistent
        for _ in 0..100 {
            assert_eq!(
                cs.decide_vote(800, 1000, 0.0, &mut rng),
                VoteDecision::PersistentVote
            );
        }
    }

    #[test]
    fn wfa_ls_non_persistent_sortition() {
        let cs = CommitteeSelection::WfaLs {
            persistent_stake_fraction: 0.3,
        };
        let mut rng = make_rng(42);
        // stake=100/1000 = 0.1, below 0.7 → not persistent.
        // vote_probability=1.0 → per_node = 1.0 * 0.1 = 0.1, so ~10% hit rate
        let hits: usize = (0..1000)
            .filter(|_| cs.decide_vote(100, 1000, 1.0, &mut rng) == VoteDecision::NonPersistentVote)
            .count();
        // Expected ~100, allow wide margin.
        assert!(hits > 50 && hits < 200, "hits={hits}, expected ~100");
    }

    #[test]
    fn wfa_ls_zero_stake_no_vote() {
        let cs = CommitteeSelection::WfaLs {
            persistent_stake_fraction: 0.3,
        };
        let mut rng = make_rng(42);
        assert_eq!(cs.decide_vote(0, 1000, 1.0, &mut rng), VoteDecision::NoVote);
    }

    #[test]
    fn everyone_votes_with_stake() {
        let cs = CommitteeSelection::EveryoneVotes;
        let mut rng = make_rng(42);
        assert_eq!(
            cs.decide_vote(1, 1000, 0.0, &mut rng),
            VoteDecision::PersistentVote
        );
    }

    #[test]
    fn everyone_votes_zero_stake() {
        let cs = CommitteeSelection::EveryoneVotes;
        let mut rng = make_rng(42);
        assert_eq!(cs.decide_vote(0, 1000, 0.0, &mut rng), VoteDecision::NoVote);
    }

    #[test]
    fn centile_high_includes_most() {
        let cs = CommitteeSelection::StakeCentile {
            top_centile_of_stake: 0.95,
        };
        let mut rng = make_rng(42);
        let hits: usize = (0..1000)
            .filter(|_| cs.decide_vote(100, 1000, 0.0, &mut rng) == VoteDecision::PersistentVote)
            .count();
        // Expected ~950, allow ±5%.
        assert!(hits > 900 && hits < 990, "hits={hits}, expected ~950");
    }

    #[test]
    fn centile_low_excludes_more() {
        let cs = CommitteeSelection::StakeCentile {
            top_centile_of_stake: 0.5,
        };
        let mut rng = make_rng(42);
        let hits: usize = (0..1000)
            .filter(|_| cs.decide_vote(100, 1000, 0.0, &mut rng) == VoteDecision::PersistentVote)
            .count();
        // Expected ~500, allow ±10%.
        assert!(hits > 400 && hits < 600, "hits={hits}, expected ~500");
    }

    #[test]
    fn committee_selection_toml_roundtrip() {
        // WfaLs
        let cs = CommitteeSelection::WfaLs {
            persistent_stake_fraction: 0.4,
        };
        let toml = toml::to_string(&cs).unwrap();
        let parsed: CommitteeSelection = toml::from_str(&toml).unwrap();
        assert!(matches!(
            parsed,
            CommitteeSelection::WfaLs {
                persistent_stake_fraction
            } if (persistent_stake_fraction - 0.4).abs() < f64::EPSILON
        ));

        // EveryoneVotes
        let cs = CommitteeSelection::EveryoneVotes;
        let toml = toml::to_string(&cs).unwrap();
        let parsed: CommitteeSelection = toml::from_str(&toml).unwrap();
        assert!(matches!(parsed, CommitteeSelection::EveryoneVotes));

        // StakeCentile
        let cs = CommitteeSelection::StakeCentile {
            top_centile_of_stake: 0.9,
        };
        let toml = toml::to_string(&cs).unwrap();
        let parsed: CommitteeSelection = toml::from_str(&toml).unwrap();
        assert!(matches!(
            parsed,
            CommitteeSelection::StakeCentile {
                top_centile_of_stake
            } if (top_centile_of_stake - 0.9).abs() < f64::EPSILON
        ));
    }

    #[test]
    fn production_config_default_has_new_fields() {
        let config = ProductionConfig::default();
        assert!(matches!(
            config.committee_selection,
            CommitteeSelection::WfaLs { .. }
        ));
        assert_eq!(config.persistent_vote_bytes, 130);
        assert_eq!(config.non_persistent_vote_bytes, 180);
        assert!((config.quorum_stake_fraction - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    fn dynamic_config_partial_update() {
        let mut dyn_config = NodeConfig::default().dynamic_config();
        let original_rb_body = dyn_config.rb_body_validation_ms_constant;

        let update = DynamicConfigUpdate {
            rb_generation_probability: Some(0.99),
            ..Default::default()
        };
        dyn_config.apply_update(&update);

        assert_eq!(dyn_config.rb_generation_probability, 0.99);
        // Unchanged fields remain the same.
        assert_eq!(dyn_config.rb_body_validation_ms_constant, original_rb_body);
    }
}
