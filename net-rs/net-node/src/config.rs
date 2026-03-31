//! TOML-based configuration with layered loading via figment.
//!
//! Config files are loaded left-to-right via repeatable `--config` flags,
//! with later files overriding earlier ones. Individual values can be
//! overridden with `--set key=value`.

use std::collections::HashMap;

use figment::providers::{Format, Serialized, Toml};
use figment::Figment;
use serde::{Deserialize, Serialize};

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
    #[serde(default)]
    pub vote_generation_probability: f64,

    /// Leios stage length in slots.
    #[serde(default = "default_stage_length")]
    pub stage_length_slots: u64,
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

impl Default for ProductionConfig {
    fn default() -> Self {
        Self {
            stake: 0,
            total_stake: default_total_stake(),
            rb_generation_probability: default_rb_probability(),
            eb_generation_probability: 0.0,
            vote_generation_probability: 0.0,
            stage_length_slots: default_stage_length(),
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
}

fn default_tx_size_min() -> usize {
    250
}

fn default_tx_size_max() -> usize {
    16384
}

impl Default for TxConfig {
    fn default() -> Self {
        Self {
            tx_rate: 0.0,
            tx_size_min: default_tx_size_min(),
            tx_size_max: default_tx_size_max(),
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
    5.0
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
}
