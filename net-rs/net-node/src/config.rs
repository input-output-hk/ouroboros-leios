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

    /// Outbound peer list.
    #[serde(default)]
    pub peers: Vec<PeerConfig>,
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
