//! TOML-based cluster configuration with figment loading.

use figment::providers::{Format, Serialized, Toml};
use figment::Figment;
use serde::{Deserialize, Serialize};

/// External peer to inject into random cluster nodes.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ExternalPeerConfig {
    /// Address of the external peer (e.g. "relay.example.com:3001").
    pub address: String,

    /// How many random cluster nodes should get this peer.
    #[serde(default = "default_inject_count")]
    pub inject_into_nodes: usize,
}

fn default_inject_count() -> usize {
    1
}

/// Subset of ClusterConfig controllable via the REST API.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ClusterControlConfig {
    pub num_nodes: Option<usize>,
    pub degree: Option<usize>,
    pub min_latency_ms: Option<u64>,
    pub max_latency_ms: Option<u64>,
    pub seed: Option<u64>,
    /// Node-level config overrides written into each node's overlay TOML.
    /// Keys are dotted TOML paths (e.g. "production.rb_generation_probability").
    #[serde(default)]
    pub node_config: std::collections::HashMap<String, serde_json::Value>,
}

/// Top-level cluster configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ClusterConfig {
    /// Number of net-node instances to spawn.
    pub num_nodes: usize,

    /// Target number of peers per node.
    #[serde(default = "default_degree")]
    pub degree: usize,

    /// Minimum simulated link latency (ms).
    #[serde(default = "default_min_latency")]
    pub min_latency_ms: u64,

    /// Maximum simulated link latency (ms).
    #[serde(default = "default_max_latency")]
    pub max_latency_ms: u64,

    /// Path to the base net-node config (e.g. "net-node/configs/mainnet.toml").
    pub base_config: String,

    /// First port for node allocation (node i gets base_port + i).
    #[serde(default = "default_base_port")]
    pub base_port: u16,

    /// PRNG seed for reproducible topology. Optional.
    pub seed: Option<u64>,

    /// Path for merged event JSONL output.
    #[serde(default = "default_output_events")]
    pub output_events: String,

    /// Time window (seconds) for cross-node event ordering.
    #[serde(default = "default_ordering_window")]
    pub ordering_window_secs: f64,

    /// Port for the telemetry aggregator HTTP server.
    #[serde(default = "default_aggregator_port")]
    pub aggregator_port: u16,

    /// Stake distribution strategy ("equal").
    #[serde(default = "default_stake_distribution")]
    pub stake_distribution: String,

    /// How often nodes should report stats (seconds).
    #[serde(default = "default_stats_interval")]
    pub stats_interval_secs: u64,

    /// Maximum number of recent events kept in memory for the UI API.
    #[serde(default = "default_event_window_size")]
    pub event_window_size: usize,

    /// Override rb_generation_probability for all nodes.
    pub rb_generation_probability: Option<f64>,

    /// External peers injected into random nodes.
    #[serde(default)]
    pub external_peers: Vec<ExternalPeerConfig>,
}

fn default_degree() -> usize {
    3
}
fn default_min_latency() -> u64 {
    5
}
fn default_max_latency() -> u64 {
    300
}
fn default_base_port() -> u16 {
    30000
}
fn default_output_events() -> String {
    "cluster-events.jsonl".to_string()
}
fn default_ordering_window() -> f64 {
    5.0
}
fn default_aggregator_port() -> u16 {
    9100
}
fn default_stake_distribution() -> String {
    "equal".to_string()
}
fn default_event_window_size() -> usize {
    10000
}
fn default_stats_interval() -> u64 {
    5
}

impl Default for ClusterConfig {
    fn default() -> Self {
        Self {
            num_nodes: 5,
            degree: default_degree(),
            min_latency_ms: default_min_latency(),
            max_latency_ms: default_max_latency(),
            base_config: "net-node/configs/mainnet.toml".to_string(),
            base_port: default_base_port(),
            seed: None,
            output_events: default_output_events(),
            ordering_window_secs: default_ordering_window(),
            aggregator_port: default_aggregator_port(),
            stake_distribution: default_stake_distribution(),
            stats_interval_secs: default_stats_interval(),
            event_window_size: default_event_window_size(),
            rb_generation_probability: None,
            external_peers: Vec::new(),
        }
    }
}

impl ClusterConfig {
    /// Apply optional overrides from a control config, returning a new config.
    pub fn with_overrides(
        &self,
        overrides: &ClusterControlConfig,
    ) -> Result<ClusterConfig, String> {
        let mut config = self.clone();
        if let Some(n) = overrides.num_nodes {
            config.num_nodes = n;
        }
        if let Some(d) = overrides.degree {
            config.degree = d;
        }
        if let Some(min) = overrides.min_latency_ms {
            config.min_latency_ms = min;
        }
        if let Some(max) = overrides.max_latency_ms {
            config.max_latency_ms = max;
        }
        if let Some(s) = overrides.seed {
            config.seed = Some(s);
        }
        if config.num_nodes == 0 {
            return Err("num_nodes must be at least 1".into());
        }
        if config.min_latency_ms > config.max_latency_ms {
            return Err("min_latency_ms must be <= max_latency_ms".into());
        }
        Ok(config)
    }

    /// Extract the controllable fields as a `ClusterControlConfig`.
    ///
    /// Reads initial node-level config values from the base config file.
    pub fn control_fields(&self) -> ClusterControlConfig {
        let mut node_config = read_node_config_defaults(&self.base_config);
        // If the cluster config has an explicit rb_generation_probability, it
        // overrides whatever was in the base config file.
        if let Some(p) = self.rb_generation_probability {
            node_config.insert(
                "production.rb_generation_probability".into(),
                serde_json::json!(p),
            );
        }
        ClusterControlConfig {
            num_nodes: Some(self.num_nodes),
            degree: Some(self.degree),
            min_latency_ms: Some(self.min_latency_ms),
            max_latency_ms: Some(self.max_latency_ms),
            seed: self.seed,
            node_config,
        }
    }
}

/// Load cluster configuration from a TOML file with optional --set overrides.
pub fn load(
    config_file: &str,
    set_overrides: &[String],
) -> Result<ClusterConfig, Box<dyn std::error::Error + Send + Sync>> {
    let mut figment = Figment::from(Serialized::defaults(ClusterConfig::default()))
        .merge(Toml::file(config_file));

    for override_str in set_overrides {
        let toml_fragment = set_override_to_toml(override_str)?;
        figment = figment.merge(Toml::string(&toml_fragment));
    }

    let config: ClusterConfig = figment.extract()?;

    if config.num_nodes == 0 {
        return Err("num_nodes must be at least 1".into());
    }
    if config.min_latency_ms > config.max_latency_ms {
        return Err("min_latency_ms must be <= max_latency_ms".into());
    }

    Ok(config)
}

/// Read node-level config defaults from the base net-node config file.
///
/// Extracts known controllable values so the UI can show current defaults.
fn read_node_config_defaults(
    base_config: &str,
) -> std::collections::HashMap<String, serde_json::Value> {
    let mut map = std::collections::HashMap::new();
    let Ok(content) = std::fs::read_to_string(base_config) else {
        return map;
    };
    let Ok(table) = content.parse::<toml::Value>() else {
        return map;
    };
    if let Some(production) = table.get("production") {
        if let Some(v) = production
            .get("rb_generation_probability")
            .and_then(|v| v.as_float())
        {
            map.insert(
                "production.rb_generation_probability".into(),
                serde_json::json!(v),
            );
        }
    }
    if let Some(validation) = table.get("validation") {
        if let Some(v) = validation
            .get("rb_body_validation_ms_constant")
            .and_then(|v| v.as_float())
        {
            map.insert(
                "validation.rb_body_validation_ms_constant".into(),
                serde_json::json!(v),
            );
        }
    }
    map
}

/// Convert "key=value" to a TOML fragment string.
fn set_override_to_toml(s: &str) -> Result<String, Box<dyn std::error::Error + Send + Sync>> {
    let (key, value) = s
        .split_once('=')
        .ok_or_else(|| format!("invalid --set format (expected key=value): {s}"))?;
    // Try to parse as a number or boolean first; otherwise quote as string.
    if value.parse::<i64>().is_ok()
        || value.parse::<f64>().is_ok()
        || value == "true"
        || value == "false"
    {
        Ok(format!("{key} = {value}"))
    } else {
        Ok(format!("{key} = \"{value}\""))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn test_default_config() {
        let config = ClusterConfig::default();
        assert_eq!(config.num_nodes, 5);
        assert_eq!(config.degree, 3);
        assert_eq!(config.min_latency_ms, 5);
        assert_eq!(config.max_latency_ms, 300);
    }

    #[test]
    fn test_load_from_file() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test-cluster.toml");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(
            f,
            r#"
num_nodes = 8
degree = 4
base_config = "mainnet.toml"
seed = 123
"#
        )
        .unwrap();

        let config = load(path.to_str().unwrap(), &[]).unwrap();
        assert_eq!(config.num_nodes, 8);
        assert_eq!(config.degree, 4);
        assert_eq!(config.seed, Some(123));
        // Defaults should fill in the rest.
        assert_eq!(config.aggregator_port, 9100);
    }

    #[test]
    fn test_set_override() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test-cluster.toml");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(
            f,
            r#"
num_nodes = 3
base_config = "mainnet.toml"
"#
        )
        .unwrap();

        let config = load(path.to_str().unwrap(), &["num_nodes=10".to_string()]).unwrap();
        assert_eq!(config.num_nodes, 10);
    }

    #[test]
    fn test_validation_errors() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test-cluster.toml");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(
            f,
            r#"
num_nodes = 0
base_config = "mainnet.toml"
"#
        )
        .unwrap();

        let result = load(path.to_str().unwrap(), &[]);
        assert!(result.is_err());
    }
}
