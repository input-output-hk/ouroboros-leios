//! TOML-based cluster configuration with figment loading.

use figment::providers::{Format, Toml};
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
///
/// `topology_source` selects the topology mode (`"random"` or `"yaml"`), and
/// `topology_random` / `topology_yaml` carry that mode's parameters.  Each is
/// optional: a field left `None` leaves the cluster's current value untouched.
/// In practice the UI sends `topology_source = "random"` together with a fresh
/// `topology_random` when restarting a random cluster, and omits all three in
/// YAML mode (the cluster restarts with whatever YAML it loaded at startup).
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ClusterControlConfig {
    /// Which topology mode to switch to.  `None` leaves it unchanged.
    #[serde(default)]
    pub topology_source: Option<TopologySource>,
    /// Replacement random-mode parameters.  `None` leaves them unchanged.
    #[serde(default)]
    pub topology_random: Option<RandomTopologyConfig>,
    /// Replacement YAML-mode parameters.  `None` leaves them unchanged.
    #[serde(default)]
    pub topology_yaml: Option<YamlTopologyConfig>,
    #[serde(default)]
    pub seed: Option<u64>,
    /// Node-level config overrides written into each node's overlay TOML.
    /// Keys are dotted TOML paths (e.g. "production.rb_generation_probability").
    #[serde(default)]
    pub node_config: std::collections::HashMap<String, serde_json::Value>,
}

/// Which topology mode the cluster runs in.
///
/// Selected by the top-level scalar `topology_source = "random" | "yaml"`.
/// The mode-specific parameters live in the always-present `[topology_random]`
/// and `[topology_yaml]` sections (see [`ClusterConfig`]); only the section
/// matching the selected mode is read.  Defaults to [`TopologySource::Random`]
/// (the historical behaviour) so existing configs that don't mention
/// `topology_source` keep generating a random graph.
///
/// Selecting [`TopologySource::Yaml`] loads `data/simulation/pseudo-mainnet/
/// topology-v*.yaml`-style files (same schema as sim-rs and topology-checker).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum TopologySource {
    /// Generate a random connected graph from `[topology_random]`.
    #[default]
    Random,
    /// Load a YAML topology from `[topology_yaml]`.
    Yaml,
}

/// Parameters for [`TopologySource::Random`] (the `[topology_random]` section).
///
/// `deny_unknown_fields` rejects typos and stray keys within the section.
/// The section is always present in the config (with per-field defaults), so a
/// YAML-mode config can omit it entirely; conversely, leaving a populated
/// `[topology_random]` section while in YAML mode is silently ignored.
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct RandomTopologyConfig {
    /// Number of net-node instances to spawn.
    #[serde(default = "default_num_nodes")]
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
    /// Stake distribution strategy ("equal", "mainnet-shaped").
    #[serde(default = "default_stake_distribution")]
    pub stake_distribution: String,
}

impl Default for RandomTopologyConfig {
    fn default() -> Self {
        Self {
            num_nodes: default_num_nodes(),
            degree: default_degree(),
            min_latency_ms: default_min_latency(),
            max_latency_ms: default_max_latency(),
            stake_distribution: default_stake_distribution(),
        }
    }
}

/// Parameters for [`TopologySource::Yaml`] (the `[topology_yaml]` section).
///
/// `path` defaults to the empty string so a random-mode config need not
/// declare the section; `load` rejects an empty `path` when the selected mode
/// is YAML.  `deny_unknown_fields` rejects stray keys within the section.
#[derive(Debug, Clone, Default, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct YamlTopologyConfig {
    /// Path to the YAML topology (v3/v4 schema), interpreted relative to the
    /// process's current directory at startup.
    #[serde(default)]
    pub path: String,
    /// Optional cap: load only the first `node_limit` nodes from the YAML (in
    /// YAML insertion order; the v4 generator orders by stake-rank descending,
    /// so this is effectively top-N by stake).  `None` loads every node —
    /// beware, v4-mainnet has 2,685 nodes with a dense peer graph, which is
    /// impractical for a local process-per-node cluster.
    #[serde(default)]
    pub node_limit: Option<usize>,
}

/// Top-level cluster configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ClusterConfig {
    /// Which topology mode to run (`"random"` or `"yaml"`).  See
    /// [`TopologySource`].  Parameters live in `topology_random` /
    /// `topology_yaml`; only the section matching this mode is read.
    #[serde(default)]
    pub topology_source: TopologySource,

    /// Random-mode parameters (`[topology_random]`).  See
    /// [`RandomTopologyConfig`].
    #[serde(default)]
    pub topology_random: RandomTopologyConfig,

    /// YAML-mode parameters (`[topology_yaml]`).  See [`YamlTopologyConfig`].
    #[serde(default)]
    pub topology_yaml: YamlTopologyConfig,

    /// Path to the base net-node config (e.g. "net-node/configs/mainnet.toml").
    pub base_config: String,

    /// First port for node allocation (node i gets base_port + i).
    #[serde(default = "default_base_port")]
    pub base_port: u16,

    /// PRNG seed for reproducible topology. Optional.
    #[serde(default)]
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

    /// How often nodes should report stats (seconds).
    #[serde(default = "default_stats_interval")]
    pub stats_interval_secs: u64,

    /// Maximum number of recent events kept in memory for the UI API.
    #[serde(default = "default_event_window_size")]
    pub event_window_size: usize,

    /// Override rb_generation_probability for all nodes.
    #[serde(default)]
    pub rb_generation_probability: Option<f64>,

    /// Override the per-node Poisson transaction generation rate
    /// (`[transactions] tx_rate`).  Useful for cluster scenarios that
    /// need to drive EB production without authoring a dedicated base
    /// config — e.g. abstention-pressure experiments where the cluster
    /// must keep the mempool busy enough to overflow into EBs.  When
    /// `None`, the base config's value is used (`mainnet.toml` defaults
    /// to `0.0` = no generation).
    #[serde(default)]
    pub tx_rate: Option<f64>,

    /// Per-node adversarial / experimental behaviour.  See
    /// `shared_consensus::behaviour::BehaviourSpec` for the catalogue.
    /// When set, the nodes selected by [`Self::behaviour_selection`]
    /// are started with this behaviour; the remaining nodes stay
    /// honest.
    #[serde(default)]
    pub behaviour: Option<shared_consensus::behaviour::BehaviourSpec>,

    /// Which nodes should run [`Self::behaviour`].  See
    /// [`BehaviourSelection`] for the variants.  When `None` and
    /// `behaviour` is set, no node runs the behaviour (use
    /// `{ kind = "all" }` to attach it everywhere).
    #[serde(default)]
    pub behaviour_selection: Option<BehaviourSelection>,

    /// External peers injected into random nodes.
    #[serde(default)]
    pub external_peers: Vec<ExternalPeerConfig>,
}

fn default_num_nodes() -> usize {
    5
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
            base_config: "net-node/configs/mainnet.toml".to_string(),
            base_port: default_base_port(),
            seed: None,
            output_events: default_output_events(),
            ordering_window_secs: default_ordering_window(),
            aggregator_port: default_aggregator_port(),
            stats_interval_secs: default_stats_interval(),
            event_window_size: default_event_window_size(),
            rb_generation_probability: None,
            tx_rate: None,
            behaviour: None,
            behaviour_selection: None,
            external_peers: Vec::new(),
            topology_source: TopologySource::default(),
            topology_random: RandomTopologyConfig::default(),
            topology_yaml: YamlTopologyConfig::default(),
        }
    }
}

/// Which subset of nodes runs the cluster's configured behaviour.
///
/// Serialised as a tagged TOML table:
///
/// ```toml
/// [behaviour_selection]
/// kind = "stake-fraction"
/// fraction = 0.2
/// ```
///
/// All variants are deterministic for a given [`ClusterConfig::seed`]
/// so re-runs land on the same nodes.  Stake-aware variants ignore
/// zero-stake nodes (i.e. relays under `mainnet-shaped`).
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum BehaviourSelection {
    /// Attach the behaviour to every node in the cluster.
    All,
    /// Attach the behaviour to a hand-listed set of node indices.
    Nodes {
        #[serde(default)]
        indices: Vec<usize>,
    },
    /// Pick `count` random nodes (deterministically, seeded from
    /// [`ClusterConfig::seed`]) from those with `stake > 0`.  Useful
    /// for "this many adversaries somewhere in the voting set" without
    /// concentrating on the largest pools.
    StakeRandom { count: usize },
    /// Pick `count` nodes from those with `stake > 0`, ordered by
    /// stake descending and tie-broken by index ascending.  Targets
    /// the largest pools first.
    StakeOrdered { count: usize },
    /// Pick the smallest prefix of stake-bearing nodes (ordered by
    /// stake descending, tie-broken by index ascending) whose
    /// cumulative stake covers `fraction` of the total cluster stake.
    /// This is the same shape as CIP-0164 top-stake committee
    /// selection (`top_centile_of_stake`) and is the right knob for
    /// abstention-pressure experiments — `fraction = 0.2` makes 20%
    /// of the *voting weight* run the behaviour, regardless of how
    /// many nodes that turns out to be.
    StakeFraction { fraction: f64 },
}

/// Request payload for `POST /api/attack`: which behaviour to install
/// and which nodes to install it on.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct AttackRequest {
    pub behaviour: shared_consensus::behaviour::BehaviourSpec,
    pub selection: BehaviourSelection,
}

/// State of the cluster's currently-active runtime attack, surfaced to
/// the UI via `GET /api/attack`.  `indices` is the resolved set of
/// node indices the attack applies to so the UI can highlight them
/// without re-running selection logic.  `started_at_s` is seconds
/// since UNIX epoch — same convention as event timestamps.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ActiveAttack {
    pub behaviour: shared_consensus::behaviour::BehaviourSpec,
    pub selection: BehaviourSelection,
    pub indices: Vec<usize>,
    pub started_at_s: f64,
}

impl ClusterConfig {
    /// Apply optional overrides from a control config, returning a new config.
    ///
    /// `topology_source` (when present) switches the mode; `topology_random` /
    /// `topology_yaml` (when present) replace that mode's parameters wholesale.
    /// There's no per-field merge, so a caller can't mix modes by overriding a
    /// single random knob on a YAML-backed cluster.
    pub fn with_overrides(
        &self,
        overrides: &ClusterControlConfig,
    ) -> Result<ClusterConfig, String> {
        let mut config = self.clone();
        if let Some(kind) = overrides.topology_source {
            config.topology_source = kind;
        }
        if let Some(random) = &overrides.topology_random {
            config.topology_random = random.clone();
        }
        if let Some(yaml) = &overrides.topology_yaml {
            config.topology_yaml = yaml.clone();
        }
        if let Some(s) = overrides.seed {
            config.seed = Some(s);
        }
        if config.topology_source == TopologySource::Random {
            let random = &config.topology_random;
            if random.num_nodes == 0 {
                return Err("num_nodes must be at least 1".into());
            }
            if random.min_latency_ms > random.max_latency_ms {
                return Err("min_latency_ms must be <= max_latency_ms".into());
            }
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
        // Same pattern for `[transactions] tx_rate`: when the cluster
        // config sets it, it overrides whatever the base config has.
        if let Some(r) = self.tx_rate {
            node_config.insert("transactions.tx_rate".into(), serde_json::json!(r));
        }
        ClusterControlConfig {
            topology_source: Some(self.topology_source),
            topology_random: Some(self.topology_random.clone()),
            topology_yaml: Some(self.topology_yaml.clone()),
            seed: self.seed,
            node_config,
        }
    }
}

/// Load cluster configuration from a TOML file with optional --set overrides.
///
/// Every field with a default declares it via `#[serde(default = "...")]`, so
/// figment only needs to carry the user-supplied TOML and any `--set`
/// overrides — we don't seed `ClusterConfig::default()` as a base layer.
pub fn load(
    config_file: &str,
    set_overrides: &[String],
) -> Result<ClusterConfig, Box<dyn std::error::Error + Send + Sync>> {
    let mut figment = Figment::from(Toml::file(config_file));

    for override_str in set_overrides {
        let toml_fragment = set_override_to_toml(override_str)?;
        figment = figment.merge(Toml::string(&toml_fragment));
    }

    let config: ClusterConfig = figment.extract()?;

    // Mode-specific validation.  Only the selected mode's section is checked;
    // the other section is ignored even if populated.
    match config.topology_source {
        TopologySource::Random => {
            let random = &config.topology_random;
            if random.num_nodes == 0 {
                return Err("num_nodes must be at least 1".into());
            }
            if random.min_latency_ms > random.max_latency_ms {
                return Err("min_latency_ms must be <= max_latency_ms".into());
            }
        }
        TopologySource::Yaml => {
            if config.topology_yaml.path.is_empty() {
                return Err(
                    "topology_yaml.path must be set when topology_source = \"yaml\"".into(),
                );
            }
        }
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
    if let Some(transactions) = table.get("transactions") {
        if let Some(v) = transactions.get("tx_rate").and_then(|v| v.as_float()) {
            map.insert("transactions.tx_rate".into(), serde_json::json!(v));
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
        assert_eq!(config.topology_source, TopologySource::Random);
        let random = &config.topology_random;
        assert_eq!(random.num_nodes, 5);
        assert_eq!(random.degree, 3);
        assert_eq!(random.min_latency_ms, 5);
        assert_eq!(random.max_latency_ms, 300);
        assert_eq!(random.stake_distribution, "equal");
    }

    /// Smallest valid config: just `base_config`.  Every other top-level
    /// field has to have a serde default, otherwise the user will hit a
    /// "missing field `X`" error the moment they trim their config.  This
    /// test pins that contract explicitly so it can't regress silently
    /// (e.g. by someone adding a new required field without realising).
    #[test]
    fn test_load_minimal_config() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("minimal.toml");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(f, r#"base_config = "mainnet.toml""#).unwrap();

        let config = load(path.to_str().unwrap(), &[]).expect("minimal config must load");

        // base_config is the only field the user wrote — everything else
        // must come from defaults.
        assert_eq!(config.base_config, "mainnet.toml");
        assert_eq!(config.base_port, 30000);
        assert_eq!(config.aggregator_port, 9100);
        assert!(config.seed.is_none());
        assert!(config.rb_generation_probability.is_none());
        assert!(config.tx_rate.is_none());
        assert!(config.behaviour.is_none());
        assert!(config.behaviour_selection.is_none());
        assert!(config.external_peers.is_empty());

        // topology_source defaults to Random with the [topology_random]
        // section's fields at their per-field defaults.
        assert_eq!(config.topology_source, TopologySource::Random);
        let random = &config.topology_random;
        assert_eq!(random.num_nodes, 5);
        assert_eq!(random.degree, 3);
        assert_eq!(random.min_latency_ms, 5);
        assert_eq!(random.max_latency_ms, 300);
        assert_eq!(random.stake_distribution, "equal");
    }

    #[test]
    fn test_load_from_file() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test-cluster.toml");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(
            f,
            r#"
base_config = "mainnet.toml"
seed = 123
topology_source = "random"

[topology_random]
num_nodes = 8
degree = 4
"#
        )
        .unwrap();

        let config = load(path.to_str().unwrap(), &[]).unwrap();
        assert_eq!(config.topology_source, TopologySource::Random);
        assert_eq!(config.topology_random.num_nodes, 8);
        assert_eq!(config.topology_random.degree, 4);
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
base_config = "mainnet.toml"
topology_source = "random"

[topology_random]
num_nodes = 3
"#
        )
        .unwrap();

        // --set drills into the [topology_random] table by dotted key.
        let config = load(
            path.to_str().unwrap(),
            &["topology_random.num_nodes=10".to_string()],
        )
        .unwrap();
        assert_eq!(config.topology_random.num_nodes, 10);
    }

    #[test]
    fn test_validation_errors() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("test-cluster.toml");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(
            f,
            r#"
base_config = "mainnet.toml"
topology_source = "random"

[topology_random]
num_nodes = 0
"#
        )
        .unwrap();

        let result = load(path.to_str().unwrap(), &[]);
        assert!(result.is_err());
    }

    #[test]
    fn test_yaml_section_rejects_unknown_fields() {
        // `deny_unknown_fields` on YamlTopologyConfig still catches typos and
        // stray keys: `degree` is meaningless in [topology_yaml], so the parse
        // must fail rather than silently ignore it.
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("bad.toml");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(
            f,
            r#"
base_config = "mainnet.toml"
topology_source = "yaml"

[topology_yaml]
path = "topology.yaml"
degree = 7
"#
        )
        .unwrap();

        let err = load(path.to_str().unwrap(), &[]).unwrap_err();
        let msg = err.to_string();
        assert!(
            msg.contains("degree") || msg.contains("unknown field"),
            "expected unknown-field error mentioning 'degree', got: {msg}"
        );
    }

    #[test]
    fn test_random_section_rejects_unknown_fields() {
        // Symmetric: `path` is meaningless in [topology_random].
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("bad.toml");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(
            f,
            r#"
base_config = "mainnet.toml"
topology_source = "random"

[topology_random]
num_nodes = 5
path = "topology.yaml"
"#
        )
        .unwrap();

        let err = load(path.to_str().unwrap(), &[]).unwrap_err();
        let msg = err.to_string();
        assert!(
            msg.contains("path") || msg.contains("unknown field"),
            "expected unknown-field error mentioning 'path', got: {msg}"
        );
    }

    #[test]
    fn test_unused_section_is_ignored() {
        // Accepted tradeoff of the flat layout: a fully-valid but unused
        // section is silently ignored.  Here YAML mode is selected, but a
        // populated [topology_random] section is present — it must not cause
        // an error, and the YAML path must still take effect.
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("mixed.toml");
        let mut f = std::fs::File::create(&path).unwrap();
        writeln!(
            f,
            r#"
base_config = "mainnet.toml"
topology_source = "yaml"

[topology_random]
num_nodes = 99
degree = 7

[topology_yaml]
path = "topology.yaml"
"#
        )
        .unwrap();

        let config = load(path.to_str().unwrap(), &[]).expect("unused section is ignored");
        assert_eq!(config.topology_source, TopologySource::Yaml);
        assert_eq!(config.topology_yaml.path, "topology.yaml");
    }
}
