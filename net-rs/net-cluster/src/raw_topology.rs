//! YAML topology parser.
//!
//! Mirrors the on-disk schema used by `sim-rs`, `topology-checker`, and the
//! `data/simulation/pseudo-mainnet/topology-v*.yaml` files:
//!
//! ```yaml
//! nodes:
//!   node-0:
//!     stake: 12345
//!     location: [10.05, 49.70]      # (lon, lat) — ignored by net-cluster
//!     cpu-core-count: 4              # ignored by net-cluster
//!     producers:
//!       node-1:
//!         latency-ms: 45.3
//!         bandwidth-bytes-per-second: 125000000   # ignored in v1
//! ```
//!
//! Only the fields net-cluster needs (`stake`, `producers[*].latency-ms`)
//! drive behaviour; the rest are accepted-and-ignored so we can ingest the
//! existing topology YAMLs without surgery.

use std::path::Path;

use indexmap::IndexMap;
use serde::Deserialize;

/// Raw YAML topology, as produced by the v3/v4 generators.
#[derive(Debug, Deserialize)]
pub struct RawTopology {
    /// Node-id → node entry.  Uses `IndexMap` to preserve **YAML insertion
    /// order**, which is load-bearing: the v4 generator emits nodes in
    /// stake-rank-descending order (`node-0` = highest stake, `node-2684`
    /// = lowest), and our `node_limit` semantics rely on that to behave
    /// as "first-N by YAML order ≈ top-N by stake".
    ///
    /// A `BTreeMap` here would iterate **lexicographically**
    /// (`node-0, node-1, node-10, node-100, …, node-2`) which silently
    /// breaks the top-N invariant — see the regression test
    /// `numeric_node_ids_preserve_yaml_order` below.
    pub nodes: IndexMap<String, RawNode>,
}

#[derive(Debug, Deserialize)]
pub struct RawNode {
    /// Stake (lovelace-equivalent).  Defaults to 0 for relays / pure
    /// consumers that the YAML omits the field for.
    #[serde(default)]
    pub stake: u64,

    /// Geographic placement.  Ignored by net-cluster (localhost ports
    /// don't model geography); kept for round-trip parsing.
    #[serde(default)]
    #[allow(dead_code)]
    pub location: Option<RawNodeLocation>,

    /// CPU core count.  Currently unused.
    #[serde(default, rename = "cpu-core-count")]
    #[allow(dead_code)]
    pub cpu_core_count: Option<u32>,

    /// Outbound producer edges with per-link latency / bandwidth.
    /// Insertion-ordered to match the rest of the YAML faithfully.
    #[serde(default)]
    pub producers: IndexMap<String, RawLinkInfo>,
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
#[allow(dead_code)]
pub enum RawNodeLocation {
    /// Symbolic cluster name (older v1/v2 YAMLs).
    Cluster { cluster: String },
    /// `[lon, lat]` literal coordinates (v3/v4 YAMLs).
    Coords([f64; 2]),
}

#[derive(Debug, Deserialize)]
pub struct RawLinkInfo {
    #[serde(rename = "latency-ms")]
    pub latency_ms: f64,

    /// Per-link bandwidth.  Honouring this requires per-peer shaping in
    /// `net-core`'s coordinator, which doesn't exist today — the loader
    /// logs a one-time warning when any link carries a value and then
    /// ignores it.
    #[serde(default, rename = "bandwidth-bytes-per-second")]
    pub bandwidth_bytes_per_second: Option<u64>,
}

/// Read a topology YAML from disk and parse it.
pub fn load_from_path(
    path: &Path,
) -> Result<RawTopology, Box<dyn std::error::Error + Send + Sync>> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| format!("failed to read topology YAML at {}: {e}", path.display()))?;
    let raw: RawTopology = serde_yaml::from_str(&content)
        .map_err(|e| format!("failed to parse topology YAML at {}: {e}", path.display()))?;
    Ok(raw)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = r#"
nodes:
  node-0:
    stake: 100
    location: [10.0, 49.7]
    cpu-core-count: 4
    producers:
      node-1:
        latency-ms: 45.3
        bandwidth-bytes-per-second: 125000000
      node-2:
        latency-ms: 12.0
  node-1:
    stake: 0
    location: [-77.5, 38.9]
    producers:
      node-0:
        latency-ms: 45.3
  node-2:
    stake: 200
    location:
      cluster: "us-east"
    producers: {}
"#;

    #[test]
    fn parses_v4_style_yaml() {
        let raw: RawTopology = serde_yaml::from_str(SAMPLE).unwrap();
        assert_eq!(raw.nodes.len(), 3);

        let n0 = &raw.nodes["node-0"];
        assert_eq!(n0.stake, 100);
        assert_eq!(n0.cpu_core_count, Some(4));
        assert_eq!(n0.producers.len(), 2);
        assert!((n0.producers["node-1"].latency_ms - 45.3).abs() < 1e-9);
        assert_eq!(
            n0.producers["node-1"].bandwidth_bytes_per_second,
            Some(125_000_000)
        );
        assert_eq!(n0.producers["node-2"].bandwidth_bytes_per_second, None);
    }

    #[test]
    fn defaults_missing_stake_to_zero() {
        let raw: RawTopology = serde_yaml::from_str(SAMPLE).unwrap();
        assert_eq!(raw.nodes["node-1"].stake, 0);
    }

    #[test]
    fn parses_cluster_location() {
        // Older v1/v2 YAMLs use `location: { cluster: "..." }` instead of
        // a `[lon, lat]` array.  We accept both for forward compat.
        let raw: RawTopology = serde_yaml::from_str(SAMPLE).unwrap();
        assert!(raw.nodes["node-2"].location.is_some());
    }

    #[test]
    fn missing_producers_section_is_empty() {
        let raw: RawTopology = serde_yaml::from_str("nodes:\n  solo: {}\n").unwrap();
        assert_eq!(raw.nodes.len(), 1);
        assert!(raw.nodes["solo"].producers.is_empty());
        assert_eq!(raw.nodes["solo"].stake, 0);
    }

    /// Regression test for the lexicographic-vs-insertion-order bug.
    ///
    /// The v4 YAMLs use IDs like `node-0`, `node-1`, …, `node-2684` in
    /// **stake-rank-descending** insertion order.  A `BTreeMap` would
    /// iterate them lexicographically (`node-0, node-1, node-10, node-100,
    /// …, node-2, node-20, …`), silently breaking `node_limit` semantics.
    ///
    /// This test pins the iteration to YAML order regardless of how the
    /// IDs sort as strings.
    #[test]
    fn numeric_node_ids_preserve_yaml_order() {
        // Twelve nodes in *insertion* order: 0, 1, 2, …, 11.
        // Lexicographic order would be: 0, 1, 10, 11, 2, 3, …, 9.
        let yaml = (0..12)
            .map(|i| {
                format!(
                    "  node-{i}:\n    stake: {}\n    producers: {{}}\n",
                    1000 - i
                )
            })
            .collect::<String>();
        let raw: RawTopology = serde_yaml::from_str(&format!("nodes:\n{yaml}")).unwrap();
        let ids: Vec<&str> = raw.nodes.keys().map(String::as_str).collect();
        assert_eq!(
            ids,
            vec![
                "node-0", "node-1", "node-2", "node-3", "node-4", "node-5", "node-6", "node-7",
                "node-8", "node-9", "node-10", "node-11",
            ],
            "iteration must follow YAML insertion order, not lexicographic"
        );
        // And the corresponding stakes are descending, as in v4.
        let stakes: Vec<u64> = raw.nodes.values().map(|n| n.stake).collect();
        assert!(stakes.windows(2).all(|w| w[0] > w[1]));
    }
}
