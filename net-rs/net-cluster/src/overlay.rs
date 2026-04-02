//! Per-node TOML overlay generation.
//!
//! Generates temporary TOML config files that overlay the base config with
//! per-node identity, peers, stake, and telemetry HTTP sinks.

use std::fmt::Write;
use std::path::{Path, PathBuf};

use std::collections::HashMap;

use crate::topology::{NodeTopology, Topology};

/// Generated overlay files, stored in a temp directory.
pub struct OverlayFiles {
    /// Directory containing the overlay files (used for cleanup).
    #[allow(dead_code)]
    pub dir: PathBuf,
    /// Paths to each node's overlay file, indexed by node index.
    pub paths: Vec<PathBuf>,
}

/// Generate overlay TOML files for all nodes in the topology.
///
/// Files are written to `{temp_dir}/node-{i}.toml`. The `aggregator_url`
/// is the base URL for the cluster's telemetry HTTP server.
pub fn generate_overlays(
    topology: &Topology,
    temp_dir: &Path,
    aggregator_port: u16,
    stats_interval_secs: u64,
    rb_generation_probability: Option<f64>,
    node_config: &HashMap<String, serde_json::Value>,
) -> Result<OverlayFiles, Box<dyn std::error::Error + Send + Sync>> {
    std::fs::create_dir_all(temp_dir)?;

    let mut paths = Vec::with_capacity(topology.nodes.len());

    for node in &topology.nodes {
        let toml_content = render_overlay(
            node,
            aggregator_port,
            stats_interval_secs,
            rb_generation_probability,
            node_config,
        );
        let path = temp_dir.join(format!("node-{}.toml", node.index));
        std::fs::write(&path, &toml_content)?;
        paths.push(path);
    }

    Ok(OverlayFiles {
        dir: temp_dir.to_path_buf(),
        paths,
    })
}

/// Render a single node's overlay TOML content.
fn render_overlay(
    node: &NodeTopology,
    aggregator_port: u16,
    stats_interval_secs: u64,
    rb_generation_probability: Option<f64>,
    node_config: &HashMap<String, serde_json::Value>,
) -> String {
    let mut s = String::new();

    writeln!(s, "node_id = \"{}\"", node.node_id).ok();
    writeln!(s, "listen_address = \"{}\"", node.listen_address).ok();
    writeln!(s, "seed = {}", node.seed).ok();
    writeln!(s).ok();
    writeln!(s, "[production]").ok();
    writeln!(s, "stake = {}", node.stake).ok();
    if let Some(p) = rb_generation_probability {
        writeln!(s, "rb_generation_probability = {p}").ok();
    }
    writeln!(s).ok();
    writeln!(s, "[telemetry]").ok();
    writeln!(s, "stats_interval_secs = {stats_interval_secs}").ok();
    writeln!(s).ok();
    writeln!(s, "[[telemetry.event_sinks]]").ok();
    writeln!(s, "type = \"http\"").ok();
    writeln!(s, "url = \"http://127.0.0.1:{aggregator_port}/events\"").ok();
    writeln!(s).ok();
    writeln!(s, "[[telemetry.stats_sinks]]").ok();
    writeln!(s, "type = \"http\"").ok();
    writeln!(s, "url = \"http://127.0.0.1:{aggregator_port}/stats\"").ok();

    // Node config overrides from the UI, grouped by TOML section.
    if !node_config.is_empty() {
        let mut sections: HashMap<&str, Vec<(&str, &serde_json::Value)>> = HashMap::new();
        for (key, value) in node_config {
            if let Some((section, field)) = key.split_once('.') {
                sections.entry(section).or_default().push((field, value));
            }
        }
        for (section, fields) in &sections {
            writeln!(s).ok();
            writeln!(s, "[{section}]").ok();
            for (field, value) in fields {
                match value {
                    serde_json::Value::Number(n) => {
                        writeln!(s, "{field} = {n}").ok();
                    }
                    serde_json::Value::Bool(b) => {
                        writeln!(s, "{field} = {b}").ok();
                    }
                    serde_json::Value::String(st) => {
                        writeln!(s, "{field} = \"{st}\"").ok();
                    }
                    _ => {}
                }
            }
        }
    }

    for peer in &node.peers {
        writeln!(s).ok();
        writeln!(s, "[[peers]]").ok();
        writeln!(s, "address = \"{}\"", peer.address).ok();
        if peer.inbound_delay_ms > 0 {
            writeln!(s, "inbound_delay_ms = {}", peer.inbound_delay_ms).ok();
        }
    }

    s
}

/// Clean up the overlay temp directory.
pub fn cleanup(dir: &Path) {
    if dir.exists() {
        if let Err(e) = std::fs::remove_dir_all(dir) {
            tracing::warn!("failed to clean up overlay dir {}: {e}", dir.display());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::topology::PeerLink;

    fn sample_node() -> NodeTopology {
        NodeTopology {
            index: 0,
            node_id: "node-0".to_string(),
            listen_address: "127.0.0.1:30000".to_string(),
            listen_port: 30000,
            stake: 500,
            seed: 42,
            peers: vec![
                PeerLink {
                    address: "127.0.0.1:30001".to_string(),
                    inbound_delay_ms: 50,
                },
                PeerLink {
                    address: "relay.example.com:3001".to_string(),
                    inbound_delay_ms: 0,
                },
            ],
        }
    }

    #[test]
    fn test_render_overlay() {
        let node = sample_node();
        let toml = render_overlay(&node, 9100, 5, None, &HashMap::new());

        assert!(toml.contains("node_id = \"node-0\""));
        assert!(toml.contains("listen_address = \"127.0.0.1:30000\""));
        assert!(toml.contains("seed = 42"));
        assert!(toml.contains("stake = 500"));
        assert!(toml.contains("http://127.0.0.1:9100/events"));
        assert!(toml.contains("http://127.0.0.1:9100/stats"));
        assert!(toml.contains("address = \"127.0.0.1:30001\""));
        assert!(toml.contains("inbound_delay_ms = 50"));
        assert!(toml.contains("address = \"relay.example.com:3001\""));
        // External peer with 0 delay should not have inbound_delay_ms.
        let relay_section = toml.split("relay.example.com").nth(1).unwrap();
        assert!(!relay_section.contains("inbound_delay_ms"));
    }

    #[test]
    fn test_render_parses_as_toml() {
        let node = sample_node();
        let toml_str = render_overlay(&node, 9100, 5, None, &HashMap::new());
        let parsed: toml::Value = toml::from_str(&toml_str).expect("generated TOML should parse");
        assert_eq!(parsed["node_id"].as_str(), Some("node-0"));
    }

    #[test]
    fn test_generate_overlays() {
        let topo = crate::topology::Topology {
            nodes: vec![sample_node()],
            edges: Vec::new(),
        };
        let dir = tempfile::tempdir().unwrap();
        let overlays =
            generate_overlays(&topo, dir.path(), 9100, 5, None, &HashMap::new()).unwrap();
        assert_eq!(overlays.paths.len(), 1);
        assert!(overlays.paths[0].exists());

        let content = std::fs::read_to_string(&overlays.paths[0]).unwrap();
        assert!(content.contains("node_id = \"node-0\""));
    }
}
