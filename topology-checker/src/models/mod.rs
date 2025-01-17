use indexmap::IndexMap;
use serde::Deserialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error = 0,
}

#[derive(Debug, Clone)]
pub struct Issue {
    pub severity: Severity,
    pub node: String,
    pub message: String,
    pub suggestion: String,
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
#[allow(dead_code)]
pub enum Location {
    Cluster { cluster: Option<String> },
    Coordinates([f64; 2]),
}

#[derive(Debug, Deserialize)]
pub struct Producer {
    #[serde(rename = "latency-ms")]
    pub latency_ms: f64,
    #[serde(rename = "bandwidth-bytes-per-second")]
    #[serde(default)]
    #[allow(dead_code)]
    pub bandwidth_bytes_per_second: Option<u64>,
    #[serde(rename = "cpu-core-count")]
    #[serde(default)]
    #[allow(dead_code)]
    pub cpu_core_count: Option<u64>,
}

#[derive(Debug, Deserialize)]
pub struct Node {
    #[allow(dead_code)]
    pub location: Location,
    #[serde(default)]
    pub producers: IndexMap<String, Producer>,
    #[serde(default)]
    pub stake: u64,
}

#[derive(Debug, Deserialize)]
pub struct Topology {
    pub nodes: IndexMap<String, Node>,
}
impl Topology {
    #[allow(dead_code)]
    pub fn get_node_coordinates(&self, node_id: &str) -> Option<[f64; 2]> {
        match &self.nodes.get(node_id)?.location {
            Location::Coordinates(coords) => Some(*coords),
            Location::Cluster { .. } => None,
        }
    }
}
