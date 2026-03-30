//! Shared types for telemetry ingestion.
//!
//! Mirror types from net-node's telemetry module, with Deserialize support.
//! Events are kept as opaque `serde_json::Value` to avoid coupling to the
//! full NodeEvent enum.

use serde::{Deserialize, Serialize};

/// Stats snapshot received from a net-node instance.
///
/// Mirrors `net_node::telemetry::StatsSnapshot` with Deserialize.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StatsSnapshot {
    pub node_id: String,
    pub uptime_secs: f64,
    pub slot: u64,
    pub tip_block_no: Option<u64>,
    pub blocks_produced: u64,
    pub blocks_received: u64,
    pub blocks_validated: u64,
    pub txs_generated: u64,
    pub peer_count: usize,
    pub peers: Vec<PeerStatsEntry>,
}

/// Per-peer stats entry within a stats snapshot.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PeerStatsEntry {
    pub peer_id: String,
    pub address: String,
    pub mode: String,
    pub rtt_ms: Option<f64>,
    pub tip_block_no: Option<u64>,
    pub inbound_delay_ms: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
}

/// An ingested event with extracted metadata for aggregation.
pub struct IngestedEvent {
    /// Timestamp from the event's `time_s` field.
    pub time_s: f64,
    /// Node ID extracted from the event's `message.node` field.
    pub node_id: String,
    /// The full event as opaque JSON (written to JSONL output as-is).
    pub raw: serde_json::Value,
}

/// Extract `time_s` and `message.node` from a raw OutputEvent JSON value.
///
/// Returns `None` if the required fields are missing or malformed.
pub fn parse_event(value: serde_json::Value) -> Option<IngestedEvent> {
    let time_s = value.get("time_s")?.as_f64()?;
    let node_id = value
        .get("message")
        .and_then(|m| m.get("node"))
        .and_then(|n| n.as_str())
        .unwrap_or("unknown")
        .to_string();
    Some(IngestedEvent {
        time_s,
        node_id,
        raw: value,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_event() {
        let json = serde_json::json!({
            "time_s": 1.5,
            "message": {"type": "Slot", "node": "node-0", "slot": 42}
        });
        let event = parse_event(json).unwrap();
        assert!((event.time_s - 1.5).abs() < f64::EPSILON);
        assert_eq!(event.node_id, "node-0");
    }

    #[test]
    fn test_parse_event_missing_node() {
        let json = serde_json::json!({
            "time_s": 2.0,
            "message": {"type": "Something"}
        });
        let event = parse_event(json).unwrap();
        assert_eq!(event.node_id, "unknown");
    }

    #[test]
    fn test_parse_event_missing_time() {
        let json = serde_json::json!({"message": {"type": "Slot"}});
        assert!(parse_event(json).is_none());
    }

    #[test]
    fn test_stats_deserialize() {
        let json = serde_json::json!({
            "node_id": "node-0",
            "uptime_secs": 10.0,
            "slot": 100,
            "tip_block_no": 5,
            "blocks_produced": 1,
            "blocks_received": 3,
            "blocks_validated": 2,
            "txs_generated": 10,
            "peer_count": 1,
            "peers": [{
                "peer_id": "peer-1",
                "address": "127.0.0.1:30001",
                "mode": "Duplex",
                "rtt_ms": 5.0,
                "tip_block_no": 4,
                "inbound_delay_ms": 50,
                "bytes_sent": 1024,
                "bytes_received": 2048
            }]
        });
        let stats: StatsSnapshot = serde_json::from_value(json).unwrap();
        assert_eq!(stats.node_id, "node-0");
        assert_eq!(stats.peers.len(), 1);
        assert_eq!(stats.peers[0].bytes_sent, 1024);
    }
}
