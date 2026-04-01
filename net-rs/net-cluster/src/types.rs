//! Shared types for telemetry ingestion.
//!
//! Mirror types from net-node's telemetry module, with Deserialize support.
//! Events are kept as opaque `serde_json::Value` to avoid coupling to the
//! full NodeEvent enum.

use std::collections::VecDeque;

use serde::{Deserialize, Serialize};

/// A block entry in a chain tree snapshot, for UI display.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChainTreeEntry {
    pub block_number: u64,
    pub hash: String,
    pub prev_hash: Option<String>,
}

/// Stats snapshot received from a net-node instance.
///
/// Mirrors `net_node::telemetry::StatsSnapshot` with Deserialize.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StatsSnapshot {
    pub node_id: String,
    pub uptime_secs: f64,
    pub slot: u64,
    pub tip_block_no: Option<u64>,
    #[serde(default)]
    pub tip_hash: Option<String>,
    pub blocks_produced: u64,
    pub blocks_received: u64,
    pub blocks_validated: u64,
    pub txs_generated: u64,
    pub peer_count: usize,
    pub peers: Vec<PeerStatsEntry>,
    #[serde(default)]
    pub chain_tree: Vec<ChainTreeEntry>,
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

/// Ring buffer of recent events for the UI API.
///
/// Keeps up to `capacity` events ordered by insertion time. Events are
/// stored as opaque JSON values with their `time_s` for efficient filtering.
pub struct EventWindow {
    events: VecDeque<serde_json::Value>,
    capacity: usize,
}

impl EventWindow {
    pub fn new(capacity: usize) -> Self {
        Self {
            events: VecDeque::with_capacity(capacity.min(1024)),
            capacity,
        }
    }

    /// Push events into the window, evicting oldest if over capacity.
    pub fn push(&mut self, events: impl IntoIterator<Item = serde_json::Value>) {
        for event in events {
            if self.events.len() >= self.capacity {
                self.events.pop_front();
            }
            self.events.push_back(event);
        }
    }

    /// Return all events with `time_s > after`.
    pub fn events_after(&self, after: f64) -> Vec<serde_json::Value> {
        self.events
            .iter()
            .filter(|e| {
                e.get("time_s")
                    .and_then(|t| t.as_f64())
                    .is_some_and(|t| t > after)
            })
            .cloned()
            .collect()
    }

    /// Return all events in the window.
    #[cfg(test)]
    pub fn all_events(&self) -> Vec<serde_json::Value> {
        self.events.iter().cloned().collect()
    }
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
        // chain_tree defaults to empty when absent (backward compat).
        assert!(stats.chain_tree.is_empty());
    }

    #[test]
    fn test_stats_deserialize_with_chain_tree() {
        let json = serde_json::json!({
            "node_id": "node-0",
            "uptime_secs": 10.0,
            "slot": 100,
            "tip_block_no": 5,
            "blocks_produced": 1,
            "blocks_received": 3,
            "blocks_validated": 2,
            "txs_generated": 10,
            "peer_count": 0,
            "peers": [],
            "chain_tree": [
                {"block_number": 1, "hash": "a1b2", "prev_hash": null},
                {"block_number": 2, "hash": "c3d4", "prev_hash": "a1b2"}
            ]
        });
        let stats: StatsSnapshot = serde_json::from_value(json).unwrap();
        assert_eq!(stats.chain_tree.len(), 2);
        assert_eq!(stats.chain_tree[0].hash, "a1b2");
        assert_eq!(stats.chain_tree[1].prev_hash.as_deref(), Some("a1b2"));
    }

    #[test]
    fn test_event_window_push_and_query() {
        let mut w = EventWindow::new(5);
        w.push(vec![
            serde_json::json!({"time_s": 1.0, "message": {"type": "A"}}),
            serde_json::json!({"time_s": 2.0, "message": {"type": "B"}}),
            serde_json::json!({"time_s": 3.0, "message": {"type": "C"}}),
        ]);
        assert_eq!(w.all_events().len(), 3);
        assert_eq!(w.events_after(1.5).len(), 2);
        assert_eq!(w.events_after(3.0).len(), 0);
    }

    #[test]
    fn test_event_window_capacity() {
        let mut w = EventWindow::new(3);
        w.push(vec![
            serde_json::json!({"time_s": 1.0}),
            serde_json::json!({"time_s": 2.0}),
            serde_json::json!({"time_s": 3.0}),
            serde_json::json!({"time_s": 4.0}),
        ]);
        // Oldest event (time_s=1.0) should have been evicted.
        assert_eq!(w.all_events().len(), 3);
        let times: Vec<f64> = w
            .all_events()
            .iter()
            .filter_map(|e| e["time_s"].as_f64())
            .collect();
        assert_eq!(times, vec![2.0, 3.0, 4.0]);
    }
}
