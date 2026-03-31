//! Telemetry: event and stats sinks for observability.
//!
//! Events use a JSONL format compatible with sim-rs tooling.
//! Stats snapshots include the full peer list with bandwidth data.

use std::io::Write;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use net_core::multi_peer::types::PeerInfo;
use serde::Serialize;
use tracing::info;

use crate::config::{EventSinkConfig, StatsSinkConfig, TelemetryConfig};

// ---------------------------------------------------------------------------
// Event types (sim-rs compatible JSONL format)
// ---------------------------------------------------------------------------

/// Top-level JSONL wrapper, matching sim-rs `OutputEvent`.
#[derive(Serialize)]
pub struct OutputEvent {
    pub time_s: f64,
    pub message: NodeEvent,
}

/// Telemetry events. Uses `#[serde(tag = "type")]` for sim-rs compatibility.
#[derive(Serialize, Clone)]
#[serde(tag = "type")]
#[allow(dead_code)]
pub enum NodeEvent {
    // --- sim-rs compatible ---
    Slot {
        node: String,
        slot: u64,
    },
    RBGenerated {
        node: String,
        slot: u64,
        size_bytes: usize,
    },
    RBReceived {
        node: String,
        slot: u64,
    },
    TXGenerated {
        node: String,
        size_bytes: usize,
    },
    EBGenerated {
        node: String,
        slot: u64,
    },
    VTBundleGenerated {
        node: String,
        slot: u64,
        count: usize,
    },

    // --- net-node specific ---
    PeerConnected {
        node: String,
        peer_id: String,
        address: String,
    },
    PeerDisconnected {
        node: String,
        peer_id: String,
        reason: String,
    },
    BlockValidated {
        node: String,
        block_no: u64,
    },
    TipAdvanced {
        node: String,
        block_no: u64,
        slot: u64,
    },
    RolledBack {
        node: String,
        slot: u64,
    },
    EBReceived {
        node: String,
        slot: u64,
    },
    VotesReceived {
        node: String,
        count: usize,
    },
}

// ---------------------------------------------------------------------------
// Stats snapshot
// ---------------------------------------------------------------------------

#[derive(Serialize, Clone)]
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

#[derive(Serialize, Clone)]
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

impl PeerStatsEntry {
    pub fn from_peer_info(info: &PeerInfo) -> Self {
        Self {
            peer_id: info.peer_id.to_string(),
            address: info.address.clone(),
            mode: format!("{:?}", info.mode),
            rtt_ms: info.rtt.map(|d| d.as_secs_f64() * 1000.0),
            tip_block_no: info.tip_block_no,
            inbound_delay_ms: info.inbound_delay.as_millis() as u64,
            bytes_sent: info.bytes_sent,
            bytes_received: info.bytes_received,
        }
    }
}

// ---------------------------------------------------------------------------
// Sink traits
// ---------------------------------------------------------------------------

pub trait EventSink: Send {
    fn emit(&mut self, event: &OutputEvent);
    fn flush(&mut self);
}

pub trait StatsSink: Send {
    fn emit(&mut self, stats: &StatsSnapshot);
}

// ---------------------------------------------------------------------------
// File event sink (JSONL)
// ---------------------------------------------------------------------------

pub struct FileEventSink {
    writer: std::io::BufWriter<std::fs::File>,
    count_since_flush: usize,
}

impl FileEventSink {
    pub fn new(path: &str) -> std::io::Result<Self> {
        let file = std::fs::File::create(path)?;
        Ok(Self {
            writer: std::io::BufWriter::new(file),
            count_since_flush: 0,
        })
    }
}

impl EventSink for FileEventSink {
    fn emit(&mut self, event: &OutputEvent) {
        let _ = serde_json::to_writer(&mut self.writer, event);
        let _ = self.writer.write_all(b"\n");
        self.count_since_flush += 1;
        // Flush every 50 events to ensure data is written promptly.
        if self.count_since_flush >= 50 {
            let _ = self.writer.flush();
            self.count_since_flush = 0;
        }
    }

    fn flush(&mut self) {
        let _ = self.writer.flush();
        self.count_since_flush = 0;
    }
}

// ---------------------------------------------------------------------------
// HTTP event sink (batched POST via reqwest)
// ---------------------------------------------------------------------------

pub struct HttpEventSink {
    url: String,
    client: reqwest::Client,
    batch: Vec<serde_json::Value>,
    batch_limit: usize,
}

impl HttpEventSink {
    pub fn new(url: &str) -> Self {
        Self {
            url: url.to_string(),
            client: reqwest::Client::new(),
            batch: Vec::new(),
            batch_limit: 100,
        }
    }

    fn send_batch(&mut self) {
        if self.batch.is_empty() {
            return;
        }
        let events = std::mem::take(&mut self.batch);
        let client = self.client.clone();
        let url = self.url.clone();
        tokio::spawn(async move {
            let _ = client.post(&url).json(&events).send().await;
        });
    }
}

impl EventSink for HttpEventSink {
    fn emit(&mut self, event: &OutputEvent) {
        if let Ok(value) = serde_json::to_value(event) {
            self.batch.push(value);
        }
        if self.batch.len() >= self.batch_limit {
            self.send_batch();
        }
    }

    fn flush(&mut self) {
        self.send_batch();
    }
}

// ---------------------------------------------------------------------------
// Log stats sink (periodic tracing::info)
// ---------------------------------------------------------------------------

pub struct LogStatsSink;

impl StatsSink for LogStatsSink {
    fn emit(&mut self, stats: &StatsSnapshot) {
        info!(
            node = %stats.node_id,
            slot = stats.slot,
            tip = ?stats.tip_block_no,
            produced = stats.blocks_produced,
            received = stats.blocks_received,
            validated = stats.blocks_validated,
            peers = stats.peer_count,
            "periodic stats"
        );
        for peer in &stats.peers {
            info!(
                node = %stats.node_id,
                peer = %peer.peer_id,
                address = %peer.address,
                mode = %peer.mode,
                rtt_ms = ?peer.rtt_ms,
                delay_ms = peer.inbound_delay_ms,
                sent = peer.bytes_sent,
                received = peer.bytes_received,
                "  peer stats"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// HTTP stats sink (POST via reqwest)
// ---------------------------------------------------------------------------

pub struct HttpStatsSink {
    url: String,
    client: reqwest::Client,
}

impl HttpStatsSink {
    pub fn new(url: &str) -> Self {
        Self {
            url: url.to_string(),
            client: reqwest::Client::new(),
        }
    }
}

impl StatsSink for HttpStatsSink {
    fn emit(&mut self, stats: &StatsSnapshot) {
        let client = self.client.clone();
        let url = self.url.clone();
        let stats = stats.clone();
        tokio::spawn(async move {
            let _ = client.post(&url).json(&stats).send().await;
        });
    }
}

// ---------------------------------------------------------------------------
// Telemetry handle (owns counters, sinks, called from main loop)
// ---------------------------------------------------------------------------

pub struct TelemetryHandle {
    node_id: String,
    genesis_time_unix: u64,
    start_time: std::time::Instant,
    event_sinks: Vec<Box<dyn EventSink>>,
    stats_sinks: Vec<Box<dyn StatsSink>>,
    // Counters
    pub blocks_produced: u64,
    pub blocks_received: u64,
    pub blocks_validated: u64,
    pub txs_generated: u64,
    pub current_slot: u64,
    pub tip_block_no: Option<u64>,
}

impl TelemetryHandle {
    pub fn new(
        config: &TelemetryConfig,
        node_id: String,
        genesis_time_unix: u64,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let mut event_sinks: Vec<Box<dyn EventSink>> = Vec::new();
        for sink_config in &config.event_sinks {
            match sink_config {
                EventSinkConfig::File { path } => {
                    event_sinks.push(Box::new(FileEventSink::new(path)?));
                }
                EventSinkConfig::Http { url } => {
                    event_sinks.push(Box::new(HttpEventSink::new(url)));
                }
            }
        }

        let mut stats_sinks: Vec<Box<dyn StatsSink>> = Vec::new();
        for sink_config in &config.stats_sinks {
            match sink_config {
                StatsSinkConfig::Log => {
                    stats_sinks.push(Box::new(LogStatsSink));
                }
                StatsSinkConfig::Http { url } => {
                    stats_sinks.push(Box::new(HttpStatsSink::new(url)));
                }
            }
        }

        Ok(Self {
            start_time: std::time::Instant::now(),
            node_id,
            genesis_time_unix,
            event_sinks,
            stats_sinks,
            blocks_produced: 0,
            blocks_received: 0,
            blocks_validated: 0,
            txs_generated: 0,
            current_slot: 0,
            tip_block_no: None,
        })
    }

    /// Whether any event sinks are configured.
    #[allow(dead_code)]
    pub fn has_event_sinks(&self) -> bool {
        !self.event_sinks.is_empty()
    }

    /// Whether any stats sinks are configured.
    pub fn has_stats_sinks(&self) -> bool {
        !self.stats_sinks.is_empty()
    }

    /// Compute time_s (seconds since genesis).
    fn time_s(&self) -> f64 {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or(Duration::ZERO);
        now.as_secs_f64() - self.genesis_time_unix as f64
    }

    /// Record a telemetry event.
    pub fn record(&mut self, event: NodeEvent) {
        if self.event_sinks.is_empty() {
            return;
        }
        let output = OutputEvent {
            time_s: self.time_s(),
            message: event,
        };
        for sink in &mut self.event_sinks {
            sink.emit(&output);
        }
    }

    /// Emit a stats snapshot with peer info.
    pub fn emit_stats(&mut self, peers: &[PeerInfo]) {
        if self.stats_sinks.is_empty() {
            return;
        }
        let snapshot = StatsSnapshot {
            node_id: self.node_id.clone(),
            uptime_secs: self.start_time.elapsed().as_secs_f64(),
            slot: self.current_slot,
            tip_block_no: self.tip_block_no,
            blocks_produced: self.blocks_produced,
            blocks_received: self.blocks_received,
            blocks_validated: self.blocks_validated,
            txs_generated: self.txs_generated,
            peer_count: peers.len(),
            peers: peers.iter().map(PeerStatsEntry::from_peer_info).collect(),
        };
        for sink in &mut self.stats_sinks {
            sink.emit(&snapshot);
        }
    }

    /// Flush all sinks.
    pub fn flush(&mut self) {
        for sink in &mut self.event_sinks {
            sink.flush();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn output_event_serialization() {
        let event = OutputEvent {
            time_s: 1.23,
            message: NodeEvent::Slot {
                node: "node-0".into(),
                slot: 42,
            },
        };
        let json = serde_json::to_string(&event).unwrap();
        assert!(json.contains("\"time_s\":1.23"));
        assert!(json.contains("\"type\":\"Slot\""));
        assert!(json.contains("\"slot\":42"));
    }

    #[test]
    fn stats_snapshot_includes_peers() {
        let snapshot = StatsSnapshot {
            node_id: "test".into(),
            uptime_secs: 10.0,
            slot: 100,
            tip_block_no: Some(50),
            blocks_produced: 5,
            blocks_received: 45,
            blocks_validated: 44,
            txs_generated: 10,
            peer_count: 1,
            peers: vec![PeerStatsEntry {
                peer_id: "peer-0".into(),
                address: "127.0.0.1:3001".into(),
                mode: "Duplex".into(),
                rtt_ms: Some(5.0),
                tip_block_no: Some(50),
                inbound_delay_ms: 200,
                bytes_sent: 1024,
                bytes_received: 2048,
            }],
        };
        let json = serde_json::to_string(&snapshot).unwrap();
        assert!(json.contains("\"bytes_sent\":1024"));
        assert!(json.contains("\"bytes_received\":2048"));
        assert!(json.contains("\"inbound_delay_ms\":200"));
    }

    #[test]
    fn file_sink_writes_jsonl() {
        let path = std::env::temp_dir().join("net-node-test-events.jsonl");
        let path_str = path.to_str().unwrap();

        {
            let mut sink = FileEventSink::new(path_str).unwrap();
            sink.emit(&OutputEvent {
                time_s: 0.0,
                message: NodeEvent::Slot {
                    node: "test".into(),
                    slot: 1,
                },
            });
            sink.emit(&OutputEvent {
                time_s: 1.0,
                message: NodeEvent::RBGenerated {
                    node: "test".into(),
                    slot: 1,
                    size_bytes: 100,
                },
            });
            sink.flush();
        }

        let content = std::fs::read_to_string(&path).unwrap();
        let lines: Vec<&str> = content.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].contains("\"type\":\"Slot\""));
        assert!(lines[1].contains("\"type\":\"RBGenerated\""));

        let _ = std::fs::remove_file(&path);
    }
}
