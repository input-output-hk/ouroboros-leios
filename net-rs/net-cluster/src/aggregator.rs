//! Time-ordered event aggregation with watermark-based flushing.
//!
//! Events from multiple nodes arrive out of order. The aggregator buffers
//! them and flushes to JSONL output in timestamp order, using a watermark
//! derived from the earliest latest-event across all known nodes.

use std::collections::{BTreeMap, HashMap};
use std::io::{BufWriter, Write};
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use tokio::sync::{mpsc, RwLock};

use crate::types::{EventWindow, IngestedEvent};

/// Run the aggregator as a tokio task.
///
/// Receives events via `event_rx`, buffers them, and flushes time-ordered
/// events to the JSONL output file based on the watermark algorithm.
pub async fn run(
    mut event_rx: mpsc::Receiver<Vec<IngestedEvent>>,
    output_path: &Path,
    num_nodes: usize,
    ordering_window_secs: f64,
    event_window: Arc<RwLock<EventWindow>>,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let file = std::fs::File::create(output_path)?;
    let mut writer = BufWriter::new(file);

    let mut state = AggregatorState::new(num_nodes, ordering_window_secs);

    let mut flush_interval = tokio::time::interval(std::time::Duration::from_secs(1));

    loop {
        tokio::select! {
            batch = event_rx.recv() => {
                match batch {
                    Some(events) => {
                        state.ingest(events);
                        state.flush_to_watermark(&mut writer, &event_window).await?;
                    }
                    None => {
                        // Channel closed — final flush of all remaining events.
                        state.flush_all(&mut writer, &event_window).await?;
                        break;
                    }
                }
            }
            _ = flush_interval.tick() => {
                state.flush_to_watermark(&mut writer, &event_window).await?;
            }
        }
    }

    writer.flush()?;
    Ok(())
}

/// Internal aggregator state.
struct AggregatorState {
    /// Latest event timestamp per node.
    latest_per_node: HashMap<String, f64>,
    /// Wall-clock time of the last event per node (for staleness detection).
    last_seen: HashMap<String, Instant>,
    /// Buffered events, ordered by timestamp.
    buffer: BTreeMap<OrderedF64, Vec<serde_json::Value>>,
    /// Expected number of nodes.
    num_nodes: usize,
    /// How long (wall-clock seconds) before a silent node is considered stale.
    stale_threshold_secs: f64,
    /// Total events written to output.
    events_written: u64,
}

/// Wrapper for f64 that implements Ord for use as BTreeMap key.
#[derive(Debug, Clone, Copy, PartialEq)]
struct OrderedF64(f64);

impl Eq for OrderedF64 {}

impl PartialOrd for OrderedF64 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrderedF64 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl AggregatorState {
    fn new(num_nodes: usize, stale_threshold_secs: f64) -> Self {
        Self {
            latest_per_node: HashMap::new(),
            last_seen: HashMap::new(),
            buffer: BTreeMap::new(),
            num_nodes,
            stale_threshold_secs,
            events_written: 0,
        }
    }

    fn ingest(&mut self, events: Vec<IngestedEvent>) {
        let now = Instant::now();
        for event in events {
            // Update per-node tracking.
            let entry = self
                .latest_per_node
                .entry(event.node_id.clone())
                .or_insert(0.0);
            if event.time_s > *entry {
                *entry = event.time_s;
            }
            self.last_seen.insert(event.node_id, now);

            // Buffer the event.
            self.buffer
                .entry(OrderedF64(event.time_s))
                .or_default()
                .push(event.raw);
        }
    }

    /// Compute the watermark: the minimum of latest timestamps across all
    /// active (non-stale) nodes. Returns None if we can't determine a safe
    /// watermark yet.
    fn watermark(&self) -> Option<f64> {
        if self.latest_per_node.is_empty() {
            return None;
        }

        let now = Instant::now();

        // Collect latest timestamps for non-stale nodes.
        let active_latest: Vec<f64> = self
            .latest_per_node
            .iter()
            .filter(|(node_id, _)| {
                if let Some(last_seen) = self.last_seen.get(*node_id) {
                    last_seen.elapsed().as_secs_f64() < self.stale_threshold_secs
                } else {
                    true
                }
            })
            .map(|(_, &t)| t)
            .collect();

        if active_latest.is_empty() {
            return None;
        }

        // If not all nodes have reported yet, only use watermark if we've
        // waited long enough (stale_threshold).
        if self.latest_per_node.len() < self.num_nodes {
            // Check if we've been running long enough for the missing nodes
            // to be considered stale. If the first node reported recently,
            // we should wait.
            let earliest_seen = self.last_seen.values().min().copied();
            if let Some(earliest) = earliest_seen {
                if now.duration_since(earliest).as_secs_f64() < self.stale_threshold_secs {
                    return None;
                }
            }
        }

        active_latest.iter().copied().reduce(f64::min)
    }

    /// Flush all events with timestamp <= watermark.
    async fn flush_to_watermark<W: Write>(
        &mut self,
        writer: &mut W,
        event_window: &Arc<RwLock<EventWindow>>,
    ) -> Result<(), std::io::Error> {
        let watermark = match self.watermark() {
            Some(w) => w,
            None => return Ok(()),
        };

        // Split the BTreeMap: we want to flush all events with time_s <= watermark.
        // split_off(key) returns everything >= key and leaves everything < key.
        // We need a cutoff strictly greater than watermark.
        let cutoff = next_after(watermark);
        let kept = self.buffer.split_off(&OrderedF64(cutoff));
        let flushing = std::mem::replace(&mut self.buffer, kept);

        let mut window_batch = Vec::new();
        for (_ts, events) in flushing {
            for event in events {
                serde_json::to_writer(&mut *writer, &event)?;
                writer.write_all(b"\n")?;
                self.events_written += 1;
                window_batch.push(event);
            }
        }
        writer.flush()?;

        if !window_batch.is_empty() {
            event_window.write().await.push(window_batch);
        }

        if self.events_written > 0 && self.events_written.is_multiple_of(1000) {
            tracing::info!("aggregator: {} events written", self.events_written);
        }

        Ok(())
    }

    /// Flush all remaining buffered events (used at shutdown).
    async fn flush_all<W: Write>(
        &mut self,
        writer: &mut W,
        event_window: &Arc<RwLock<EventWindow>>,
    ) -> Result<(), std::io::Error> {
        let flushing = std::mem::take(&mut self.buffer);
        let mut window_batch = Vec::new();
        for (_ts, events) in flushing {
            for event in events {
                serde_json::to_writer(&mut *writer, &event)?;
                writer.write_all(b"\n")?;
                self.events_written += 1;
                window_batch.push(event);
            }
        }
        writer.flush()?;

        if !window_batch.is_empty() {
            event_window.write().await.push(window_batch);
        }

        tracing::info!(
            "aggregator: final flush complete, {} total events written",
            self.events_written
        );
        Ok(())
    }
}

/// Return the smallest f64 strictly greater than `x`.
fn next_after(x: f64) -> f64 {
    if x.is_nan() || x == f64::INFINITY {
        return x;
    }
    if x == f64::NEG_INFINITY {
        return f64::MIN;
    }
    let bits = x.to_bits();
    let next_bits = if x >= 0.0 { bits + 1 } else { bits - 1 };
    f64::from_bits(next_bits)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_event(time_s: f64, node: &str) -> IngestedEvent {
        IngestedEvent {
            time_s,
            node_id: node.to_string(),
            raw: serde_json::json!({
                "time_s": time_s,
                "message": {"type": "Slot", "node": node, "slot": (time_s as u64)}
            }),
        }
    }

    #[test]
    fn test_watermark_no_events() {
        let state = AggregatorState::new(3, 5.0);
        assert!(state.watermark().is_none());
    }

    #[test]
    fn test_watermark_partial_nodes() {
        let mut state = AggregatorState::new(3, 5.0);
        // Only one node has reported — watermark should be None since not
        // enough time has passed for missing nodes to be stale.
        state.ingest(vec![make_event(1.0, "node-0")]);
        assert!(state.watermark().is_none());
    }

    #[test]
    fn test_watermark_all_nodes() {
        let mut state = AggregatorState::new(2, 5.0);
        state.ingest(vec![make_event(1.0, "node-0"), make_event(2.0, "node-1")]);
        // Both nodes reported, watermark = min(1.0, 2.0) = 1.0.
        let w = state.watermark().unwrap();
        assert!((w - 1.0).abs() < f64::EPSILON);
    }

    fn test_window() -> Arc<RwLock<EventWindow>> {
        Arc::new(RwLock::new(EventWindow::new(1000)))
    }

    #[tokio::test]
    async fn test_flush_ordering() {
        let mut state = AggregatorState::new(2, 5.0);
        state.ingest(vec![
            make_event(3.0, "node-0"),
            make_event(1.0, "node-0"),
            make_event(2.0, "node-1"),
            make_event(4.0, "node-1"),
        ]);

        let window = test_window();
        let mut output = Vec::new();
        state
            .flush_to_watermark(&mut output, &window)
            .await
            .unwrap();

        let lines: Vec<&str> = std::str::from_utf8(&output)
            .unwrap()
            .trim()
            .split('\n')
            .collect();

        // Watermark = min(3.0, 4.0) = 3.0, so events at t=1.0, 2.0, 3.0 flush.
        assert_eq!(lines.len(), 3);

        // Verify ordering.
        let times: Vec<f64> = lines
            .iter()
            .map(|l| {
                let v: serde_json::Value = serde_json::from_str(l).unwrap();
                v["time_s"].as_f64().unwrap()
            })
            .collect();
        assert_eq!(times, vec![1.0, 2.0, 3.0]);

        // Verify event window also received the events.
        assert_eq!(window.read().await.all_events().len(), 3);
    }

    #[tokio::test]
    async fn test_flush_all() {
        let mut state = AggregatorState::new(2, 5.0);
        state.ingest(vec![make_event(1.0, "node-0"), make_event(5.0, "node-1")]);

        let window = test_window();
        let mut output = Vec::new();
        state.flush_all(&mut output, &window).await.unwrap();

        let lines: Vec<&str> = std::str::from_utf8(&output)
            .unwrap()
            .trim()
            .split('\n')
            .collect();
        assert_eq!(lines.len(), 2);
        assert_eq!(window.read().await.all_events().len(), 2);
    }
}
