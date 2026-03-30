//! HTTP telemetry receiver.
//!
//! Axum server with POST endpoints for receiving event batches and stats
//! snapshots from net-node instances.

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;

use axum::extract::State;
use axum::http::StatusCode;
use axum::routing::post;
use axum::Json;
use tokio::sync::{mpsc, RwLock};

use crate::topology::Topology;
use crate::types::{self, IngestedEvent, StatsSnapshot};

/// Shared state for the HTTP server.
pub struct ServerState {
    /// Channel to send ingested events to the aggregator task.
    pub event_tx: mpsc::Sender<Vec<IngestedEvent>>,
    /// Latest stats per node (write here, read in future Stage 2 GET endpoints).
    pub latest_stats: RwLock<HashMap<String, StatsSnapshot>>,
    /// Topology (for future Stage 2 GET endpoint).
    #[allow(dead_code)]
    pub topology: Topology,
}

/// Start the telemetry HTTP server.
///
/// Returns the `Arc<ServerState>` (shared with the aggregator) and a
/// `JoinHandle` for the server task. The server must be started before
/// spawning net-node children so they can connect immediately.
pub async fn start(
    port: u16,
    event_tx: mpsc::Sender<Vec<IngestedEvent>>,
    topology: Topology,
) -> Result<(Arc<ServerState>, tokio::task::JoinHandle<()>), Box<dyn std::error::Error + Send + Sync>>
{
    let state = Arc::new(ServerState {
        event_tx,
        latest_stats: RwLock::new(HashMap::new()),
        topology,
    });

    let app = axum::Router::new()
        .route("/events", post(receive_events))
        .route("/stats", post(receive_stats))
        .with_state(state.clone());

    let addr = SocketAddr::from(([127, 0, 0, 1], port));
    let listener = tokio::net::TcpListener::bind(addr).await?;
    tracing::info!("telemetry server listening on {addr}");

    let handle = tokio::spawn(async move {
        if let Err(e) = axum::serve(listener, app).await {
            tracing::error!("telemetry server error: {e}");
        }
    });

    Ok((state, handle))
}

/// Log notable events (block production, reception, etc.) at info level.
fn log_interesting_event(event: &IngestedEvent) {
    let msg = &event.raw.get("message");
    let event_type = msg.and_then(|m| m.get("type")).and_then(|t| t.as_str());
    match event_type {
        Some("RBGenerated") => {
            let slot = msg.and_then(|m| m.get("slot")).and_then(|s| s.as_u64());
            tracing::info!("{}: produced block (slot {:?})", event.node_id, slot);
        }
        Some("EBGenerated") => {
            let slot = msg.and_then(|m| m.get("slot")).and_then(|s| s.as_u64());
            tracing::info!("{}: produced EB (slot {:?})", event.node_id, slot);
        }
        Some("VTBundleGenerated") => {
            let count = msg.and_then(|m| m.get("count")).and_then(|c| c.as_u64());
            tracing::info!("{}: produced {} votes", event.node_id, count.unwrap_or(0));
        }
        Some("RBReceived") => {
            let slot = msg.and_then(|m| m.get("slot")).and_then(|s| s.as_u64());
            tracing::info!("{}: received block (slot {:?})", event.node_id, slot);
        }
        _ => {}
    }
}

/// POST /events — receive a batch of OutputEvent JSON values.
async fn receive_events(
    State(state): State<Arc<ServerState>>,
    Json(batch): Json<Vec<serde_json::Value>>,
) -> StatusCode {
    let events: Vec<IngestedEvent> = batch.into_iter().filter_map(types::parse_event).collect();

    if events.is_empty() {
        return StatusCode::OK;
    }

    for event in &events {
        log_interesting_event(event);
    }

    match state.event_tx.try_send(events) {
        Ok(()) => StatusCode::OK,
        Err(mpsc::error::TrySendError::Full(_)) => {
            tracing::warn!("aggregator channel full, dropping event batch");
            StatusCode::SERVICE_UNAVAILABLE
        }
        Err(mpsc::error::TrySendError::Closed(_)) => {
            tracing::warn!("aggregator channel closed");
            StatusCode::INTERNAL_SERVER_ERROR
        }
    }
}

/// POST /stats — receive a stats snapshot from a node.
async fn receive_stats(
    State(state): State<Arc<ServerState>>,
    Json(stats): Json<StatsSnapshot>,
) -> StatusCode {
    let node_id = stats.node_id.clone();
    tracing::debug!(
        "stats from {node_id}: slot={}, tip={:?}, peers={}",
        stats.slot,
        stats.tip_block_no,
        stats.peer_count
    );
    state.latest_stats.write().await.insert(node_id, stats);
    StatusCode::OK
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use tower::util::ServiceExt;

    fn test_state() -> (Arc<ServerState>, mpsc::Receiver<Vec<IngestedEvent>>) {
        let (tx, rx) = mpsc::channel(100);
        let state = Arc::new(ServerState {
            event_tx: tx,
            latest_stats: RwLock::new(HashMap::new()),
            topology: Topology {
                nodes: Vec::new(),
                edges: Vec::new(),
            },
        });
        (state, rx)
    }

    fn test_app(state: Arc<ServerState>) -> axum::Router {
        axum::Router::new()
            .route("/events", post(receive_events))
            .route("/stats", post(receive_stats))
            .with_state(state)
    }

    #[tokio::test]
    async fn test_post_events() {
        let (state, _rx) = test_state();
        let app = test_app(state);

        let body = serde_json::json!([
            {"time_s": 1.0, "message": {"type": "Slot", "node": "node-0", "slot": 1}},
            {"time_s": 2.0, "message": {"type": "Slot", "node": "node-1", "slot": 2}}
        ]);

        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/events")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_post_stats() {
        let (state, _rx) = test_state();
        let app = test_app(state.clone());

        let body = serde_json::json!({
            "node_id": "node-0",
            "uptime_secs": 10.0,
            "slot": 100,
            "tip_block_no": 5,
            "blocks_produced": 1,
            "blocks_received": 3,
            "blocks_validated": 2,
            "txs_generated": 10,
            "peer_count": 1,
            "peers": []
        });

        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/stats")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);

        let stats = state.latest_stats.read().await;
        assert!(stats.contains_key("node-0"));
        assert_eq!(stats["node-0"].slot, 100);
    }

    #[tokio::test]
    async fn test_post_empty_events() {
        let (state, _rx) = test_state();
        let app = test_app(state);

        let body = serde_json::json!([]);

        let response = app
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/events")
                    .header("content-type", "application/json")
                    .body(Body::from(serde_json::to_vec(&body).unwrap()))
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }
}
