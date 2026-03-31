//! HTTP telemetry receiver and REST API.
//!
//! Axum server with POST endpoints for receiving telemetry from net-node
//! instances, and GET endpoints for the UI to query topology, stats, and events.

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;

use axum::extract::{Path, Query, State};
use axum::http::StatusCode;
use axum::response::sse::{Event, KeepAlive, Sse};
use axum::routing::{get, post};
use axum::Json;
use futures_util::stream::Stream;
use tokio::sync::{broadcast, mpsc, RwLock};
use tower_http::cors::CorsLayer;

use crate::topology::Topology;
use crate::types::{self, EventWindow, IngestedEvent, StatsSnapshot};

/// Shared state for the HTTP server.
pub struct ServerState {
    /// Channel to send ingested events to the aggregator task.
    pub event_tx: mpsc::Sender<Vec<IngestedEvent>>,
    /// Latest stats per node.
    pub latest_stats: RwLock<HashMap<String, StatsSnapshot>>,
    /// Cluster topology.
    pub topology: Topology,
    /// Recent events window for the UI API.
    pub event_window: Arc<RwLock<EventWindow>>,
    /// Broadcast channel for real-time SSE event streaming.
    pub event_broadcast: broadcast::Sender<Vec<serde_json::Value>>,
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
    event_window: Arc<RwLock<EventWindow>>,
) -> Result<(Arc<ServerState>, tokio::task::JoinHandle<()>), Box<dyn std::error::Error + Send + Sync>>
{
    let (event_broadcast, _) = broadcast::channel(256);
    let state = Arc::new(ServerState {
        event_tx,
        latest_stats: RwLock::new(HashMap::new()),
        topology,
        event_window,
        event_broadcast,
    });

    let app = axum::Router::new()
        // Telemetry ingestion (POST).
        .route("/events", post(receive_events))
        .route("/stats", post(receive_stats))
        // UI API (GET).
        .route("/api/topology", get(get_topology))
        .route("/api/stats", get(get_all_stats))
        .route("/api/stats/:node_id", get(get_node_stats))
        .route("/api/events", get(get_events))
        .route("/api/events/stream", get(event_stream))
        .layer(CorsLayer::permissive())
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

// ---------------------------------------------------------------------------
// POST handlers (telemetry ingestion from net-node)
// ---------------------------------------------------------------------------

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

    // Push to EventWindow immediately so the UI gets real-time events
    // (the aggregator still writes time-ordered JSONL separately).
    let raw_events: Vec<serde_json::Value> = events.iter().map(|e| e.raw.clone()).collect();
    {
        state.event_window.write().await.push(raw_events.clone());
    }

    // Broadcast to SSE subscribers (ignore if no subscribers).
    let _ = state.event_broadcast.send(raw_events);

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

// ---------------------------------------------------------------------------
// GET handlers (UI API)
// ---------------------------------------------------------------------------

/// GET /api/topology — return the cluster node/edge graph.
async fn get_topology(State(state): State<Arc<ServerState>>) -> Json<Topology> {
    Json(state.topology.clone())
}

/// GET /api/stats — return latest stats for all nodes.
async fn get_all_stats(
    State(state): State<Arc<ServerState>>,
) -> Json<HashMap<String, StatsSnapshot>> {
    let stats = state.latest_stats.read().await;
    Json(stats.clone())
}

/// GET /api/stats/:node_id — return latest stats for a single node.
async fn get_node_stats(
    State(state): State<Arc<ServerState>>,
    Path(node_id): Path<String>,
) -> Result<Json<StatsSnapshot>, StatusCode> {
    let stats = state.latest_stats.read().await;
    match stats.get(&node_id) {
        Some(s) => Ok(Json(s.clone())),
        None => Err(StatusCode::NOT_FOUND),
    }
}

/// Query parameters for the events endpoint.
#[derive(serde::Deserialize)]
struct EventsQuery {
    /// Return events with time_s > after. Default: 0.
    after: Option<f64>,
}

/// GET /api/events/stream — SSE stream of events as they arrive.
async fn event_stream(
    State(state): State<Arc<ServerState>>,
) -> Sse<impl Stream<Item = Result<Event, std::convert::Infallible>>> {
    let mut rx = state.event_broadcast.subscribe();
    let stream = async_stream::stream! {
        loop {
            match rx.recv().await {
                Ok(batch) => {
                    for event in batch {
                        if let Ok(json) = serde_json::to_string(&event) {
                            yield Ok(Event::default().data(json));
                        }
                    }
                }
                Err(broadcast::error::RecvError::Lagged(n)) => {
                    tracing::warn!("SSE client lagged, dropped {n} batches");
                }
                Err(broadcast::error::RecvError::Closed) => break,
            }
        }
    };
    Sse::new(stream).keep_alive(KeepAlive::default())
}

/// GET /api/events?after=T — return recent events after the given timestamp.
async fn get_events(
    State(state): State<Arc<ServerState>>,
    Query(query): Query<EventsQuery>,
) -> Json<Vec<serde_json::Value>> {
    let window = state.event_window.read().await;
    let after = query.after.unwrap_or(0.0);
    Json(window.events_after(after))
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use tower::util::ServiceExt;

    fn test_state() -> (Arc<ServerState>, mpsc::Receiver<Vec<IngestedEvent>>) {
        let (tx, rx) = mpsc::channel(100);
        let event_window = Arc::new(RwLock::new(EventWindow::new(100)));
        let (event_broadcast, _) = broadcast::channel(256);
        let state = Arc::new(ServerState {
            event_tx: tx,
            latest_stats: RwLock::new(HashMap::new()),
            topology: Topology {
                nodes: Vec::new(),
                edges: Vec::new(),
            },
            event_window,
            event_broadcast,
        });
        (state, rx)
    }

    fn test_app(state: Arc<ServerState>) -> axum::Router {
        axum::Router::new()
            .route("/events", post(receive_events))
            .route("/stats", post(receive_stats))
            .route("/api/topology", get(get_topology))
            .route("/api/stats", get(get_all_stats))
            .route("/api/stats/:node_id", get(get_node_stats))
            .route("/api/events", get(get_events))
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

    #[tokio::test]
    async fn test_get_topology() {
        let (state, _rx) = test_state();
        let app = test_app(state);

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/api/topology")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
        let body = axum::body::to_bytes(response.into_body(), 1024 * 1024)
            .await
            .unwrap();
        let topo: serde_json::Value = serde_json::from_slice(&body).unwrap();
        assert!(topo["nodes"].is_array());
        assert!(topo["edges"].is_array());
    }

    #[tokio::test]
    async fn test_get_all_stats() {
        let (state, _rx) = test_state();
        // Insert some stats.
        state.latest_stats.write().await.insert(
            "node-0".to_string(),
            StatsSnapshot {
                node_id: "node-0".to_string(),
                uptime_secs: 10.0,
                slot: 100,
                tip_block_no: Some(5),
                tip_hash: None,
                blocks_produced: 1,
                blocks_received: 3,
                blocks_validated: 2,
                txs_generated: 10,
                peer_count: 0,
                peers: Vec::new(),
            },
        );
        let app = test_app(state);

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/api/stats")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
        let body = axum::body::to_bytes(response.into_body(), 1024 * 1024)
            .await
            .unwrap();
        let stats: HashMap<String, serde_json::Value> = serde_json::from_slice(&body).unwrap();
        assert!(stats.contains_key("node-0"));
    }

    #[tokio::test]
    async fn test_get_node_stats_found() {
        let (state, _rx) = test_state();
        state.latest_stats.write().await.insert(
            "node-0".to_string(),
            StatsSnapshot {
                node_id: "node-0".to_string(),
                uptime_secs: 10.0,
                slot: 100,
                tip_block_no: Some(5),
                tip_hash: None,
                blocks_produced: 1,
                blocks_received: 3,
                blocks_validated: 2,
                txs_generated: 10,
                peer_count: 0,
                peers: Vec::new(),
            },
        );
        let app = test_app(state);

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/api/stats/node-0")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_get_node_stats_not_found() {
        let (state, _rx) = test_state();
        let app = test_app(state);

        let response = app
            .oneshot(
                Request::builder()
                    .uri("/api/stats/nonexistent")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();

        assert_eq!(response.status(), StatusCode::NOT_FOUND);
    }

    #[tokio::test]
    async fn test_get_events() {
        let (state, _rx) = test_state();
        // Insert events into the window.
        state.event_window.write().await.push(vec![
            serde_json::json!({"time_s": 1.0, "message": {"type": "Slot"}}),
            serde_json::json!({"time_s": 2.0, "message": {"type": "Slot"}}),
            serde_json::json!({"time_s": 3.0, "message": {"type": "Slot"}}),
        ]);
        let app = test_app(state);

        // Query all events.
        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .uri("/api/events?after=0")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        let body = axum::body::to_bytes(response.into_body(), 1024 * 1024)
            .await
            .unwrap();
        let events: Vec<serde_json::Value> = serde_json::from_slice(&body).unwrap();
        assert_eq!(events.len(), 3);

        // Query events after t=1.5.
        let response = app
            .oneshot(
                Request::builder()
                    .uri("/api/events?after=1.5")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        let body = axum::body::to_bytes(response.into_body(), 1024 * 1024)
            .await
            .unwrap();
        let events: Vec<serde_json::Value> = serde_json::from_slice(&body).unwrap();
        assert_eq!(events.len(), 2);
    }
}
