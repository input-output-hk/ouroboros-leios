//! HTTP telemetry receiver and REST API.
//!
//! Axum server with POST endpoints for receiving telemetry from net-node
//! instances, and GET endpoints for the UI to query topology, stats, and events.

use std::collections::{BTreeSet, HashMap};
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
use crate::config::{ActiveAttack, AttackRequest, ClusterControlConfig};
use crate::topology::Topology;
use crate::types::{
    self, AggregatedVotesHistory, EventWindow, IngestedEvent, NodeVotes, StatsSnapshot, WINDOW_SIZE
};

/// Control message sent from the HTTP handlers to the main loop for
/// the runtime attack-trigger feature.
#[derive(Debug)]
pub enum AttackCommand {
    /// Install `request.behaviour` on the nodes picked by
    /// `request.selection`.  Replaces any prior active attack (the
    /// affected nodes are reset to their startup spec first).
    Start(AttackRequest),
    /// Reset every node currently part of the active attack back to
    /// its startup spec and clear the active-attack state.  No-op when
    /// no attack is active.
    Stop,
}

/// Shared state for the HTTP server.
pub struct ServerState {
    /// Channel to send ingested events to the aggregator task.
    pub event_tx: mpsc::Sender<Vec<IngestedEvent>>,
    /// Latest stats per node.
    pub latest_stats: RwLock<HashMap<String, StatsSnapshot>>,
    /// Voting aggregate statistics, by node.
    pub aggregate_votes: RwLock<AggregatedVotes>,
    /// Cluster topology (updated on restart).
    pub topology: RwLock<Topology>,
    /// Recent events window for the UI API.
    pub event_window: Arc<RwLock<EventWindow>>,
    /// Broadcast channel for real-time SSE event streaming.
    pub event_broadcast: broadcast::Sender<Vec<serde_json::Value>>,
    /// Channel to send restart commands to the main loop.
    pub restart_tx: mpsc::Sender<ClusterControlConfig>,
    /// Channel to send node config updates (without restart) to the main loop.
    pub update_tx: mpsc::Sender<std::collections::HashMap<String, serde_json::Value>>,
    /// Channel for runtime attack-trigger commands (start / stop).  The
    /// main loop owns the per-node stdin pipes and the resolved
    /// node-stake vector, so it does the actual installation.
    pub attack_tx: mpsc::Sender<AttackCommand>,
    /// Current controllable config (updated on restart).
    pub current_config: RwLock<ClusterControlConfig>,
    /// Per-node stake vector aligned with `topology.nodes`.  Read by
    /// the main loop to resolve `BehaviourSelection` at attack-trigger
    /// time, and refreshed on every restart.
    pub stakes: RwLock<Vec<u64>>,
    /// Currently-active runtime attack, or `None` if no attack is in
    /// progress.  Maintained by the main loop; surfaced to the UI via
    /// `GET /api/attack`.
    pub active_attack: RwLock<Option<ActiveAttack>>,
    /// Guard against concurrent restarts.
    pub restarting: RwLock<bool>,
}

#[derive(Default)]
pub struct AggregatedVotes {
    /// Maps event (indexed by slot --- *TODO:* we hope that only one RB exists for a slot)
    /// to status of the message, follow-up events, indexed by node which produced the
    /// follow-up event:
    /// * RBReceived;
    /// * EBGenerated;
    /// * EBReceived;
    /// * Vote ('yes' if it was certified by current node);
    /// * Member of persistent committee (for the slot) at the time of election.
    pub events: HashMap<u64, HashMap<String, NodeVotes>>,
    pub slots: BTreeSet<u64>,
}

impl AggregatedVotes {
    fn update_for_slot_node<F>(&mut self, node_id: String, slot: u64, update: F)
    where
        F: FnOnce(&mut NodeVotes),
    {
        let slot_entry = self.events.entry(slot).or_default();
        let bitmask = slot_entry.entry(node_id).or_default();
        update(bitmask);
    }

    pub fn update_aggregated_event(&mut self, event: &IngestedEvent) {
        let msg = &event.raw.get("message");
        let event_type = msg.and_then(|m| m.get("type")).and_then(|t| t.as_str());
        let slot = msg.and_then(|m| m.get("slot")).and_then(|s| s.as_u64());
        let node_id = event.node_id.clone();
        if let Some(slot) = slot {
            match event_type {
                Some("RBReceived") => {
                    self.slots.insert(slot);
                    self.update_for_slot_node(node_id, slot, |mask| {
                        mask.rb_received = true;
                    });
                }
                Some("EBReceived") => {
                    self.slots.insert(slot);
                    self.update_for_slot_node(node_id, slot, |mask| {
                        mask.eb_received = true;
                    });
                }
                Some("EBGenerated") => {
                    self.slots.insert(slot);
                    self.update_for_slot_node(node_id, slot, |mask| {
                        mask.eb_generated = true;
                    });
                }
                Some("VTBundleGenerated") => {
                    self.slots.insert(slot);
                    let count = msg.and_then(|m| m.get("count"));
                    if count.and_then(|c| c.as_u64()).unwrap_or(0) > 0 {
                        self.update_for_slot_node(node_id, slot, |mask| {
                            mask.vote_cast = true;
                        });
                    }
                }
                Some("LeiosElectionInfo") => {
                    let pers_committee = msg.and_then(
                        |m| m.get("pers_committee_member")).and_then(|c| c.as_bool()
                    );
                    // No event happens, so no slot update needed.
                    self.update_for_slot_node(node_id, slot, |mask| {
                        mask.perm_committee_member = pers_committee.is_some_and(|x| x);
                    });
                }
                _ => {}
            }
        }
    }

    /// Removing old events to prevent unbounded memory growth.
    pub fn garbage_collect(&mut self) {
        let mut deleted_slots = 0;
        while let Some(oldest) = self.slots.first().cloned() {
            if self.slots.len() <= WINDOW_SIZE as usize {
                break;
            }

            self.events.remove(&oldest);
            self.slots.remove(&oldest);
            deleted_slots += 1;
        }

        if deleted_slots > 0 {
            tracing::info!(
                "Aggregated voting GC: {deleted_slots} slots deleted, current interval: {:?}..={:?}, {} slots",
                self.slots.first(),
                self.slots.last(),
                self.slots.len()
            );
        }
    }
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
    restart_tx: mpsc::Sender<ClusterControlConfig>,
    update_tx: mpsc::Sender<HashMap<String, serde_json::Value>>,
    attack_tx: mpsc::Sender<AttackCommand>,
    initial_config: ClusterControlConfig,
    initial_stakes: Vec<u64>,
) -> Result<(Arc<ServerState>, tokio::task::JoinHandle<()>), Box<dyn std::error::Error + Send + Sync>>
{
    let (event_broadcast, _) = broadcast::channel(256);
    let state = Arc::new(ServerState {
        event_tx,
        latest_stats: RwLock::new(HashMap::new()),
        topology: RwLock::new(topology),
        event_window,
        event_broadcast,
        restart_tx,
        update_tx,
        attack_tx,
        current_config: RwLock::new(initial_config),
        stakes: RwLock::new(initial_stakes),
        active_attack: RwLock::new(None),
        restarting: RwLock::new(false),
        aggregate_votes: RwLock::new(AggregatedVotes::default()),
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
        .route("/api/votes-history", get(get_votes_history)) // TODO: separate endpoint for aggregated votes?
        // Cluster control API.
        .route("/api/config", get(get_config))
        .route("/api/restart", post(restart_cluster))
        .route("/api/update-config", post(update_config))
        .route("/api/attack", get(get_attack).post(start_attack))
        .route("/api/attack/stop", post(stop_attack))
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
            let len = msg.and_then(|m| m.get("len")).and_then(|l| l.as_u64());
            tracing::info!("{}: received block (slot {:?}, len {:?})", event.node_id, slot, len);
        }
        Some("EBReceived") => {
            let slot = msg.and_then(|m| m.get("slot")).and_then(|s| s.as_u64());
            let len = msg.and_then(|m| m.get("len")).and_then(|l| l.as_u64());
            tracing::info!("{}: received EB (slot {:?}, len {:?})", event.node_id, slot, len);
        }
        Some("EBTxsReceived") => {
            let slot = msg.and_then(|m| m.get("slot")).and_then(|s| s.as_u64());
            let len = msg.and_then(|m| m.get("len")).and_then(|c| c.as_u64());
            tracing::info!("{}: received EB txs (slot {:?}, count {:?})", event.node_id, slot, len);
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
        state.aggregate_votes.write().await.update_aggregated_event(event);
    }

    {
        state.aggregate_votes.write().await.garbage_collect();
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
    Json(state.topology.read().await.clone())
}

/// GET /api/config — return current controllable config.
async fn get_config(State(state): State<Arc<ServerState>>) -> Json<ClusterControlConfig> {
    Json(state.current_config.read().await.clone())
}

/// POST /api/restart — restart the cluster with new config overrides.
async fn restart_cluster(
    State(state): State<Arc<ServerState>>,
    Json(overrides): Json<ClusterControlConfig>,
) -> Result<StatusCode, (StatusCode, String)> {
    {
        let mut restarting = state.restarting.write().await;
        if *restarting {
            return Err((StatusCode::CONFLICT, "Restart already in progress".into()));
        }
        *restarting = true;
    }
    match state.restart_tx.send(overrides).await {
        Ok(()) => Ok(StatusCode::ACCEPTED),
        Err(_) => {
            *state.restarting.write().await = false;
            Err((
                StatusCode::INTERNAL_SERVER_ERROR,
                "Restart channel closed".into(),
            ))
        }
    }
}

/// Payload for POST /api/update-config.
#[derive(serde::Deserialize)]
struct UpdateConfigPayload {
    node_config: HashMap<String, serde_json::Value>,
}

/// POST /api/update-config — push node config changes to running nodes without restart.
async fn update_config(
    State(state): State<Arc<ServerState>>,
    Json(payload): Json<UpdateConfigPayload>,
) -> Result<StatusCode, (StatusCode, String)> {
    // Update stored config so GET /api/config reflects the change.
    {
        let mut config = state.current_config.write().await;
        for (k, v) in &payload.node_config {
            config.node_config.insert(k.clone(), v.clone());
        }
    }
    // Send to main loop for delivery to child processes.
    match state.update_tx.try_send(payload.node_config) {
        Ok(()) => Ok(StatusCode::OK),
        Err(mpsc::error::TrySendError::Full(_)) => Err((
            StatusCode::SERVICE_UNAVAILABLE,
            "Update channel full".into(),
        )),
        Err(mpsc::error::TrySendError::Closed(_)) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            "Update channel closed".into(),
        )),
    }
}

/// GET /api/attack — return the currently-active runtime attack, or
/// `null` when no attack is in progress.
async fn get_attack(State(state): State<Arc<ServerState>>) -> Json<Option<ActiveAttack>> {
    Json(state.active_attack.read().await.clone())
}

/// POST /api/attack — install `request.behaviour` on the nodes picked
/// by `request.selection`.  Returns 202 once the command is queued, or
/// 409 Conflict if an attack is already active (call
/// `POST /api/attack/stop` first to replace).
async fn start_attack(
    State(state): State<Arc<ServerState>>,
    Json(request): Json<AttackRequest>,
) -> Result<StatusCode, (StatusCode, String)> {
    if state.active_attack.read().await.is_some() {
        return Err((
            StatusCode::CONFLICT,
            "An attack is already active; POST /api/attack/stop first".into(),
        ));
    }
    match state.attack_tx.try_send(AttackCommand::Start(request)) {
        Ok(()) => Ok(StatusCode::ACCEPTED),
        Err(mpsc::error::TrySendError::Full(_)) => Err((
            StatusCode::SERVICE_UNAVAILABLE,
            "Attack channel full".into(),
        )),
        Err(mpsc::error::TrySendError::Closed(_)) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            "Attack channel closed".into(),
        )),
    }
}

/// POST /api/attack/stop — reset every node currently part of the
/// active attack back to its startup spec.  No-op when no attack is
/// active.  Returns 202 once the command is queued.
async fn stop_attack(
    State(state): State<Arc<ServerState>>,
) -> Result<StatusCode, (StatusCode, String)> {
    match state.attack_tx.try_send(AttackCommand::Stop) {
        Ok(()) => Ok(StatusCode::ACCEPTED),
        Err(mpsc::error::TrySendError::Full(_)) => Err((
            StatusCode::SERVICE_UNAVAILABLE,
            "Attack channel full".into(),
        )),
        Err(mpsc::error::TrySendError::Closed(_)) => Err((
            StatusCode::INTERNAL_SERVER_ERROR,
            "Attack channel closed".into(),
        )),
    }
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

async fn get_votes_history(
    State(state): State<Arc<ServerState>>,
) -> Json<AggregatedVotesHistory> {
    let node_ids: Vec<String> = state.topology.read().await
        .nodes.iter().map(|t| t.node_id.clone()).collect();

    let votes = state.aggregate_votes.read().await;

    let last_slot = votes.events.keys().max().cloned().unwrap_or(0);

    // History: from newest [idx=0, slot=last_slot] to oldest [idx=WINDOW_SIZE-1,
    //          slot=last_slot-WINDOW_SIZE+1].
    let mut history = Vec::new();
    for slot in ((last_slot+1).saturating_sub(WINDOW_SIZE)..=last_slot).rev() {
        let Some(node_statuses) = votes.events.get(&slot) else {
            history.push("".to_string());
            continue;
        };
        let mut str = String::new();
        for node_id in &node_ids {
            // Priority: Vote > EB > RB > Committee membership.
            // Rationale:
            // 1. Vote cast only if all other events happened; correctness of node
            //    behaviour is not intended to be tested here (yet).
            // 2. This is needed for Leios debugging: so EB reception is more important than RB.
            // 3. Committee info will be shown in empty slots, and committee does not change
            //    often, so viewer will guess it from adjacent columns, no need to specify
            //    this info each time.
            str.push(match node_statuses.get(node_id) {
                Some(NodeVotes {vote_cast: true, eb_received: true, rb_received: true, ..}) => '1',
                Some(NodeVotes {vote_cast: true, eb_generated: true, ..}) => 'G',
                Some(NodeVotes {eb_received: true, rb_received: true, ..}) => 'E',
                Some(NodeVotes {rb_received: true, ..}) => 'R',
                Some(NodeVotes {perm_committee_member: true, eb_received: false, vote_cast: false, ..}) => '*',
                Some(NodeVotes {perm_committee_member: false, eb_received: false, vote_cast: false, ..}) => '.',
                None => '.',
                _ => '?'
            });
        }
        history.push(str);
    };

    Json(AggregatedVotesHistory{
        last_slot,
        node_ids,
        votes: history, // TODO: serialize the full history of votes
    })
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
        let (restart_tx, _restart_rx) = mpsc::channel(1);
        let (update_tx, _update_rx) = mpsc::channel(16);
        let (attack_tx, _attack_rx) = mpsc::channel(4);
        let state = Arc::new(ServerState {
            event_tx: tx,
            latest_stats: RwLock::new(HashMap::new()),
            topology: RwLock::new(Topology {
                nodes: Vec::new(),
                edges: Vec::new(),
            }),
            event_window,
            event_broadcast,
            restart_tx,
            update_tx,
            attack_tx,
            current_config: RwLock::new(ClusterControlConfig {
                num_nodes: Some(5),
                degree: Some(3),
                min_latency_ms: Some(5),
                max_latency_ms: Some(300),
                seed: None,
                node_config: HashMap::new(),
            }),
            stakes: RwLock::new(Vec::new()),
            active_attack: RwLock::new(None),
            restarting: RwLock::new(false),
            aggregate_votes: RwLock::new(AggregatedVotes::default()),
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
                chain_tree: Vec::new(),
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
                chain_tree: Vec::new(),
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

    #[test]
    fn test_garbage_collect() {
        let mut votes = AggregatedVotes::default();

        // Insert 50 slots with mixed content:
        // - Even slots: only perm_committee_member (no real events)
        // - Odd slots: have actual events (rb_received, and optionally eb/vote)
        for slot in 0..50u64 {
            votes.slots.insert(slot);
            let mut node_map = HashMap::new();
            if slot % 2 == 0 {
                // Committee-only slot (no real events)
                node_map.insert("node-0".to_string(), NodeVotes {
                    perm_committee_member: true,
                    rb_received: false,
                    eb_received: false,
                    eb_generated: false,
                    vote_cast: false,
                });
            } else {
                // Slot with real events
                node_map.insert("node-0".to_string(), NodeVotes {
                    perm_committee_member: true,
                    rb_received: true,
                    eb_received: slot >= 21,
                    eb_generated: false,
                    vote_cast: slot >= 31,
                });
            }
            votes.events.insert(slot, node_map);
        }

        assert_eq!(votes.slots.len(), 50);

        votes.garbage_collect();

        // 1) Exactly WINDOW_SIZE (25) slots remain.
        assert_eq!(votes.slots.len(), WINDOW_SIZE as usize);

        // 2) Removed slots are the oldest ones, so only the newest 25 remain.
        for slot in 0..50u64 {
            // All elder odd slots should have been removed
            if !votes.slots.contains(&slot) {
                assert!(slot < *votes.slots.first().unwrap());
                assert!(votes.events.iter().all(|(k,_v)| slot < *k));
            }
        }

        // 3) Slots and events are in sync
        for slot in votes.slots.iter() {
            assert!(votes.events.contains_key(slot));
        }

        for slot in votes.events.keys() {
            assert!(votes.slots.contains(slot));
        }
    }
}
