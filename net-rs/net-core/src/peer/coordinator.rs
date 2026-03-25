//! Coordinator: manages multiple peer connections, aggregates events,
//! and exposes a peer-agnostic interface to the application.
//!
//! The coordinator runs as a single tokio task. It receives events from
//! all peer tasks via a shared fan-in channel and sends commands to
//! individual peers via per-peer channels.

use std::collections::HashMap;
use std::net::ToSocketAddrs;
use std::sync::Arc;
use std::time::Duration;

use tokio::sync::mpsc;
use tokio::task::JoinHandle;
use tokio::time::Instant;

use crate::mux::MuxConfig;
use crate::protocols::peersharing::PeerAddress;
use crate::types::{Point, Tip, WrappedHeader};

use super::chain_store::ChainStore;
use super::connect::{self, Connection};
use super::duplex_task::{run_duplex_task, DuplexTaskConfig};
use super::peer_task::{run_peer_task, PeerTaskConfig};
use super::responder_task::{run_responder_task, server_protocol_configs, ResponderTaskConfig};
use super::types::{NetworkCommand, NetworkEvent, PeerCommand, PeerEvent};
use super::{ConnectionMode, CoordinatorConfig, CoordinatorHandle, PeerId};

/// Per-peer state tracked by the coordinator.
struct PeerState {
    address: String,
    #[allow(dead_code)]
    mode: ConnectionMode,
    commands: mpsc::Sender<PeerCommand>,
    task_handle: JoinHandle<()>,
    tip: Option<Tip>,
    rtt: Option<Duration>,
    /// Backoff for next reconnection attempt if this peer fails.
    reconnect_backoff: Duration,
}

/// The coordinator's internal state.
struct Coordinator {
    config: CoordinatorConfig,
    peers: HashMap<PeerId, PeerState>,
    next_peer_id: u64,

    /// Receives (PeerId, PeerEvent) from all peer tasks.
    peer_events: mpsc::Receiver<(PeerId, PeerEvent)>,
    /// Cloned and given to each new peer task.
    peer_event_sender: mpsc::Sender<(PeerId, PeerEvent)>,

    /// Sends NetworkEvent to the application.
    network_events: mpsc::Sender<NetworkEvent>,
    /// Receives NetworkCommand from the application.
    network_commands: mpsc::Receiver<NetworkCommand>,

    /// Best known tip (for deduplication).
    best_tip: Option<Tip>,
    /// Pending block fetch requests: point → peer that's fetching it.
    pending_fetches: HashMap<Point, PeerId>,
    /// Peers waiting to be reconnected (address, next attempt time, current backoff).
    reconnect_queue: Vec<(String, Instant, Duration)>,

    /// Shared chain state for responder peers.
    chain_store: Arc<ChainStore>,
    /// Headers from HeaderAnnounced, keyed by point, for populating ChainStore on BlockFetched.
    pending_headers: HashMap<Point, WrappedHeader>,
    /// Completed inbound connections from the accept loop.
    inbound_connections: Option<mpsc::Receiver<Connection>>,
    /// Handle for the accept loop task (if listening).
    accept_task: Option<JoinHandle<()>>,
    /// Peer provider callback for PeerSharing server.
    peer_provider: Arc<dyn Fn(u8) -> Vec<PeerAddress> + Send + Sync>,
}

impl Coordinator {
    fn new(
        config: CoordinatorConfig,
        peer_event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
        peer_events: mpsc::Receiver<(PeerId, PeerEvent)>,
        network_events: mpsc::Sender<NetworkEvent>,
        network_commands: mpsc::Receiver<NetworkCommand>,
        chain_store: Arc<ChainStore>,
    ) -> Self {
        Self {
            config,
            peers: HashMap::new(),
            next_peer_id: 0,
            peer_events,
            peer_event_sender,
            network_events,
            network_commands,
            best_tip: None,
            pending_fetches: HashMap::new(),
            reconnect_queue: Vec::new(),
            chain_store,
            pending_headers: HashMap::new(),
            inbound_connections: None,
            accept_task: None,
            peer_provider: Arc::new(|_| Vec::new()),
        }
    }

    /// Assign a new PeerId and spawn an outbound peer task (initiator or duplex).
    fn add_peer_with_backoff(&mut self, address: String, reconnect_backoff: Duration) -> PeerId {
        let peer_id = PeerId(self.next_peer_id);
        self.next_peer_id += 1;

        let (cmd_sender, cmd_receiver) = mpsc::channel(16);

        let (task_handle, mode) = if self.config.duplex {
            let task_config = DuplexTaskConfig {
                peer_id,
                address: address.clone(),
                network_magic: self.config.network_magic,
                keepalive_interval: self.config.keepalive_interval,
                sdu_timeout: self.config.sdu_timeout,
                chain_store: self.chain_store.clone(),
                peer_provider: self.peer_provider.clone(),
                event_sender: self.peer_event_sender.clone(),
                command_receiver: cmd_receiver,
            };
            (
                tokio::spawn(run_duplex_task(task_config)),
                ConnectionMode::Duplex,
            )
        } else {
            let task_config = PeerTaskConfig {
                peer_id,
                address: address.clone(),
                network_magic: self.config.network_magic,
                keepalive_interval: self.config.keepalive_interval,
                sdu_timeout: self.config.sdu_timeout,
                event_sender: self.peer_event_sender.clone(),
                command_receiver: cmd_receiver,
            };
            (
                tokio::spawn(run_peer_task(task_config)),
                ConnectionMode::InitiatorOnly,
            )
        };

        self.peers.insert(
            peer_id,
            PeerState {
                address,
                mode,
                commands: cmd_sender,
                task_handle,
                tip: None,
                rtt: None,
                reconnect_backoff,
            },
        );

        peer_id
    }

    /// Assign a new PeerId and spawn a peer task with default backoff.
    fn add_peer(&mut self, address: String) -> PeerId {
        self.add_peer_with_backoff(address, Duration::from_secs(1))
    }

    /// Handle an event from a peer task.
    async fn handle_peer_event(&mut self, peer_id: PeerId, event: PeerEvent) {
        match event {
            PeerEvent::Connected => {
                let address = self
                    .peers
                    .get(&peer_id)
                    .map(|p| p.address.clone())
                    .unwrap_or_default();
                let _ = self
                    .network_events
                    .send(NetworkEvent::PeerConnected { peer_id, address })
                    .await;
            }

            PeerEvent::HeaderAnnounced { header, tip } => {
                // Update this peer's known tip.
                if let Some(peer) = self.peers.get_mut(&peer_id) {
                    peer.tip = Some(tip.clone());
                }

                // Store header for later use when BlockFetched arrives.
                self.pending_headers
                    .insert(tip.point.clone(), header.clone());

                // Deduplicate: only forward if this tip is ahead of our best.
                let is_new = match &self.best_tip {
                    None => true,
                    Some(best) => tip.block_no > best.block_no,
                };

                if is_new {
                    self.best_tip = Some(tip.clone());
                    let _ = self
                        .network_events
                        .send(NetworkEvent::TipAdvanced { tip, header })
                        .await;
                }
            }

            PeerEvent::RolledBack { point, tip } => {
                // Update peer's tip.
                if let Some(peer) = self.peers.get_mut(&peer_id) {
                    peer.tip = Some(tip.clone());
                }

                // Forward rollback if it affects our best chain.
                if let Some(best) = &self.best_tip {
                    if tip.block_no < best.block_no {
                        self.best_tip = Some(tip.clone());
                        self.chain_store.rollback_to(&point);
                        let _ = self
                            .network_events
                            .send(NetworkEvent::RolledBack { point, tip })
                            .await;
                    }
                }
            }

            PeerEvent::BlockFetched { point, body } => {
                self.pending_fetches.remove(&point);

                // Populate chain store for responder peers.
                let header = self
                    .pending_headers
                    .remove(&point)
                    .unwrap_or(WrappedHeader::opaque(vec![0xA0])); // fallback: empty CBOR map
                self.chain_store
                    .append_block(point.clone(), header, body.clone());

                let _ = self
                    .network_events
                    .send(NetworkEvent::BlockReceived { point, body })
                    .await;
            }

            PeerEvent::LatencyMeasured { rtt } => {
                if let Some(peer) = self.peers.get_mut(&peer_id) {
                    peer.rtt = Some(rtt);
                }
            }

            PeerEvent::PeersDiscovered { peers } => {
                let _ = self
                    .network_events
                    .send(NetworkEvent::PeersDiscovered { peers })
                    .await;
            }

            PeerEvent::TransactionReceived { body } => {
                let _ = self
                    .network_events
                    .send(NetworkEvent::TransactionReceived { peer_id, body })
                    .await;
            }

            PeerEvent::Failed { reason } => {
                self.remove_peer(peer_id, reason).await;
            }
        }
    }

    /// Handle a command from the application.
    async fn handle_network_command(&mut self, command: NetworkCommand) -> bool {
        match command {
            NetworkCommand::AddPeer { address } => {
                if self.peers.len() >= self.config.max_peers {
                    tracing::warn!(
                        "max peers ({}) reached, ignoring AddPeer",
                        self.config.max_peers
                    );
                } else {
                    self.add_peer(address);
                }
            }

            NetworkCommand::FetchBlock { point } => {
                // Find the best peer to fetch from: has the block (tip >= point)
                // and lowest RTT.
                if self.pending_fetches.contains_key(&point) {
                    return true; // already fetching
                }

                let best_peer = self
                    .peers
                    .iter()
                    .filter(|(_, p)| {
                        p.tip
                            .as_ref()
                            .is_some_and(|t| t.point == point || t.block_no > 0)
                    })
                    .min_by_key(|(_, p)| p.rtt.unwrap_or(Duration::from_secs(999)))
                    .map(|(id, _)| *id);

                if let Some(best_id) = best_peer {
                    if let Some(peer) = self.peers.get(&best_id) {
                        let _ = peer
                            .commands
                            .send(PeerCommand::FetchBlocks {
                                from: point.clone(),
                                to: point.clone(),
                            })
                            .await;
                        self.pending_fetches.insert(point, best_id);
                    }
                }
            }

            NetworkCommand::DiscoverPeers => {
                // Send to a random connected peer.
                if let Some((&peer_id, _)) = self.peers.iter().next() {
                    if let Some(peer) = self.peers.get(&peer_id) {
                        let _ = peer
                            .commands
                            .send(PeerCommand::RequestPeers { amount: 10 })
                            .await;
                    }
                }
            }

            NetworkCommand::InjectBlock {
                point,
                header,
                body,
            } => {
                self.chain_store.append_block(point, *header, body);
            }

            NetworkCommand::InjectRollback { point } => {
                self.chain_store.rollback_to(&point);
            }

            NetworkCommand::Shutdown => {
                // Disconnect all peers.
                let peer_ids: Vec<PeerId> = self.peers.keys().copied().collect();
                for peer_id in peer_ids {
                    if let Some(peer) = self.peers.get(&peer_id) {
                        let _ = peer.commands.send(PeerCommand::Disconnect).await;
                    }
                }
                return false; // signal to stop
            }
        }
        true // continue
    }

    /// Remove a peer, notify the application, and schedule reconnection.
    async fn remove_peer(&mut self, peer_id: PeerId, reason: String) {
        const MAX_BACKOFF: Duration = Duration::from_secs(30);

        if let Some(peer) = self.peers.remove(&peer_id) {
            peer.task_handle.abort();

            // Only schedule reconnection for initiator peers (not inbound responders).
            if peer.mode == ConnectionMode::InitiatorOnly {
                let backoff = peer.reconnect_backoff;
                let next_backoff = (backoff * 2).min(MAX_BACKOFF);
                self.reconnect_queue.push((
                    peer.address.clone(),
                    Instant::now() + backoff,
                    next_backoff,
                ));
            }

            let _ = self
                .network_events
                .send(NetworkEvent::PeerDisconnected { peer_id, reason })
                .await;

            // Clean up any pending fetches assigned to this peer.
            self.pending_fetches.retain(|_, id| *id != peer_id);
        }
    }

    /// Process any due reconnections.
    fn process_reconnections(&mut self) {
        let now = Instant::now();

        let mut still_pending = Vec::new();
        let ready: Vec<(String, Duration)> = self
            .reconnect_queue
            .drain(..)
            .filter_map(|(address, when, backoff)| {
                if now >= when {
                    Some((address, backoff))
                } else {
                    still_pending.push((address, when, backoff));
                    None
                }
            })
            .collect();

        self.reconnect_queue = still_pending;

        for (address, next_backoff) in ready {
            if self.peers.len() >= self.config.max_peers {
                // Re-queue — we're at capacity.
                self.reconnect_queue
                    .push((address, Instant::now() + next_backoff, next_backoff));
            } else {
                // Spawn a new peer task with the escalated backoff.
                // If it connects successfully and later fails, remove_peer
                // will use this backoff. On sustained success the backoff
                // could be reset (future improvement).
                let peer_id = self.add_peer_with_backoff(address.clone(), next_backoff);
                tracing::info!("reconnecting to {address} as {peer_id}");
            }
        }
    }

    /// Add a responder peer for an accepted inbound connection.
    fn add_responder_peer(&mut self, connection: Connection, address: String) -> PeerId {
        let peer_id = PeerId(self.next_peer_id);
        self.next_peer_id += 1;

        let (cmd_sender, cmd_receiver) = mpsc::channel(16);

        let task_config = ResponderTaskConfig {
            peer_id,
            connection,
            chain_store: self.chain_store.clone(),
            peer_provider: self.peer_provider.clone(),
            event_sender: self.peer_event_sender.clone(),
            command_receiver: cmd_receiver,
        };

        let task_handle = tokio::spawn(run_responder_task(task_config));

        self.peers.insert(
            peer_id,
            PeerState {
                address,
                mode: ConnectionMode::ResponderOnly,
                commands: cmd_sender,
                task_handle,
                tip: None,
                rtt: None,
                reconnect_backoff: Duration::from_secs(0), // unused for responders
            },
        );

        peer_id
    }

    /// Start the accept loop if a listen address is configured.
    fn start_accept_loop(&mut self) {
        let listen_address = match &self.config.listen_address {
            Some(addr) => addr.clone(),
            None => return,
        };

        let addr = match listen_address.to_socket_addrs() {
            Ok(mut addrs) => match addrs.next() {
                Some(addr) => addr,
                None => {
                    tracing::error!("could not resolve listen address: {listen_address}");
                    return;
                }
            },
            Err(e) => {
                tracing::error!("invalid listen address {listen_address}: {e}");
                return;
            }
        };

        let magic = self.config.network_magic;
        let mux_config = MuxConfig {
            sdu_timeout: self.config.sdu_timeout,
            ..MuxConfig::default()
        };
        let protocols = server_protocol_configs();

        let (conn_sender, conn_receiver) = mpsc::channel::<Connection>(16);
        self.inbound_connections = Some(conn_receiver);

        let task = tokio::spawn(async move {
            let listener = match tokio::net::TcpListener::bind(addr).await {
                Ok(l) => {
                    tracing::info!("listening for inbound peers on {addr}");
                    l
                }
                Err(e) => {
                    tracing::error!("failed to bind {addr}: {e}");
                    return;
                }
            };

            loop {
                match connect::accept_and_handshake(
                    &listener,
                    magic,
                    &protocols,
                    mux_config.clone(),
                )
                .await
                {
                    Ok(conn) => {
                        if conn_sender.send(conn).await.is_err() {
                            break; // coordinator shut down
                        }
                    }
                    Err(e) => {
                        tracing::warn!("inbound handshake failed: {e}");
                    }
                }
            }
        });

        self.accept_task = Some(task);
    }

    /// Time until next reconnection is due, or a large default.
    fn next_reconnect_delay(&self) -> Duration {
        self.reconnect_queue
            .iter()
            .map(|(_, when, _)| when.saturating_duration_since(Instant::now()))
            .min()
            .unwrap_or(Duration::from_secs(3600))
    }

    /// Main coordinator loop.
    async fn run(mut self) {
        // Start accept loop if configured.
        self.start_accept_loop();

        loop {
            let reconnect_delay = self.next_reconnect_delay();

            tokio::select! {
                event = self.peer_events.recv() => {
                    match event {
                        Some((peer_id, peer_event)) => {
                            self.handle_peer_event(peer_id, peer_event).await;
                        }
                        None => break,
                    }
                }
                command = self.network_commands.recv() => {
                    match command {
                        Some(cmd) => {
                            if !self.handle_network_command(cmd).await {
                                break;
                            }
                        }
                        None => break,
                    }
                }
                conn = async {
                    match &mut self.inbound_connections {
                        Some(rx) => rx.recv().await,
                        None => std::future::pending().await,
                    }
                } => {
                    if let Some(conn) = conn {
                        if self.peers.len() < self.config.max_peers {
                            let peer_id = self.add_responder_peer(conn, "inbound".to_string());
                            tracing::info!("accepted inbound peer as {peer_id}");
                        } else {
                            tracing::warn!("max peers reached, dropping inbound connection");
                            conn.running.abort();
                        }
                    }
                }
                _ = tokio::time::sleep(reconnect_delay) => {
                    self.process_reconnections();
                }
            }
        }

        // Abort accept loop if running.
        if let Some(task) = self.accept_task.take() {
            task.abort();
        }

        // Abort all remaining peer tasks.
        for (_, peer) in self.peers.drain() {
            peer.task_handle.abort();
        }
    }
}

/// Spawn a coordinator task and return a handle for the application.
pub fn spawn_coordinator(config: CoordinatorConfig) -> CoordinatorHandle {
    let (net_event_sender, net_event_receiver) = mpsc::channel(64);
    let (net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);
    let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
    let (chain_store, _chain_rx) = ChainStore::new(config.chain_store_capacity);

    let coordinator = Coordinator::new(
        config,
        peer_event_sender,
        peer_event_receiver,
        net_event_sender,
        net_cmd_receiver,
        chain_store,
    );

    tokio::spawn(coordinator.run());

    CoordinatorHandle {
        events: net_event_receiver,
        commands: net_cmd_sender,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: set up a coordinator with a MemBearer-connected peer.
    /// Returns (CoordinatorHandle, server_handle, MemBearer pair).
    ///
    /// Since the coordinator uses connect_and_handshake (TCP), we can't use
    /// MemBearer directly with it. Instead, we test the coordinator's event
    /// handling logic by manually sending events on the fan-in channel.
    #[tokio::test]
    async fn coordinator_forwards_tip_advanced() {
        use crate::types::{Tip, WrappedHeader};

        let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
        let (net_event_sender, mut net_event_receiver) = mpsc::channel(64);
        let (_net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);

        let config = CoordinatorConfig::default();
        let (chain_store, _chain_rx) = crate::peer::chain_store::ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender.clone(),
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
        );

        // Manually insert a peer (simulate it being connected).
        let peer_id = PeerId(0);
        let (cmd_sender, _cmd_receiver) = mpsc::channel(16);
        coordinator.peers.insert(
            peer_id,
            PeerState {
                address: "test:3001".to_string(),
                mode: ConnectionMode::InitiatorOnly,
                commands: cmd_sender,
                task_handle: tokio::spawn(async {}),
                tip: None,
                rtt: None,
                reconnect_backoff: Duration::from_secs(1),
            },
        );

        let tip = Tip {
            point: Point::Specific {
                slot: 100,
                hash: [1u8; 32],
            },
            block_no: 100,
        };
        let header = WrappedHeader::opaque(vec![0xA0]);

        // Send a HeaderAnnounced event.
        coordinator
            .handle_peer_event(
                peer_id,
                PeerEvent::HeaderAnnounced {
                    header: header.clone(),
                    tip: tip.clone(),
                },
            )
            .await;

        // Should produce a TipAdvanced network event.
        let event = net_event_receiver.try_recv().unwrap();
        match event {
            NetworkEvent::TipAdvanced {
                tip: recv_tip,
                header: recv_header,
            } => {
                assert_eq!(recv_tip.block_no, 100);
                assert_eq!(recv_header.raw, header.raw);
            }
            other => panic!("expected TipAdvanced, got {other:?}"),
        }

        // Verify peer's tip was updated.
        assert_eq!(
            coordinator
                .peers
                .get(&peer_id)
                .unwrap()
                .tip
                .as_ref()
                .unwrap()
                .block_no,
            100
        );
    }

    #[tokio::test]
    async fn coordinator_deduplicates_tips() {
        use crate::types::{Tip, WrappedHeader};

        let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
        let (net_event_sender, mut net_event_receiver) = mpsc::channel(64);
        let (_net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);

        let config = CoordinatorConfig::default();
        let (chain_store, _chain_rx) = crate::peer::chain_store::ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender,
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
        );

        // Two peers.
        let peer_a = PeerId(0);
        let peer_b = PeerId(1);
        for peer_id in [peer_a, peer_b] {
            let (cmd_sender, _cmd_receiver) = mpsc::channel(16);
            coordinator.peers.insert(
                peer_id,
                PeerState {
                    address: format!("test-{:?}:3001", peer_id),
                    mode: ConnectionMode::InitiatorOnly,
                    commands: cmd_sender,
                    task_handle: tokio::spawn(async {}),
                    tip: None,
                    rtt: None,
                    reconnect_backoff: Duration::from_secs(1),
                },
            );
        }

        let tip_100 = Tip {
            point: Point::Specific {
                slot: 100,
                hash: [1u8; 32],
            },
            block_no: 100,
        };
        let header = WrappedHeader::opaque(vec![0xA0]);

        // Peer A announces tip 100.
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::HeaderAnnounced {
                    header: header.clone(),
                    tip: tip_100.clone(),
                },
            )
            .await;

        // Should produce TipAdvanced.
        assert!(net_event_receiver.try_recv().is_ok());

        // Peer B announces same tip 100.
        coordinator
            .handle_peer_event(
                peer_b,
                PeerEvent::HeaderAnnounced {
                    header: header.clone(),
                    tip: tip_100.clone(),
                },
            )
            .await;

        // Should NOT produce another TipAdvanced (deduplicated).
        assert!(net_event_receiver.try_recv().is_err());

        // Peer B announces tip 101 — this IS new.
        let tip_101 = Tip {
            point: Point::Specific {
                slot: 101,
                hash: [2u8; 32],
            },
            block_no: 101,
        };
        coordinator
            .handle_peer_event(
                peer_b,
                PeerEvent::HeaderAnnounced {
                    header: header.clone(),
                    tip: tip_101,
                },
            )
            .await;

        let event = net_event_receiver.try_recv().unwrap();
        match event {
            NetworkEvent::TipAdvanced { tip, .. } => {
                assert_eq!(tip.block_no, 101);
            }
            other => panic!("expected TipAdvanced, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn coordinator_handles_peer_failure() {
        let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
        let (net_event_sender, mut net_event_receiver) = mpsc::channel(64);
        let (_net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);

        let config = CoordinatorConfig::default();
        let (chain_store, _chain_rx) = crate::peer::chain_store::ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender,
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
        );

        let peer_id = PeerId(0);
        let (cmd_sender, _cmd_receiver) = mpsc::channel(16);
        coordinator.peers.insert(
            peer_id,
            PeerState {
                address: "test:3001".to_string(),
                mode: ConnectionMode::InitiatorOnly,
                commands: cmd_sender,
                task_handle: tokio::spawn(async {}),
                tip: None,
                rtt: None,
                reconnect_backoff: Duration::from_secs(1),
            },
        );

        // Peer fails.
        coordinator
            .handle_peer_event(
                peer_id,
                PeerEvent::Failed {
                    reason: "connection reset".to_string(),
                },
            )
            .await;

        // Should produce PeerDisconnected.
        let event = net_event_receiver.try_recv().unwrap();
        match event {
            NetworkEvent::PeerDisconnected {
                peer_id: recv_id,
                reason,
            } => {
                assert_eq!(recv_id, peer_id);
                assert_eq!(reason, "connection reset");
            }
            other => panic!("expected PeerDisconnected, got {other:?}"),
        }

        // Peer should be removed.
        assert!(coordinator.peers.is_empty());

        // Should be queued for reconnection.
        assert_eq!(coordinator.reconnect_queue.len(), 1);
        assert_eq!(coordinator.reconnect_queue[0].0, "test:3001");
    }

    #[tokio::test]
    async fn coordinator_schedules_reconnection() {
        let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
        let (net_event_sender, mut net_event_receiver) = mpsc::channel(64);
        let (_net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);

        let config = CoordinatorConfig::default();
        let (chain_store, _chain_rx) = crate::peer::chain_store::ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender,
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
        );

        // Add a peer and simulate failure.
        let peer_id = PeerId(0);
        let (cmd_sender, _cmd_receiver) = mpsc::channel(16);
        coordinator.peers.insert(
            peer_id,
            PeerState {
                address: "test:3001".to_string(),
                mode: ConnectionMode::InitiatorOnly,
                commands: cmd_sender,
                task_handle: tokio::spawn(async {}),
                tip: None,
                rtt: None,
                reconnect_backoff: Duration::from_secs(1),
            },
        );

        coordinator
            .handle_peer_event(
                peer_id,
                PeerEvent::Failed {
                    reason: "test".to_string(),
                },
            )
            .await;

        // Drain the PeerDisconnected event.
        let _ = net_event_receiver.try_recv();

        // Queue should have one entry.
        assert_eq!(coordinator.reconnect_queue.len(), 1);

        // Fast-forward the reconnect time.
        coordinator.reconnect_queue[0].1 = Instant::now() - Duration::from_secs(1);

        // Process reconnections — this will call add_peer, spawning a task
        // that tries to TCP connect (and will fail since there's no server).
        coordinator.process_reconnections();

        // A new peer should have been added.
        assert_eq!(coordinator.peers.len(), 1);
        // Reconnect queue should be empty now.
        assert!(coordinator.reconnect_queue.is_empty());
    }

    #[tokio::test]
    async fn coordinator_spawn_and_shutdown() {
        let config = CoordinatorConfig::default();
        let mut handle = spawn_coordinator(config);

        // Send shutdown.
        handle
            .commands
            .send(NetworkCommand::Shutdown)
            .await
            .unwrap();

        // Events channel should close after shutdown.
        let timeout_result = tokio::time::timeout(Duration::from_secs(2), async {
            while let Some(_event) = handle.events.recv().await {
                // drain any remaining events
            }
        })
        .await;

        assert!(
            timeout_result.is_ok(),
            "coordinator should shut down cleanly"
        );
    }
}
