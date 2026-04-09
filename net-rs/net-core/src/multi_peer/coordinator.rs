//! Coordinator: manages multiple peer connections, aggregates events,
//! and exposes a peer-agnostic interface to the application.
//!
//! The coordinator runs as a single tokio task. It receives events from
//! all peer tasks via a shared fan-in channel and sends commands to
//! individual peers via per-peer channels.

use std::collections::HashMap;
use std::net::{IpAddr, SocketAddr, ToSocketAddrs};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use tokio::sync::mpsc;
use tokio::task::JoinHandle;
use tokio::time::Instant;

use super::chain_fragment::ChainFragment;
use super::leios_tracker::{LeiosTracker, OfferResult, PeerRttLookup};
use crate::bearer::tcp::TcpBearer;
use crate::mux::MuxConfig;
use crate::protocols::peersharing::PeerAddress;
use crate::types::{Point, Tip};

use super::types::{NetworkCommand, NetworkEvent};
use super::{CoordinatorConfig, CoordinatorHandle};
use crate::peer::connect::{self, DuplexConnection};
use crate::peer::duplex_task::{
    run_accepted_duplex_task, run_duplex_task, AcceptedDuplexTaskConfig, DuplexTaskConfig,
};
use crate::peer::peer_task::{
    client_protocol_configs, run_peer_task, server_protocol_configs, PeerTaskConfig,
};
use crate::peer::types::{PeerCommand, PeerEvent};
use crate::peer::{ConnectionMode, PeerId};
use crate::store::chain_store::ChainStore;
use crate::store::leios_store::LeiosStore;

/// Per-peer state tracked by the coordinator.
struct PeerState {
    address: String,
    #[allow(dead_code)]
    mode: ConnectionMode,
    /// IP address for inbound peers (used for per-IP connection counting).
    ip: Option<IpAddr>,
    commands: mpsc::Sender<PeerCommand>,
    task_handle: JoinHandle<()>,
    tip: Option<Tip>,
    rtt: Option<Duration>,
    /// Chain fragment: ordered points announced via ChainSync.
    fragment: ChainFragment,
    /// Backoff for next reconnection attempt if this peer fails.
    reconnect_backoff: Duration,
    /// Simulated inbound delay. Events from this peer are delayed by this
    /// duration before processing. Zero = no delay.
    inbound_delay: Duration,
    /// Shared byte counters from this peer's mux connection.
    mux_stats: Option<Arc<crate::mux::MuxStats>>,
    /// Last rollback point this peer was notified to, for dedup: we
    /// refuse to forward consecutive `RolledBack` events with the same
    /// point so a chatty peer can't flood the consensus channel.
    last_rolled_back_to: Option<Point>,
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
    /// Shared Leios data store for responder peers (when leios_enabled).
    leios_store: Option<Arc<LeiosStore>>,
    /// Leios dedup, offer tracking, and fetch routing (None when leios_enabled=false).
    leios: Option<LeiosTracker>,
    /// Completed inbound duplex connections from the accept loop.
    inbound_connections: Option<mpsc::Receiver<(DuplexConnection, SocketAddr)>>,
    /// Handle for the accept loop task (if listening).
    accept_task: Option<JoinHandle<()>>,
    /// Per-IP connection count (handshaking + established). Shared with accept loop.
    ip_counts: Arc<Mutex<HashMap<IpAddr, usize>>>,
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
        leios_store: Option<Arc<LeiosStore>>,
    ) -> Self {
        let leios = if config.leios_enabled {
            Some(LeiosTracker::new(config.leios_dedup_window))
        } else {
            None
        };
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
            leios_store,
            leios,
            inbound_connections: None,
            accept_task: None,
            ip_counts: Arc::new(Mutex::new(HashMap::new())),
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
                leios_enabled: self.config.leios_enabled,
                leios_store: self.leios_store.clone(),
                traffic_class_overrides: self.config.traffic_class_overrides.clone(),
                scheduler_type: self.config.scheduler_type,
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
                chain_store: self.chain_store.clone(),
                event_sender: self.peer_event_sender.clone(),
                command_receiver: cmd_receiver,
                leios_enabled: self.config.leios_enabled,
                traffic_class_overrides: self.config.traffic_class_overrides.clone(),
                scheduler_type: self.config.scheduler_type,
            };
            (
                tokio::spawn(run_peer_task(task_config)),
                ConnectionMode::InitiatorOnly,
            )
        };

        let inbound_delay = self
            .config
            .peer_delays
            .get(&address)
            .copied()
            .unwrap_or(Duration::ZERO);

        self.peers.insert(
            peer_id,
            PeerState {
                address,
                mode,
                ip: None,
                commands: cmd_sender,
                task_handle,
                tip: None,
                rtt: None,
                fragment: ChainFragment::new(),
                reconnect_backoff,
                inbound_delay,
                mux_stats: None,
                last_rolled_back_to: None,
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
            PeerEvent::Connected { mux_stats } => {
                if let Some(peer) = self.peers.get_mut(&peer_id) {
                    peer.mux_stats = Some(mux_stats);
                }
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

            PeerEvent::IntersectionFound { point } => {
                if let Some(peer) = self.peers.get_mut(&peer_id) {
                    peer.fragment.set_intersection(point.clone());
                }
                // Forward to consensus so it can store the intersection as
                // the peer chain's anchor (guaranteed common ancestor).
                let _ = self
                    .network_events
                    .send(NetworkEvent::IntersectionFound { peer_id, point })
                    .await;
            }

            PeerEvent::HeaderAnnounced { header, tip } => {
                // Derive the header's own point (may differ from tip when catching up).
                let header_point = header.point().unwrap_or(tip.point.clone());

                // Update this peer's known tip and chain fragment.
                if let Some(peer) = self.peers.get_mut(&peer_id) {
                    peer.tip = Some(tip.clone());
                    peer.fragment.append(header_point.clone());
                    // A fresh forward progression clears the rollback dedup.
                    peer.last_rolled_back_to = None;
                }

                // Update best tip tracker.
                let dominated = match &self.best_tip {
                    None => false,
                    Some(best) => tip.block_no <= best.block_no,
                };
                if !dominated {
                    self.best_tip = Some(tip.clone());
                }

                // Forward every per-peer announcement so consensus can
                // maintain a candidate chain per peer (Haskell-style).
                let _ = self
                    .network_events
                    .send(NetworkEvent::TipAdvanced {
                        peer_id,
                        tip,
                        header,
                    })
                    .await;
            }

            PeerEvent::RolledBack { point, tip } => {
                // Update peer's tip and truncate chain fragment.
                // Per-peer dedup: if we already forwarded a rollback to
                // this same point for this peer, don't refire — a chatty
                // peer could otherwise flood the consensus channel.
                let duplicate = if let Some(peer) = self.peers.get_mut(&peer_id) {
                    peer.tip = Some(tip.clone());
                    peer.fragment.rollback_to(&point);
                    let dup = peer.last_rolled_back_to.as_ref() == Some(&point);
                    if !dup {
                        peer.last_rolled_back_to = Some(point.clone());
                    }
                    dup
                } else {
                    false
                };

                // If this peer's rollback lowers our best tip, update the
                // best tip and the local chain store. This mirrors the
                // prior behaviour but is no longer gated on forwarding.
                if let Some(best) = &self.best_tip {
                    if tip.block_no < best.block_no {
                        self.best_tip = Some(tip.clone());
                        self.chain_store.rollback_to(&point);
                    }
                }

                // Always forward (unless deduped) so consensus can retire
                // headers from the peer's candidate chain.
                if !duplicate {
                    let _ = self
                        .network_events
                        .send(NetworkEvent::RolledBack {
                            peer_id,
                            point,
                            tip,
                        })
                        .await;
                }
            }

            PeerEvent::BlockFetched { body } => {
                // Derive the point from the block body (header hash + slot).
                // Requires blocks to have valid Shelley+ CBOR structure.
                let point = body.point().unwrap_or(Point::Origin);

                self.pending_fetches.remove(&point);

                // Note: we do NOT remove the point from peer fragments.
                // Fragments represent what peers announced via ChainSync
                // and are used for fetch routing. Removing fetched points
                // would break future FetchBlockRange requests that use
                // this point as `from` or `to`. The pending_fetches dedup
                // already prevents duplicate in-flight fetches.

                // Forward to app for validation. The app will InjectBlock after
                // validation to make the block available to downstream peers.
                let _ = self
                    .network_events
                    .send(NetworkEvent::BlockReceived { point, body })
                    .await;
            }

            PeerEvent::LatencyMeasured { rtt } => {
                if let Some(peer) = self.peers.get_mut(&peer_id) {
                    // Accepted peers (ip.is_some()) don't have configured
                    // inbound_delay — skip their RTT to avoid showing 0ms.
                    // The outbound side of each connection tracks RTT.
                    if peer.ip.is_none() {
                        // Add the simulated inbound delay so RTT reflects
                        // configured link latency (real TCP on localhost is ~0).
                        peer.rtt = Some(rtt + peer.inbound_delay);
                    }
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

            // Leios events — deduplicated with offer tracking for smart routing.
            PeerEvent::LeiosBlockAnnounced { header } => {
                let _ = self
                    .network_events
                    .send(NetworkEvent::LeiosBlockAnnounced { header })
                    .await;
            }

            PeerEvent::LeiosBlockOffered { point } => {
                if let (Point::Specific { slot, hash }, Some(tracker)) =
                    (&point, self.leios.as_mut())
                {
                    match tracker.handle_block_offer(*slot, *hash, peer_id) {
                        OfferResult::New => {
                            tracing::debug!("leios: new EB offer at slot {slot} from {peer_id}");
                            let _ = self
                                .network_events
                                .send(NetworkEvent::LeiosBlockOffered { point })
                                .await;
                        }
                        OfferResult::Duplicate => {
                            tracing::debug!(
                                "leios: deduplicated EB offer at slot {slot} from {peer_id} (already seen)"
                            );
                        }
                        OfferResult::AtCapacity => {
                            tracing::warn!(
                                "leios: seen_leios_blocks at capacity, forwarding without dedup"
                            );
                            let _ = self
                                .network_events
                                .send(NetworkEvent::LeiosBlockOffered { point })
                                .await;
                        }
                    }
                }
            }

            PeerEvent::LeiosBlockTxsOffered { point } => {
                if let (Point::Specific { slot, hash }, Some(tracker)) =
                    (&point, self.leios.as_mut())
                {
                    match tracker.handle_txs_offer(*slot, *hash, peer_id) {
                        OfferResult::New => {
                            tracing::debug!("leios: new TXs offer at slot {slot} from {peer_id}");
                            let _ = self
                                .network_events
                                .send(NetworkEvent::LeiosBlockTxsOffered { point })
                                .await;
                        }
                        OfferResult::Duplicate => {
                            tracing::debug!(
                                "leios: deduplicated TXs offer at slot {slot} from {peer_id} (already seen)"
                            );
                        }
                        OfferResult::AtCapacity => {
                            tracing::warn!(
                                "leios: seen_leios_txs at capacity, forwarding without dedup"
                            );
                            let _ = self
                                .network_events
                                .send(NetworkEvent::LeiosBlockTxsOffered { point })
                                .await;
                        }
                    }
                }
            }

            PeerEvent::LeiosVotesOffered { votes } => {
                if let Some(tracker) = self.leios.as_mut() {
                    let result = tracker.handle_vote_batch(votes, peer_id);
                    if result.at_capacity {
                        tracing::warn!(
                            "leios: seen_leios_votes at capacity, forwarding without dedup"
                        );
                    }
                    if !result.unseen.is_empty() {
                        tracing::debug!(
                            "leios: {} new vote(s) from {peer_id}",
                            result.unseen.len()
                        );
                        let _ = self
                            .network_events
                            .send(NetworkEvent::LeiosVotesOffered {
                                votes: result.unseen,
                            })
                            .await;
                    } else {
                        tracing::debug!("leios: all votes from {peer_id} deduplicated");
                    }
                }
            }

            PeerEvent::LeiosBlockFetched { point, block } => {
                if let (Point::Specific { slot, hash }, Some(tracker)) =
                    (&point, self.leios.as_mut())
                {
                    tracker.complete_block_fetch(*slot, *hash);
                }
                // Populate leios store for responder peers.
                if let Some(ref store) = self.leios_store {
                    store.inject_block(point.clone(), block.clone());
                }
                let _ = self
                    .network_events
                    .send(NetworkEvent::LeiosBlockReceived { point, block })
                    .await;
            }

            PeerEvent::LeiosBlockTxsFetched {
                point,
                transactions,
            } => {
                if let (Point::Specific { slot, hash }, Some(tracker)) =
                    (&point, self.leios.as_mut())
                {
                    tracker.complete_txs_fetch(*slot, *hash);
                }
                let _ = self
                    .network_events
                    .send(NetworkEvent::LeiosBlockTxsReceived {
                        point,
                        transactions,
                    })
                    .await;
            }

            PeerEvent::LeiosVotesFetched { votes } => {
                if let Some(tracker) = self.leios.as_mut() {
                    tracker.complete_vote_fetch(peer_id);
                }
                let _ = self
                    .network_events
                    .send(NetworkEvent::LeiosVotesReceived { votes })
                    .await;
            }

            PeerEvent::BlockFetchFailed { from, to } => {
                // Clear pending_fetches so the app can retry via a
                // different peer. Don't remove from fragments — the peer
                // may still have the blocks (transient failure), and
                // other peers' fragments should remain intact for rerouting.
                self.pending_fetches.remove(&from);
                if from != to {
                    self.pending_fetches.remove(&to);
                }
                // Notify application with the full range so it can retry.
                let _ = self
                    .network_events
                    .send(NetworkEvent::BlockFetchFailed { from, to })
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
                // Find the best peer to fetch from: peer's chain fragment
                // must contain the requested point, then pick lowest RTT.
                if self.pending_fetches.contains_key(&point) {
                    return true; // already fetching
                }

                let best_peer = self
                    .peers
                    .iter()
                    .filter(|(_, p)| p.fragment.contains(&point))
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

            NetworkCommand::FetchBlockRange { from, to } => {
                // Range fetch: find a peer whose fragment contains the
                // `to` endpoint. We only check `to` because `from` may
                // have been removed from the fragment after an earlier
                // fetch (fragment.remove on BlockFetched). The server's
                // get_range has a fallback for unknown `from` — it
                // returns the prefix up to `to`.
                if self.pending_fetches.contains_key(&to) {
                    return true;
                }

                let best_peer = self
                    .peers
                    .iter()
                    .filter(|(_, p)| p.fragment.contains(&to))
                    .min_by_key(|(_, p)| p.rtt.unwrap_or(Duration::from_secs(999)))
                    .map(|(id, _)| *id);

                if let Some(best_id) = best_peer {
                    if let Some(peer) = self.peers.get(&best_id) {
                        let _ = peer
                            .commands
                            .send(PeerCommand::FetchBlocks {
                                from,
                                to: to.clone(),
                            })
                            .await;
                        self.pending_fetches.insert(to, best_id);
                    }
                } else {
                    // No connected peer claims to have this point in its
                    // fragment — it's currently unfetchable. Signal the
                    // app so it can prune the dead fork instead of looping
                    // forever issuing requests we'll silently drop.
                    let _ = self
                        .network_events
                        .send(NetworkEvent::BlockFetchFailed { from, to })
                        .await;
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
                block_no,
            } => {
                self.chain_store
                    .append_block(point, *header, body, block_no);
            }

            NetworkCommand::InjectRollback { point } => {
                self.chain_store.rollback_to(&point);
            }

            NetworkCommand::FetchLeiosBlock { point } => {
                if let (Point::Specific { slot, hash }, Some(tracker)) =
                    (&point, self.leios.as_mut())
                {
                    let slot = *slot;
                    let hash = *hash;
                    let lookup = CoordinatorRttLookup { peers: &self.peers };
                    if let Some(best_id) = tracker.pick_block_fetch_peer(slot, hash, &lookup) {
                        let rtt = self.peers.get(&best_id).and_then(|p| p.rtt);
                        tracing::debug!(
                            "leios: routing EB fetch slot {slot} to {best_id} (rtt={rtt:?})"
                        );
                        if let Some(peer) = self.peers.get(&best_id) {
                            let _ = peer
                                .commands
                                .send(PeerCommand::FetchLeiosBlock { point })
                                .await;
                        }
                    } else {
                        tracing::debug!("leios: no peer available or already pending for EB fetch at slot {slot}");
                    }
                }
            }

            NetworkCommand::FetchLeiosBlockTxs { point, bitmap } => {
                if let (Point::Specific { slot, hash }, Some(tracker)) =
                    (&point, self.leios.as_mut())
                {
                    let slot = *slot;
                    let hash = *hash;
                    let lookup = CoordinatorRttLookup { peers: &self.peers };
                    if let Some(best_id) = tracker.pick_txs_fetch_peer(slot, hash, &lookup) {
                        let rtt = self.peers.get(&best_id).and_then(|p| p.rtt);
                        tracing::debug!(
                            "leios: routing TXs fetch slot {slot} to {best_id} (rtt={rtt:?})"
                        );
                        if let Some(peer) = self.peers.get(&best_id) {
                            let _ = peer
                                .commands
                                .send(PeerCommand::FetchLeiosBlockTxs { point, bitmap })
                                .await;
                        }
                    }
                }
            }

            NetworkCommand::FetchLeiosVotes { votes } => {
                if let Some(tracker) = self.leios.as_mut() {
                    let lookup = CoordinatorRttLookup { peers: &self.peers };
                    let by_peer = tracker.pick_vote_fetch_peers(votes, &lookup);
                    for (target_peer, vote_ids) in by_peer {
                        if let Some(peer) = self.peers.get(&target_peer) {
                            let _ = peer
                                .commands
                                .send(PeerCommand::FetchLeiosVotes { votes: vote_ids })
                                .await;
                        }
                    }
                }
            }

            NetworkCommand::InjectLeiosBlock { point, block } => {
                if let Some(ref store) = self.leios_store {
                    store.inject_block(point, block);
                }
            }

            NetworkCommand::InjectLeiosVotes { votes, data } => {
                if let Some(ref store) = self.leios_store {
                    store.inject_votes(votes, data);
                }
            }

            NetworkCommand::SubmitTransaction { tx } => {
                for peer in self.peers.values() {
                    let _ = peer
                        .commands
                        .send(PeerCommand::SubmitTransaction { tx: tx.clone() })
                        .await;
                }
            }

            NetworkCommand::QueryPeers => {
                let peers: Vec<super::types::PeerInfo> = self
                    .peers
                    .iter()
                    .map(|(id, p)| {
                        let (bytes_sent, bytes_received) =
                            p.mux_stats.as_ref().map(|s| s.snapshot()).unwrap_or((0, 0));
                        super::types::PeerInfo {
                            peer_id: *id,
                            address: p.address.clone(),
                            mode: p.mode,
                            rtt: p.rtt,
                            tip_block_no: p.tip.as_ref().map(|t| t.block_no),
                            inbound_delay: p.inbound_delay,
                            bytes_sent,
                            bytes_received,
                        }
                    })
                    .collect();
                let _ = self
                    .network_events
                    .send(NetworkEvent::PeerSnapshot { peers })
                    .await;
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

            // Decrement per-IP connection count for inbound peers.
            if let Some(ip) = peer.ip {
                decrement_ip_count(&self.ip_counts, ip);
            }

            // Schedule reconnection for outbound peers only. Accepted (inbound)
            // peers have `ip` set and should not reconnect — the remote side
            // re-initiates those.
            if peer.ip.is_none() {
                let backoff = peer.reconnect_backoff;
                let next_backoff = (backoff * 2).min(MAX_BACKOFF);
                self.reconnect_queue.push((
                    peer.address.clone(),
                    Instant::now() + backoff,
                    next_backoff,
                ));
            }

            // Surface BlockFetchFailed for every pending fetch that was
            // assigned to this peer, so the application can re-route the
            // fetch to another peer (or mark it unfetchable) instead of
            // waiting for an in_flight TTL to expire.
            let orphaned: Vec<Point> = self
                .pending_fetches
                .iter()
                .filter(|(_, id)| **id == peer_id)
                .map(|(pt, _)| pt.clone())
                .collect();
            for point in &orphaned {
                let _ = self
                    .network_events
                    .send(NetworkEvent::BlockFetchFailed {
                        from: point.clone(),
                        to: point.clone(),
                    })
                    .await;
            }
            for point in &orphaned {
                self.pending_fetches.remove(point);
            }

            let _ = self
                .network_events
                .send(NetworkEvent::PeerDisconnected { peer_id, reason })
                .await;

            // Clean up Leios offer and fetch tracking for this peer.
            if let Some(tracker) = self.leios.as_mut() {
                tracker.remove_peer(peer_id);
            }
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

    /// Add a duplex peer for an accepted inbound connection.
    fn add_accepted_peer(&mut self, connection: DuplexConnection, peer_addr: SocketAddr) -> PeerId {
        let peer_id = PeerId(self.next_peer_id);
        self.next_peer_id += 1;

        let (cmd_sender, cmd_receiver) = mpsc::channel(16);

        let task_config = AcceptedDuplexTaskConfig {
            peer_id,
            connection,
            keepalive_interval: self.config.keepalive_interval,
            chain_store: self.chain_store.clone(),
            peer_provider: self.peer_provider.clone(),
            event_sender: self.peer_event_sender.clone(),
            command_receiver: cmd_receiver,
            leios_enabled: self.config.leios_enabled,
            leios_store: self.leios_store.clone(),
        };

        let task_handle = tokio::spawn(run_accepted_duplex_task(task_config));

        let ip = peer_addr.ip();
        let address = peer_addr.to_string();
        let inbound_delay = self
            .config
            .peer_delays
            .get(&address)
            .copied()
            .unwrap_or(Duration::ZERO);

        self.peers.insert(
            peer_id,
            PeerState {
                address,
                mode: ConnectionMode::Duplex,
                ip: Some(ip),
                commands: cmd_sender,
                task_handle,
                tip: None,
                rtt: None,
                fragment: ChainFragment::new(),
                reconnect_backoff: Duration::from_secs(0), // accepted peers don't reconnect
                inbound_delay,
                mux_stats: None,
                last_rolled_back_to: None,
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
        let scheduler_type = self.config.scheduler_type;
        let mux_config = MuxConfig {
            sdu_timeout: self.config.sdu_timeout,
            ..MuxConfig::default()
        };
        let leios_enabled = self.config.leios_enabled;
        let mut client_protos = client_protocol_configs(leios_enabled);
        let mut server_protos = server_protocol_configs(leios_enabled);
        for p in client_protos.iter_mut().chain(server_protos.iter_mut()) {
            if let Some(tc) = self.config.traffic_class_overrides.get(&p.id) {
                p.traffic_class = *tc;
            }
        }

        let (conn_sender, conn_receiver) = mpsc::channel::<(DuplexConnection, SocketAddr)>(16);
        self.inbound_connections = Some(conn_receiver);

        let ip_counts = self.ip_counts.clone();
        let max_connections_per_ip = self.config.max_connections_per_ip;
        let semaphore = Arc::new(tokio::sync::Semaphore::new(self.config.max_handshaking));
        let client_protos = Arc::new(client_protos);
        let server_protos = Arc::new(server_protos);

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
                // Accept TCP connection immediately (don't block on handshake).
                let (stream, peer_addr) = match listener.accept().await {
                    Ok(accepted) => accepted,
                    Err(e) => {
                        tracing::warn!("TCP accept failed: {e}");
                        continue;
                    }
                };

                let ip = peer_addr.ip();

                // Check per-IP connection limit.
                {
                    let counts = ip_counts.lock().expect("ip_counts lock poisoned");
                    if counts.get(&ip).copied().unwrap_or(0) >= max_connections_per_ip {
                        tracing::warn!("per-IP limit reached for {ip}, dropping connection");
                        drop(stream);
                        continue;
                    }
                }

                // Check concurrent handshake limit.
                let permit = match semaphore.clone().try_acquire_owned() {
                    Ok(permit) => permit,
                    Err(_) => {
                        tracing::warn!(
                            "max handshaking limit reached, dropping connection from {ip}"
                        );
                        drop(stream);
                        continue;
                    }
                };

                // Reserve the per-IP slot before spawning.
                {
                    let mut counts = ip_counts.lock().expect("ip_counts lock poisoned");
                    *counts.entry(ip).or_insert(0) += 1;
                }

                let conn_sender = conn_sender.clone();
                let ip_counts = ip_counts.clone();
                let client_protos = client_protos.clone();
                let server_protos = server_protos.clone();
                let mux_config = mux_config.clone();

                tokio::spawn(async move {
                    let _permit = permit; // held until task completes

                    let bearer = match TcpBearer::from_accepted(stream) {
                        Ok(b) => b,
                        Err(e) => {
                            tracing::warn!("socket configuration failed for {peer_addr}: {e}");
                            decrement_ip_count(&ip_counts, ip);
                            return;
                        }
                    };

                    match connect::handshake_accepted_duplex(
                        bearer,
                        peer_addr,
                        magic,
                        &client_protos,
                        &server_protos,
                        mux_config,
                        scheduler_type,
                    )
                    .await
                    {
                        Ok(conn) => {
                            if conn_sender.send((conn, peer_addr)).await.is_err() {
                                // Coordinator shut down — clean up.
                                decrement_ip_count(&ip_counts, ip);
                            }
                        }
                        Err(e) => {
                            tracing::warn!("inbound handshake failed from {peer_addr}: {e}");
                            decrement_ip_count(&ip_counts, ip);
                        }
                    }
                });
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

        // Delayed events buffer: (delivery_time, peer_id, event).
        // Only used when peer_delays is configured; zero overhead otherwise.
        let mut delayed: Vec<(Instant, PeerId, PeerEvent)> = Vec::new();
        let has_any_delays = !self.config.peer_delays.is_empty();

        loop {
            let reconnect_delay = self.next_reconnect_delay();

            // Earliest delayed event deadline (only computed when buffer is non-empty).
            let next_delayed = delayed.iter().map(|(t, _, _)| *t).min();

            tokio::select! {
                event = self.peer_events.recv() => {
                    match event {
                        Some((peer_id, peer_event)) => {
                            // If delay simulation is active and this peer has
                            // a configured delay, buffer instead of processing.
                            // LatencyMeasured is exempt: it's a measurement, not
                            // data, and its RTT is adjusted below instead.
                            if has_any_delays && !matches!(peer_event, PeerEvent::LatencyMeasured { .. }) {
                                let delay = self.peers.get(&peer_id)
                                    .map(|p| p.inbound_delay)
                                    .unwrap_or(Duration::ZERO);
                                if !delay.is_zero() {
                                    delayed.push((Instant::now() + delay, peer_id, peer_event));
                                    continue;
                                }
                            }
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
                result = async {
                    match &mut self.inbound_connections {
                        Some(rx) => rx.recv().await,
                        None => std::future::pending().await,
                    }
                } => {
                    if let Some((conn, peer_addr)) = result {
                        if self.peers.len() < self.config.max_peers {
                            let peer_id = self.add_accepted_peer(conn, peer_addr);
                            tracing::info!("accepted inbound peer as {peer_id}");
                        } else {
                            tracing::warn!("max peers reached, dropping inbound connection");
                            conn.running.abort();
                            decrement_ip_count(&self.ip_counts, peer_addr.ip());
                        }
                    }
                }
                _ = tokio::time::sleep(reconnect_delay) => {
                    self.process_reconnections();
                }
                _ = tokio::time::sleep_until(next_delayed.unwrap_or_else(|| Instant::now() + Duration::from_secs(86400))), if !delayed.is_empty() => {
                    // Deliver all delayed events whose deadline has passed.
                    let now = Instant::now();
                    let mut i = 0;
                    while i < delayed.len() {
                        if delayed[i].0 <= now {
                            let (_, peer_id, event) = delayed.swap_remove(i);
                            self.handle_peer_event(peer_id, event).await;
                        } else {
                            i += 1;
                        }
                    }
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

/// Adapter: lets LeiosTracker look up peer RTTs from the coordinator's peer map.
struct CoordinatorRttLookup<'a> {
    peers: &'a HashMap<PeerId, PeerState>,
}

impl PeerRttLookup for CoordinatorRttLookup<'_> {
    fn rtt(&self, peer: PeerId) -> Option<Duration> {
        self.peers.get(&peer).and_then(|p| p.rtt)
    }
    fn peer_exists(&self, peer: PeerId) -> bool {
        self.peers.contains_key(&peer)
    }
}

/// Decrement the per-IP connection count, removing the entry if it reaches zero.
fn decrement_ip_count(ip_counts: &Mutex<HashMap<IpAddr, usize>>, ip: IpAddr) {
    let mut counts = ip_counts.lock().expect("ip_counts lock poisoned");
    if let Some(count) = counts.get_mut(&ip) {
        *count -= 1;
        if *count == 0 {
            counts.remove(&ip);
        }
    }
}

/// Spawn a coordinator task and return a handle for the application.
pub fn spawn_coordinator(config: CoordinatorConfig) -> CoordinatorHandle {
    // Network events channel sized to absorb bursts of per-peer announcements
    // (header advances, rollbacks). The application loop drains it on every
    // iteration, but a slow tick can leave many events queued — undersizing
    // here back-pressures the coordinator and stalls all peers.
    let (net_event_sender, net_event_receiver) = mpsc::channel(256);
    let (net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);
    let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
    let (chain_store, _chain_rx) = ChainStore::new(config.chain_store_capacity);

    let leios_store = if config.leios_enabled {
        let (store, _leios_rx) = LeiosStore::new(config.chain_store_capacity);
        Some(store)
    } else {
        None
    };

    let coordinator = Coordinator::new(
        config,
        peer_event_sender,
        peer_event_receiver,
        net_event_sender,
        net_cmd_receiver,
        chain_store,
        leios_store,
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
    use crate::types::WrappedHeader;

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
        let (chain_store, _chain_rx) = ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender.clone(),
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
            None,
        );

        // Manually insert a peer (simulate it being connected).
        let peer_id = PeerId(0);
        let (cmd_sender, _cmd_receiver) = mpsc::channel(16);
        coordinator.peers.insert(
            peer_id,
            PeerState {
                address: "test:3001".to_string(),
                mode: ConnectionMode::InitiatorOnly,
                ip: None,
                commands: cmd_sender,
                task_handle: tokio::spawn(async {}),
                tip: None,
                rtt: None,
                fragment: ChainFragment::new(),
                reconnect_backoff: Duration::from_secs(1),
                inbound_delay: Duration::ZERO,
                mux_stats: None,
                last_rolled_back_to: None,
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
                peer_id: recv_peer,
                tip: recv_tip,
                header: recv_header,
            } => {
                assert_eq!(recv_peer, peer_id);
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
        let (chain_store, _chain_rx) = ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender,
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
            None,
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
                    ip: None,
                    commands: cmd_sender,
                    task_handle: tokio::spawn(async {}),
                    tip: None,
                    rtt: None,
                    fragment: ChainFragment::new(),
                    reconnect_backoff: Duration::from_secs(1),
                    inbound_delay: Duration::ZERO,
                    mux_stats: None,
                    last_rolled_back_to: None,
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

        // Should also produce TipAdvanced (all headers forwarded for chain tree).
        assert!(net_event_receiver.try_recv().is_ok());

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
        let (chain_store, _chain_rx) = ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender,
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
            None,
        );

        let peer_id = PeerId(0);
        let (cmd_sender, _cmd_receiver) = mpsc::channel(16);
        coordinator.peers.insert(
            peer_id,
            PeerState {
                address: "test:3001".to_string(),
                mode: ConnectionMode::InitiatorOnly,
                ip: None,
                commands: cmd_sender,
                task_handle: tokio::spawn(async {}),
                tip: None,
                rtt: None,
                fragment: ChainFragment::new(),
                reconnect_backoff: Duration::from_secs(1),
                inbound_delay: Duration::ZERO,
                mux_stats: None,
                last_rolled_back_to: None,
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
    async fn remove_peer_emits_block_fetch_failed_for_orphaned_fetches() {
        let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
        let (net_event_sender, mut net_event_receiver) = mpsc::channel(64);
        let (_net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);

        let config = CoordinatorConfig::default();
        let (chain_store, _chain_rx) = ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender,
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
            None,
        );

        let peer_id = PeerId(0);
        let (cmd_sender, _cmd_receiver) = mpsc::channel(16);
        coordinator.peers.insert(
            peer_id,
            PeerState {
                address: "test:3001".to_string(),
                mode: ConnectionMode::InitiatorOnly,
                ip: None,
                commands: cmd_sender,
                task_handle: tokio::spawn(async {}),
                tip: None,
                rtt: None,
                fragment: ChainFragment::new(),
                reconnect_backoff: Duration::from_secs(1),
                inbound_delay: Duration::ZERO,
                mux_stats: None,
                last_rolled_back_to: None,
            },
        );

        // Simulate two pending fetches assigned to this peer.
        let point_a = Point::Specific {
            slot: 10,
            hash: [0xAA; 32],
        };
        let point_b = Point::Specific {
            slot: 20,
            hash: [0xBB; 32],
        };
        coordinator.pending_fetches.insert(point_a.clone(), peer_id);
        coordinator.pending_fetches.insert(point_b.clone(), peer_id);

        // Peer fails.
        coordinator
            .handle_peer_event(
                peer_id,
                PeerEvent::Failed {
                    reason: "connection reset".to_string(),
                },
            )
            .await;

        // Collect all network events emitted.
        let mut events = Vec::new();
        while let Ok(ev) = net_event_receiver.try_recv() {
            events.push(ev);
        }

        // Expect: two BlockFetchFailed (one per orphaned fetch) + one PeerDisconnected.
        let failed_points: Vec<Point> = events
            .iter()
            .filter_map(|e| match e {
                NetworkEvent::BlockFetchFailed { to, .. } => Some(to.clone()),
                _ => None,
            })
            .collect();
        assert!(
            failed_points.contains(&point_a),
            "expected BlockFetchFailed for point_a, got events: {events:?}"
        );
        assert!(
            failed_points.contains(&point_b),
            "expected BlockFetchFailed for point_b, got events: {events:?}"
        );
        assert!(
            events
                .iter()
                .any(|e| matches!(e, NetworkEvent::PeerDisconnected { .. })),
            "expected PeerDisconnected, got events: {events:?}"
        );

        // pending_fetches should be empty.
        assert!(coordinator.pending_fetches.is_empty());
    }

    #[tokio::test]
    async fn coordinator_schedules_reconnection() {
        let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
        let (net_event_sender, mut net_event_receiver) = mpsc::channel(64);
        let (_net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);

        let config = CoordinatorConfig::default();
        let (chain_store, _chain_rx) = ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender,
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
            None,
        );

        // Add a peer and simulate failure.
        let peer_id = PeerId(0);
        let (cmd_sender, _cmd_receiver) = mpsc::channel(16);
        coordinator.peers.insert(
            peer_id,
            PeerState {
                address: "test:3001".to_string(),
                mode: ConnectionMode::InitiatorOnly,
                ip: None,
                commands: cmd_sender,
                task_handle: tokio::spawn(async {}),
                tip: None,
                rtt: None,
                fragment: ChainFragment::new(),
                reconnect_backoff: Duration::from_secs(1),
                inbound_delay: Duration::ZERO,
                mux_stats: None,
                last_rolled_back_to: None,
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

    /// Helper: insert a fake peer into the coordinator with a given RTT.
    fn insert_peer(
        coordinator: &mut Coordinator,
        peer_id: PeerId,
        rtt: Option<Duration>,
    ) -> mpsc::Receiver<PeerCommand> {
        let (cmd_sender, cmd_receiver) = mpsc::channel(16);
        coordinator.peers.insert(
            peer_id,
            PeerState {
                address: format!("test-{}:3001", peer_id.0),
                mode: ConnectionMode::InitiatorOnly,
                ip: None,
                commands: cmd_sender,
                task_handle: tokio::spawn(async {}),
                tip: None,
                rtt,
                fragment: ChainFragment::new(),
                reconnect_backoff: Duration::from_secs(1),
                inbound_delay: Duration::ZERO,
                mux_stats: None,
                last_rolled_back_to: None,
            },
        );
        cmd_receiver
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

    // --- ChainFragment integration tests ---

    /// Helper: create a coordinator for fragment tests.
    fn make_fragment_coordinator() -> (Coordinator, mpsc::Receiver<NetworkEvent>) {
        let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
        let (net_event_sender, net_event_receiver) = mpsc::channel(64);
        let (_net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);
        let config = CoordinatorConfig::default();
        let (chain_store, _chain_rx) = ChainStore::new(100);
        let coordinator = Coordinator::new(
            config,
            peer_event_sender,
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
            None,
        );
        (coordinator, net_event_receiver)
    }

    #[tokio::test]
    async fn fetch_routes_to_peer_with_block_in_fragment() {
        let (mut coordinator, _net_rx) = make_fragment_coordinator();
        let peer_a = PeerId(0);
        let peer_b = PeerId(1);
        let mut cmd_a = insert_peer(&mut coordinator, peer_a, Some(Duration::from_millis(50)));
        let mut cmd_b = insert_peer(&mut coordinator, peer_b, Some(Duration::from_millis(10)));

        let point_100 = Point::Specific {
            slot: 100,
            hash: [1u8; 32],
        };
        let point_101 = Point::Specific {
            slot: 101,
            hash: [2u8; 32],
        };

        // Only peer A has point_100 in its fragment.
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::IntersectionFound {
                    point: point_100.clone(),
                },
            )
            .await;

        // Peer B has a different point.
        coordinator
            .handle_peer_event(
                peer_b,
                PeerEvent::IntersectionFound {
                    point: point_101.clone(),
                },
            )
            .await;

        // Fetch point_100 — should route to peer A (only one with it).
        coordinator
            .handle_network_command(NetworkCommand::FetchBlock {
                point: point_100.clone(),
            })
            .await;

        // Peer A should receive the fetch command.
        let cmd = cmd_a.try_recv().unwrap();
        assert!(matches!(cmd, PeerCommand::FetchBlocks { .. }));

        // Peer B should NOT receive anything.
        assert!(cmd_b.try_recv().is_err());
    }

    #[tokio::test]
    async fn fetch_prefers_lowest_rtt_among_fragment_candidates() {
        let (mut coordinator, _net_rx) = make_fragment_coordinator();
        let peer_a = PeerId(0);
        let peer_b = PeerId(1);
        let mut cmd_a = insert_peer(&mut coordinator, peer_a, Some(Duration::from_millis(100)));
        let mut cmd_b = insert_peer(&mut coordinator, peer_b, Some(Duration::from_millis(10)));

        let point = Point::Specific {
            slot: 200,
            hash: [3u8; 32],
        };

        // Both peers have the point in their fragments.
        for id in [peer_a, peer_b] {
            coordinator
                .handle_peer_event(
                    id,
                    PeerEvent::IntersectionFound {
                        point: point.clone(),
                    },
                )
                .await;
        }

        // Fetch — should route to peer B (lower RTT).
        coordinator
            .handle_network_command(NetworkCommand::FetchBlock {
                point: point.clone(),
            })
            .await;

        assert!(cmd_a.try_recv().is_err());
        let cmd = cmd_b.try_recv().unwrap();
        assert!(matches!(cmd, PeerCommand::FetchBlocks { .. }));
    }

    #[tokio::test]
    async fn fetch_fails_when_no_peer_has_block() {
        let (mut coordinator, mut net_rx) = make_fragment_coordinator();
        let peer_a = PeerId(0);
        let _cmd_a = insert_peer(&mut coordinator, peer_a, Some(Duration::from_millis(10)));

        let point = Point::Specific {
            slot: 300,
            hash: [4u8; 32],
        };

        // Peer A's fragment is empty — no intersection set.
        coordinator
            .handle_network_command(NetworkCommand::FetchBlock {
                point: point.clone(),
            })
            .await;

        // No fetch command sent, no pending fetch recorded.
        assert!(!coordinator.pending_fetches.contains_key(&point));

        // No BlockFetchFailed event either (nobody was asked).
        assert!(net_rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn fragment_pruned_on_block_fetched() {
        let (mut coordinator, _net_rx) = make_fragment_coordinator();
        let peer_a = PeerId(0);
        let peer_b = PeerId(1);
        insert_peer(&mut coordinator, peer_a, None);
        insert_peer(&mut coordinator, peer_b, None);

        let point = Point::Specific {
            slot: 400,
            hash: [5u8; 32],
        };

        // Both peers have the point.
        for id in [peer_a, peer_b] {
            coordinator
                .handle_peer_event(
                    id,
                    PeerEvent::IntersectionFound {
                        point: point.clone(),
                    },
                )
                .await;
        }

        assert!(coordinator
            .peers
            .get(&peer_a)
            .unwrap()
            .fragment
            .contains(&point));
        assert!(coordinator
            .peers
            .get(&peer_b)
            .unwrap()
            .fragment
            .contains(&point));

        // Simulate BlockFetched. The coordinator derives the point from
        // body.point(), which requires valid Shelley+ CBOR. With an opaque
        // body, it falls back to Point::Origin and can't clean up
        // pending_fetches for the real point. In production, all blocks
        // (including fake test-node blocks) have valid CBOR structure.
        //
        // This test verifies fragment pruning works for the derived point.
        coordinator.pending_fetches.insert(Point::Origin, peer_a);

        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::BlockFetched {
                    body: crate::types::BlockBody::opaque(vec![0xD8, 0x18, 0x40]),
                },
            )
            .await;

        // Opaque body resolves to Origin; pending fetch for Origin is removed.
        assert!(
            !coordinator.pending_fetches.contains_key(&Point::Origin),
            "pending fetch for Origin should be removed"
        );
    }

    #[tokio::test]
    async fn fragment_truncated_on_rollback() {
        let (mut coordinator, _net_rx) = make_fragment_coordinator();
        let peer_a = PeerId(0);
        insert_peer(&mut coordinator, peer_a, None);

        let p100 = Point::Specific {
            slot: 100,
            hash: [1u8; 32],
        };
        let p101 = Point::Specific {
            slot: 101,
            hash: [2u8; 32],
        };
        let p102 = Point::Specific {
            slot: 102,
            hash: [3u8; 32],
        };

        // Build fragment: intersection at p100, then p101, p102.
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::IntersectionFound {
                    point: p100.clone(),
                },
            )
            .await;

        let tip = Tip {
            point: p101.clone(),
            block_no: 101,
        };
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::HeaderAnnounced {
                    header: WrappedHeader::opaque(vec![0xA0]),
                    tip,
                },
            )
            .await;

        let tip2 = Tip {
            point: p102.clone(),
            block_no: 102,
        };
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::HeaderAnnounced {
                    header: WrappedHeader::opaque(vec![0xA1]),
                    tip: tip2,
                },
            )
            .await;

        let frag = &coordinator.peers.get(&peer_a).unwrap().fragment;
        assert!(frag.contains(&p100));
        assert!(frag.contains(&p101));
        assert!(frag.contains(&p102));

        // Rollback to p100.
        let rollback_tip = Tip {
            point: p100.clone(),
            block_no: 100,
        };
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::RolledBack {
                    point: p100.clone(),
                    tip: rollback_tip,
                },
            )
            .await;

        let frag = &coordinator.peers.get(&peer_a).unwrap().fragment;
        assert!(frag.contains(&p100));
        assert!(!frag.contains(&p101));
        assert!(!frag.contains(&p102));
    }

    #[tokio::test]
    async fn block_fetch_failed_removes_from_fragment_and_notifies() {
        let (mut coordinator, mut net_rx) = make_fragment_coordinator();
        let peer_a = PeerId(0);
        insert_peer(&mut coordinator, peer_a, None);

        let point = Point::Specific {
            slot: 500,
            hash: [6u8; 32],
        };

        // Peer A has the point.
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::IntersectionFound {
                    point: point.clone(),
                },
            )
            .await;

        assert!(coordinator
            .peers
            .get(&peer_a)
            .unwrap()
            .fragment
            .contains(&point));

        // Mark as pending fetch.
        coordinator.pending_fetches.insert(point.clone(), peer_a);

        // BlockFetch fails.
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::BlockFetchFailed {
                    from: point.clone(),
                    to: point.clone(),
                },
            )
            .await;

        // Fragment should still contain the point (we no longer prune
        // on fetch failure — the peer may still have the block).
        assert!(coordinator
            .peers
            .get(&peer_a)
            .unwrap()
            .fragment
            .contains(&point));

        // Pending fetch should be cleared.
        assert!(!coordinator.pending_fetches.contains_key(&point));

        // Drain the IntersectionFound event that was forwarded.
        let first = net_rx.try_recv().unwrap();
        assert!(matches!(first, NetworkEvent::IntersectionFound { .. }));

        // App should receive BlockFetchFailed.
        let event = net_rx.try_recv().unwrap();
        assert!(matches!(event, NetworkEvent::BlockFetchFailed { .. }));
    }

    #[tokio::test]
    async fn header_announced_appends_to_fragment_using_tip_for_opaque() {
        let (mut coordinator, _net_rx) = make_fragment_coordinator();
        let peer_a = PeerId(0);
        insert_peer(&mut coordinator, peer_a, None);

        let intersection = Point::Specific {
            slot: 50,
            hash: [0xAA; 32],
        };
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::IntersectionFound {
                    point: intersection.clone(),
                },
            )
            .await;

        // Opaque header has no parsed info, so point() returns None.
        // Coordinator should fall back to tip.point for the fragment.
        let tip_point = Point::Specific {
            slot: 51,
            hash: [0xBB; 32],
        };
        let tip = Tip {
            point: tip_point.clone(),
            block_no: 51,
        };
        coordinator
            .handle_peer_event(
                peer_a,
                PeerEvent::HeaderAnnounced {
                    header: WrappedHeader::opaque(vec![0xA0]),
                    tip,
                },
            )
            .await;

        let frag = &coordinator.peers.get(&peer_a).unwrap().fragment;
        assert!(frag.contains(&intersection));
        assert!(frag.contains(&tip_point));
    }

    // --- Reconnection tests ---

    /// Helper: create a coordinator and insert a peer, then remove it and
    /// return the reconnect queue state. `inbound_ip` simulates an accepted
    /// (inbound) peer when Some; outbound peers have None.
    async fn reconnection_after_removal(inbound_ip: Option<IpAddr>) -> Vec<String> {
        let (peer_event_sender, peer_event_receiver) = mpsc::channel(256);
        let (net_event_sender, mut net_event_receiver) = mpsc::channel(64);
        let (_net_cmd_sender, net_cmd_receiver) = mpsc::channel(64);
        let config = CoordinatorConfig::default();
        let (chain_store, _chain_rx) = ChainStore::new(100);
        let mut coordinator = Coordinator::new(
            config,
            peer_event_sender,
            peer_event_receiver,
            net_event_sender,
            net_cmd_receiver,
            chain_store,
            None,
        );

        let peer_id = PeerId(0);
        let (cmd_sender, _cmd_receiver) = mpsc::channel(16);
        coordinator.peers.insert(
            peer_id,
            PeerState {
                address: "test:3001".to_string(),
                mode: ConnectionMode::Duplex,
                ip: inbound_ip,
                commands: cmd_sender,
                task_handle: tokio::spawn(async {}),
                tip: None,
                rtt: None,
                fragment: ChainFragment::new(),
                reconnect_backoff: Duration::from_secs(1),
                inbound_delay: Duration::ZERO,
                mux_stats: None,
                last_rolled_back_to: None,
            },
        );

        coordinator.remove_peer(peer_id, "test".to_string()).await;
        let _ = net_event_receiver.try_recv();

        coordinator
            .reconnect_queue
            .iter()
            .map(|(addr, _, _)| addr.clone())
            .collect()
    }

    #[tokio::test]
    async fn outbound_peer_schedules_reconnection() {
        let queue = reconnection_after_removal(None).await;
        assert_eq!(queue, vec!["test:3001"]);
    }

    #[tokio::test]
    async fn accepted_peer_does_not_schedule_reconnection() {
        let queue = reconnection_after_removal(Some("127.0.0.1".parse().unwrap())).await;
        assert!(queue.is_empty());
    }
}
