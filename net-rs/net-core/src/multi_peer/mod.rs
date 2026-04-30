//! Multi-peer coordination layer.
//!
//! Manages N peer connections simultaneously, aggregates their protocol
//! events, and exposes a peer-agnostic interface to the application.
//!
//! Architecture: thread-per-peer with a shared coordinator task.
//! Each peer runs an independent tokio task tree; the coordinator
//! aggregates state via channels and makes cross-peer decisions.
//!
//! ```text
//! Application
//!     ↑ NetworkEvent (peer-agnostic)
//!     ↓ NetworkCommand
//! Coordinator task
//!     ↑ (PeerId, PeerEvent) via shared fan-in channel
//!     ↓ PeerCommand via per-peer channel
//! Per-Peer Tasks (in `peer` module)
//! ```

pub(crate) mod chain_fragment;
mod coordinator;
pub(crate) mod leios_tracker;
pub mod types;

pub use coordinator::spawn_coordinator;

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

use tokio::sync::mpsc;
pub use types::{NetworkCommand, NetworkEvent};

use crate::mux::scheduler::{SchedulerType, TrafficClass};
use crate::mux::ProtocolId;
use crate::store::leios_store::TxBodyResolver;

/// Configuration for the coordinator.
#[derive(Clone)]
pub struct CoordinatorConfig {
    /// Network magic for handshake (e.g. 764824073 for mainnet).
    pub network_magic: u64,
    /// Maximum number of managed peers.
    pub max_peers: usize,
    /// Interval between KeepAlive pings per peer.
    pub keepalive_interval: Duration,
    /// SDU timeout for mux (long at tip — blocks are infrequent).
    pub sdu_timeout: Duration,
    /// Address to listen on for inbound (responder) connections. None = don't listen.
    pub listen_address: Option<String>,
    /// Maximum blocks to retain in the chain store (for serving to responder peers).
    pub chain_store_capacity: usize,
    /// If true, outbound connections use duplex mode (both client and server protocols).
    pub duplex: bool,
    /// Enable Leios protocols (LeiosNotify, LeiosFetch). Default: false.
    pub leios_enabled: bool,
    /// Slot window for Leios announcement deduplication. Offers older than
    /// `max_seen_slot - leios_dedup_window` are pruned. Default: 1000.
    pub leios_dedup_window: u64,
    /// Log a `LeiosStore` stats line every Nth `bump_version` call. `0`
    /// disables stats logging (default). Useful for memory diagnostics.
    pub leios_store_stats_log_interval: u64,
    /// Per-protocol traffic class overrides. Applied on top of defaults
    /// from `client_protocol_configs` / `server_protocol_configs`.
    pub traffic_class_overrides: HashMap<ProtocolId, TrafficClass>,
    /// Which scheduler to use for mux connections.
    pub scheduler_type: SchedulerType,
    /// Maximum concurrent in-flight inbound handshakes.
    pub max_handshaking: usize,
    /// Maximum connections (handshaking + established) from a single IP.
    pub max_connections_per_ip: usize,
    /// Simulated inbound delay per peer address. Events from matching peers
    /// are delayed by the specified duration before processing. Default: empty
    /// (no delay). Used for local network simulation.
    pub peer_delays: HashMap<String, Duration>,
    /// Resolver for tx bodies by hash. Lets receiver-side EB tx fetches
    /// be served from the application's mempool rather than a duplicate
    /// `LeiosStore::block_txs`. None = receivers cannot re-serve EB txs.
    pub tx_body_resolver: Option<Arc<dyn TxBodyResolver>>,
}

impl Default for CoordinatorConfig {
    fn default() -> Self {
        Self {
            network_magic: 764824073, // mainnet
            max_peers: 20,
            keepalive_interval: Duration::from_secs(20),
            sdu_timeout: Duration::from_secs(900),
            listen_address: None,
            chain_store_capacity: 2160,
            duplex: false,
            leios_enabled: false,
            leios_dedup_window: 1000,
            leios_store_stats_log_interval: 0,
            traffic_class_overrides: HashMap::new(),
            scheduler_type: SchedulerType::default(),
            max_handshaking: 64,
            max_connections_per_ip: 3,
            peer_delays: HashMap::new(),
            tx_body_resolver: None,
        }
    }
}

/// Handle for interacting with a running coordinator.
///
/// The application sends `NetworkCommand`s and receives `NetworkEvent`s.
/// Dropping the handle will cause the coordinator to shut down.
pub struct CoordinatorHandle {
    /// Receive peer-agnostic network events.
    pub events: mpsc::Receiver<NetworkEvent>,
    /// Send commands to the coordinator.
    pub commands: mpsc::Sender<NetworkCommand>,
}
