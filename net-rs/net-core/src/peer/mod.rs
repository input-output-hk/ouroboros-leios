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
//! Per-Peer Tasks
//! ```

pub mod connect;
mod coordinator;
pub(crate) mod peer_task;
pub mod types;

pub use coordinator::spawn_coordinator;

use std::fmt;
use std::time::Duration;

use tokio::sync::mpsc;
pub use types::{NetworkCommand, NetworkEvent, PeerCommand, PeerEvent};

/// Unique identifier for a connected peer within a coordinator session.
///
/// Monotonically increasing — not a network address. Two connections to
/// the same address get different PeerIds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PeerId(pub u64);

impl fmt::Display for PeerId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "peer-{}", self.0)
    }
}

/// Connection mode determines which protocol roles the peer task runs.
///
/// In Cardano (V10+), TCP direction doesn't restrict protocol roles.
/// Duplex mode runs both initiator and responder protocols on one
/// connection — each protocol ID registered twice, once per mux direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnectionMode {
    /// We initiated TCP, run client-side (initiator) protocols only.
    InitiatorOnly,
    /// They connected to us, run server-side (responder) protocols only.
    ResponderOnly,
    /// Both directions on one connection (not implemented initially).
    Duplex,
}

/// Configuration for the coordinator.
#[derive(Debug, Clone)]
pub struct CoordinatorConfig {
    /// Network magic for handshake (e.g. 764824073 for mainnet).
    pub network_magic: u64,
    /// Maximum number of managed peers.
    pub max_peers: usize,
    /// Interval between KeepAlive pings per peer.
    pub keepalive_interval: Duration,
    /// SDU timeout for mux (long at tip — blocks are infrequent).
    pub sdu_timeout: Duration,
}

impl Default for CoordinatorConfig {
    fn default() -> Self {
        Self {
            network_magic: 764824073, // mainnet
            max_peers: 20,
            keepalive_interval: Duration::from_secs(20),
            sdu_timeout: Duration::from_secs(900),
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

/// Errors from the peer/coordinator layer.
#[derive(Debug, thiserror::Error)]
pub enum PeerError {
    #[error("protocol error: {0}")]
    Protocol(#[from] crate::protocol::ProtocolError),

    #[error("mux error: {0}")]
    Mux(#[from] crate::mux::MuxError),

    #[error("connection failed: {0}")]
    Connection(String),

    #[error("coordinator shut down")]
    Shutdown,

    #[error("peer {0} disconnected")]
    Disconnected(PeerId),
}
