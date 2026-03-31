//! Per-peer protocol handling.
//!
//! Manages individual peer connections: connection setup, protocol
//! sub-tasks (initiator, responder, duplex), and server-side handlers.
//! The multi-peer coordination layer lives in the `multi_peer` module.

pub(crate) mod command_dispatch;
pub mod connect;
pub(crate) mod duplex_task;
pub(crate) mod peer_task;
pub mod server_handlers;
pub mod types;

use std::fmt;

pub use types::{PeerCommand, PeerEvent};

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

/// Errors from the peer layer.
#[derive(Debug, thiserror::Error)]
pub enum PeerError {
    #[error("protocol error: {0}")]
    Protocol(#[from] crate::protocols::ProtocolError),

    #[error("mux error: {0}")]
    Mux(#[from] crate::mux::MuxError),

    #[error("connection failed: {0}")]
    Connection(String),

    #[error("coordinator shut down")]
    Shutdown,

    #[error("peer {0} disconnected")]
    Disconnected(PeerId),
}
