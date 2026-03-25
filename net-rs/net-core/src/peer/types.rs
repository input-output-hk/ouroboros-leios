//! Event and command types for the multi-peer coordinator.
//!
//! Two channel boundaries:
//! - Peer tasks ↔ Coordinator: `PeerEvent` (up) and `PeerCommand` (down)
//! - Coordinator ↔ Application: `NetworkEvent` (up) and `NetworkCommand` (down)

use std::time::Duration;

use crate::protocols::peersharing::PeerAddress;
use crate::types::{BlockBody, Point, Tip, WrappedHeader};

use super::PeerId;

// ---------------------------------------------------------------------------
// Peer ↔ Coordinator
// ---------------------------------------------------------------------------

/// Events sent from a per-peer task to the coordinator.
///
/// These abstract over raw protocol messages — the peer task translates
/// protocol-level details (e.g. `MsgRollForward`) into coordinator-relevant
/// events. Used by both initiator and responder peer tasks.
#[derive(Debug)]
pub enum PeerEvent {
    /// Connection established and handshake completed.
    Connected,

    /// ChainSync: peer announced a new header (from `MsgRollForward`).
    HeaderAnnounced { header: WrappedHeader, tip: Tip },

    /// ChainSync: peer rolled back (from `MsgRollBackward`).
    RolledBack { point: Point, tip: Tip },

    /// BlockFetch: a requested block arrived.
    BlockFetched { point: Point, body: BlockBody },

    /// KeepAlive: measured round-trip time.
    LatencyMeasured { rtt: Duration },

    /// PeerSharing: received peer addresses.
    PeersDiscovered { peers: Vec<PeerAddress> },

    /// TxSubmission server: received a transaction from a client.
    TransactionReceived { body: Vec<u8> },

    /// Peer misbehaved or connection broke.
    Failed { reason: String },
}

/// Commands sent from the coordinator to a per-peer task.
#[derive(Debug)]
pub enum PeerCommand {
    /// Fetch a range of blocks via BlockFetch.
    FetchBlocks { from: Point, to: Point },

    /// Request peer addresses via PeerSharing.
    RequestPeers { amount: u8 },

    /// Gracefully disconnect this peer.
    Disconnect,
}

// ---------------------------------------------------------------------------
// Coordinator ↔ Application
// ---------------------------------------------------------------------------

/// Events sent from the coordinator to the application.
///
/// Peer-agnostic: the application sees chains and blocks, not peers.
/// Peer identity is included only for informational/logging purposes
/// (connect/disconnect events).
#[derive(Debug)]
pub enum NetworkEvent {
    /// A peer connected successfully.
    PeerConnected { peer_id: PeerId, address: String },

    /// A peer disconnected (error or graceful).
    PeerDisconnected { peer_id: PeerId, reason: String },

    /// A new chain tip was announced (deduplicated across peers).
    TipAdvanced { tip: Tip, header: WrappedHeader },

    /// Chain rolled back to a point.
    RolledBack { point: Point, tip: Tip },

    /// A requested block was fetched.
    BlockReceived { point: Point, body: BlockBody },

    /// New peers discovered via PeerSharing.
    PeersDiscovered { peers: Vec<PeerAddress> },

    /// A transaction was received from an inbound peer (via TxSubmission server).
    TransactionReceived { peer_id: PeerId, body: Vec<u8> },
}

/// Commands sent from the application to the coordinator.
#[derive(Debug)]
pub enum NetworkCommand {
    /// Add a peer by address. The coordinator will connect and manage it.
    AddPeer { address: String },

    /// Fetch a specific block. The coordinator picks the best peer.
    FetchBlock { point: Point },

    /// Request peers from connected nodes (triggers PeerSharing).
    DiscoverPeers,

    /// Inject a block into the chain store (for responder peers to serve).
    /// Used by block generators or other local producers.
    InjectBlock {
        point: Point,
        header: Box<WrappedHeader>,
        body: BlockBody,
    },

    /// Roll back the chain store to a point (for responder peers).
    InjectRollback { point: Point },

    /// Shut down all peers and stop the coordinator.
    Shutdown,
}
