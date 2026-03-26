//! Event and command types for the coordinator ↔ application boundary.

use std::collections::BTreeMap;

use crate::peer::PeerId;
use crate::protocols::peersharing::PeerAddress;
use crate::types::{BlockBody, Point, Tip, WrappedHeader};

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

    /// A requested block fetch failed (peer responded with NoBlocks).
    /// Carries the full range from the underlying BlockFetch protocol.
    BlockFetchFailed { from: Point, to: Point },

    /// New peers discovered via PeerSharing.
    PeersDiscovered { peers: Vec<PeerAddress> },

    /// A transaction was received from an inbound peer (via TxSubmission server).
    TransactionReceived { peer_id: PeerId, body: Vec<u8> },

    /// Leios: an EB was announced via an RB header.
    LeiosBlockAnnounced { header: WrappedHeader },

    /// Leios: an endorser block is available for download from a peer.
    LeiosBlockOffered { point: Point },

    /// Leios: an EB's transactions are available for download from a peer.
    LeiosBlockTxsOffered { point: Point },

    /// Leios: votes are available for download.
    LeiosVotesOffered { votes: Vec<(u64, Vec<u8>)> },

    /// Leios: a fetched endorser block arrived.
    LeiosBlockReceived {
        point: Point,
        block: Vec<u8>,
    },

    /// Leios: fetched votes arrived.
    LeiosVotesReceived { votes: Vec<Vec<u8>> },

    /// Leios: fetched transactions for an EB arrived.
    LeiosBlockTxsReceived {
        point: Point,
        transactions: Vec<Vec<u8>>,
    },
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

    /// Fetch a specific Leios block. Coordinator picks the best peer.
    FetchLeiosBlock { point: Point },

    /// Fetch selective transactions from an EB. Coordinator picks the best peer.
    FetchLeiosBlockTxs {
        point: Point,
        bitmap: BTreeMap<u16, u64>,
    },

    /// Fetch specific votes. Coordinator picks the best peer(s).
    FetchLeiosVotes { votes: Vec<(u64, Vec<u8>)> },

    /// Inject a Leios block into the Leios store (for responder peers to serve).
    InjectLeiosBlock {
        point: Point,
        block: Vec<u8>,
    },

    /// Inject votes into the Leios store (for responder peers to serve).
    InjectLeiosVotes {
        votes: Vec<(u64, Vec<u8>)>,
        data: Vec<Vec<u8>>,
    },

    /// Shut down all peers and stop the coordinator.
    Shutdown,
}
