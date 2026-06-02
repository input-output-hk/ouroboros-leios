//! Event and command types for the coordinator ↔ application boundary.

use std::collections::BTreeMap;

use std::time::Duration;

use crate::peer::{ConnectionMode, PeerId};
use crate::protocols::peersharing::PeerAddress;
use crate::protocols::txsubmission::PendingTx;
use crate::types::{BlockBody, Point, Tip, Vote, WrappedHeader};

// ---------------------------------------------------------------------------
// Coordinator ↔ Application
// ---------------------------------------------------------------------------

/// Events sent from the coordinator to the application.
///
/// Most events carry `peer_id` so chain-selecting consumers (net-node
/// consensus) can track per-peer candidate chains. Consumers that don't
/// care about peer identity (net-cli `multi-follow`) can destructure it
/// with `peer_id: _`.
#[derive(Debug)]
pub enum NetworkEvent {
    /// A peer connected successfully.
    PeerConnected { peer_id: PeerId, address: String },

    /// A peer disconnected (error or graceful).
    PeerDisconnected { peer_id: PeerId, reason: String },

    /// A peer announced a new chain tip. Emitted per-peer, not deduplicated
    /// across peers — consensus needs to track each peer's candidate chain
    /// independently.
    TipAdvanced {
        peer_id: PeerId,
        tip: Tip,
        header: WrappedHeader,
    },

    /// ChainSync found an intersection with a peer — the common ancestor
    /// between the local chain and the peer's chain. Consensus stores this
    /// as the peer chain's anchor (guaranteed common ancestor).
    IntersectionFound { peer_id: PeerId, point: Point },

    /// A peer rolled its chain back to a point. Emitted for every peer
    /// rollback, not just those affecting the local best tip.
    RolledBack {
        peer_id: PeerId,
        point: Point,
        tip: Tip,
    },

    /// A requested block was fetched.
    BlockReceived { point: Point, body: BlockBody },

    /// A requested block fetch failed (peer responded with NoBlocks,
    /// the connection died, or no peer had the fragment).  Carries the
    /// responsible peer when one was actually attempted, so the
    /// application can put it on cooldown and re-route via the fetch
    /// policy.  `None` means no peer was reachable for the requested
    /// fragment — there's no one to cooldown.
    BlockFetchFailed {
        peer_id: Option<PeerId>,
        from: Point,
        to: Point,
    },

    /// New peers discovered via PeerSharing.
    PeersDiscovered { peers: Vec<PeerAddress> },

    /// A transaction was received from an inbound peer (via TxSubmission server).
    TransactionReceived { peer_id: PeerId, body: Vec<u8> },

    /// TxSubmission client: a peer requested `count` tx ids (blocking mode).
    TxsRequested { peer_id: PeerId, count: u16 },

    /// Leios: an EB was announced via an RB header.
    LeiosBlockAnnounced { header: WrappedHeader },

    /// Leios: an endorser block is available for download from a peer.
    LeiosBlockOffered { peer_id: PeerId, point: Point },

    /// Leios: an EB's transactions are available for download from a peer.
    LeiosBlockTxsOffered { peer_id: PeerId, point: Point },

    /// Leios: a fetched endorser block arrived.
    LeiosBlockReceived { point: Point, block: Vec<u8> },

    /// Leios: votes delivered inline by a peer (no fetch round-trip).
    LeiosVotesReceived {
        peer_id: PeerId,
        votes: Vec<Vote>,
    },

    /// Leios: fetched transactions for an EB arrived.
    LeiosBlockTxsReceived {
        point: Point,
        transactions: Vec<Vec<u8>>,
    },

    /// Response to `QueryPeers`: snapshot of all connected peers.
    PeerSnapshot { peers: Vec<PeerInfo> },
}

/// Snapshot of a single peer's state, for telemetry reporting.
#[derive(Debug, Clone)]
pub struct PeerInfo {
    pub peer_id: PeerId,
    pub address: String,
    pub mode: ConnectionMode,
    pub rtt: Option<Duration>,
    pub tip_block_no: Option<u64>,
    pub inbound_delay: Duration,
    pub bytes_sent: u64,
    pub bytes_received: u64,
}

/// Commands sent from the application to the coordinator.
#[derive(Debug)]
pub enum NetworkCommand {
    /// Add a peer by address. The coordinator will connect and manage it.
    AddPeer { address: String },

    /// Fetch a specific block. The coordinator picks the best peer.
    FetchBlock { point: Point },

    /// Fetch a range of blocks (from..=to inclusive). When `peer_id` is
    /// set, the coordinator routes directly to that peer (the one that
    /// announced the chain). Otherwise falls back to fragment-based
    /// peer selection.
    FetchBlockRange {
        from: Point,
        to: Point,
        peer_id: Option<PeerId>,
    },

    /// Request peers from connected nodes (triggers PeerSharing).
    DiscoverPeers,

    /// Ask a specific peer to re-run ChainSync intersection with fresh
    /// candidates from the current local chain. Used when a previous
    /// intersection became stale due to a local fork switch.
    ReIntersect { peer_id: PeerId },

    /// Inject a block into the chain store (for responder peers to serve).
    /// Used by block generators or other local producers.
    InjectBlock {
        point: Point,
        header: Box<WrappedHeader>,
        body: BlockBody,
        block_no: u64,
    },

    /// Roll back the chain store to a point (for responder peers).
    InjectRollback { point: Point },

    /// Fetch a Leios block from a specific peer (chosen by shared-consensus's
    /// EbFetchPolicy).  The coordinator routes directly to that peer.
    FetchLeiosBlock { peer_id: PeerId, point: Point },

    /// Fetch selective transactions from an EB on a specific peer
    /// (chosen by shared-consensus's EbTxsFetchPolicy).
    FetchLeiosBlockTxs {
        peer_id: PeerId,
        point: Point,
        bitmap: BTreeMap<u16, u64>,
    },

    /// Inject a Leios block into the Leios store (for responder peers to serve).
    InjectLeiosBlock { point: Point, block: Vec<u8> },

    /// Inject the transactions of a Leios block into the Leios store
    /// (for responder peers to serve via `MsgLeiosBlockTxsRequest`).
    InjectLeiosBlockTxs {
        point: Point,
        transactions: Vec<Vec<u8>>,
    },

    /// Record the ordered tx-hash list of an EB whose body the receiver
    /// has already fetched and decoded. Lets the responder side serve
    /// `MsgLeiosBlockTxsRequest` by resolving each requested hash via the
    /// configured `TxBodyResolver` (typically the local mempool).
    RecordLeiosEbManifest {
        point: Point,
        tx_hashes: Vec<[u8; 32]>,
    },

    /// Inject votes into the Leios store (for responder peers to re-serve
    /// inline via `MsgLeiosVotes`).
    InjectLeiosVotes { votes: Vec<Vote> },

    /// Provide transactions to a specific peer via TxSubmission.
    ProvideTxs {
        peer_id: PeerId,
        txs: Vec<PendingTx>,
    },

    /// Request a snapshot of all connected peers (for telemetry).
    QueryPeers,

    /// Shut down all peers and stop the coordinator.
    Shutdown,
}
