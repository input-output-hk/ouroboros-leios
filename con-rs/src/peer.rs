//! Peer identity used by the consensus layer.

use std::fmt;

/// Unique identifier for a connected peer within a coordinator session.
///
/// Monotonically increasing — not a network address. Two connections to
/// the same address get different PeerIds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PeerId(pub u64);

impl fmt::Display for PeerId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "peer-{}", self.0)
    }
}
