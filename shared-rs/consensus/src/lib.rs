//! Cardano consensus primitives, sans-IO.
//!
//! Hosts the protocol pieces that every Cardano-Leios implementation
//! must agree on — committee selection (CIP-0164 wFA + LS), pipeline
//! phase math, vote aggregation, longest-chain selection.  No tokio,
//! no clock, no networking; consumers wrap the state machines and
//! drive them with their own I/O layer.

pub mod aggregation;
pub mod behaviour;
pub mod bitmap;
pub mod chain_tree;
pub mod config;
pub mod elections;
pub mod fetch;
pub mod leios;
pub mod lottery;
pub mod mempool;
pub mod peer;
pub mod peer_chain;
pub mod pipeline;
pub mod praos;
pub mod production;
pub mod types;
pub mod committee;

pub use config::{CommitteeSelection, StakeEntry};
pub use peer::PeerId;
pub use types::{Point, Tip, Vote};
