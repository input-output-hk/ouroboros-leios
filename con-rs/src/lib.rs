//! Cardano consensus primitives shared between the test node (`net-node`)
//! and the simulator (`sim-rs`).
//!
//! This crate is sans-IO: no tokio, no clock, no networking. It hosts the
//! pure protocol pieces that both implementations should agree on —
//! committee selection (CIP-0164 wFA + LS), pipeline phase math, and vote
//! aggregation / quorum detection.

pub mod aggregation;
pub mod config;
pub mod elections;
pub mod pipeline;
pub mod wfa;

pub use config::{CommitteeSelection, StakeEntry};
