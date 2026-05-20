//! Shared data stores for cross-peer state.
//!
//! These stores are created by the coordinator (`multi_peer`) and shared
//! with per-peer server handlers (`peer`) via `Arc`. The coordinator
//! writes; server handlers read.

pub mod chain_store;
pub mod leios_store;
