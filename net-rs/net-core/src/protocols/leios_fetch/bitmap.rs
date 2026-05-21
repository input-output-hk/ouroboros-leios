//! Sparse `BTreeMap<u16, u64>` bitmap used by `MsgLeiosBlockTxsRequest`.
//!
//! The canonical implementation lives in [`shared_consensus::bitmap`] — the
//! same `BTreeMap<u16, u64>` representation is already the in-memory
//! type used by shared-consensus's fetch traits, so the bitmap helpers belong
//! beside them.  This module re-exports the four helpers under their
//! historical path so existing wire-codec callers (and tests) stay
//! unchanged.

pub use shared_consensus::bitmap::{contains, from_indices, iter_indices, select_all};
