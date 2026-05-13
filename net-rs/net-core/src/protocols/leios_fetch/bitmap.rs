//! Sparse `BTreeMap<u16, u64>` bitmap used by `MsgLeiosBlockTxsRequest`.
//!
//! The canonical implementation lives in [`con_rs::bitmap`] — the
//! same `BTreeMap<u16, u64>` representation is already the in-memory
//! type used by con-rs's fetch traits, so the bitmap helpers belong
//! beside them.  This module re-exports the four helpers under their
//! historical path so existing wire-codec callers (and tests) stay
//! unchanged.

pub use con_rs::bitmap::{contains, from_indices, iter_indices, select_all};
