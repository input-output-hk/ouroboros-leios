//! Producer-side body-path decision: inline-RB vs announce-via-EB.
//!
//! CIP-0164 Linear Leios's overflow rule: if the mempool exceeds the
//! per-RB byte cap, the next RB's body is empty and the txs are
//! announced via an EB; otherwise the txs go directly into the RB
//! body.  Both adapters that drive [`crate::praos::PraosState`] need
//! the same decision; this module owns it.
//!
//! Wire encoding stays with the consumer.  con-rs picks the path and
//! either drains txs (inline) or returns the manifest (EB).  The
//! consumer then computes the EB's hash from its wire bytes and
//! commits the drain-and-pin via [`crate::mempool::MempoolState::produce_eb`].

use crate::mempool::{MempoolState, PendingTx, TxId};

/// Where the txs for the next self-produced RB end up.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BodyPath {
    /// The mempool's free pool fits in the RB body cap; these txs are
    /// drained out for inclusion directly in the RB body.
    Inline(Vec<PendingTx>),
    /// The mempool overflowed the cap; every pending tx becomes an
    /// announced EB reference and the RB body is empty.  The wrapper
    /// encodes the manifest into wire bytes, hashes them, and finishes
    /// the move from free pool to `eb_pinned` via
    /// [`MempoolState::produce_eb`] with the resulting `EbKey`.
    Eb { manifest: Vec<TxId> },
}

impl BodyPath {
    /// CIP-0164 overflow rule.  Inspects the mempool's free-pool size
    /// against `rb_body_max_bytes`:
    ///
    /// - Below the cap: drains tx bodies into [`BodyPath::Inline`].
    ///   The mempool's free pool shrinks by the returned set.
    /// - At or above the cap: collects the FIFO-ordered manifest
    ///   into [`BodyPath::Eb`], capped at `eb_body_max_bytes`
    ///   worth of tx bodies.  The mempool is NOT mutated yet —
    ///   the wrapper must follow up with `produce_eb` once it has
    ///   computed the EB hash from the encoded manifest bytes.
    ///   At least one tx is always emitted if the free pool is
    ///   non-empty, even if the first tx alone exceeds the cap.
    pub fn decide(
        mempool: &mut MempoolState,
        rb_body_max_bytes: usize,
        eb_body_max_bytes: usize,
    ) -> Self {
        if mempool.total_bytes > rb_body_max_bytes {
            let mut manifest: Vec<TxId> = Vec::new();
            let mut bytes = 0usize;
            for tx in mempool.txs.iter() {
                let next = bytes + tx.size as usize;
                if next > eb_body_max_bytes && !manifest.is_empty() {
                    break;
                }
                manifest.push(tx.tx_id.clone());
                bytes = next;
                if bytes >= eb_body_max_bytes {
                    break;
                }
            }
            BodyPath::Eb { manifest }
        } else {
            BodyPath::Inline(mempool.drain_up_to(rb_body_max_bytes))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mempool::{EbKey, MempoolState};

    fn pending(id: u8, size: u32) -> PendingTx {
        PendingTx {
            tx_id: vec![id; 32],
            body: vec![0u8; size as usize],
            size,
        }
    }

    fn populate(state: &mut MempoolState, ids_and_sizes: &[(u8, u32)]) {
        for (id, size) in ids_and_sizes {
            let tx = pending(*id, *size);
            state.txs.push_back(tx);
            state.total_bytes += *size as usize;
        }
    }

    // EB cap big enough to never matter for these unit cases.
    const EB_CAP: usize = 1 << 30;

    #[test]
    fn inline_when_under_cap() {
        let mut state = MempoolState::new(100);
        populate(&mut state, &[(1, 100), (2, 100), (3, 100)]); // 300 bytes total
        let body = BodyPath::decide(&mut state, 500, EB_CAP);
        match body {
            BodyPath::Inline(txs) => {
                assert_eq!(txs.len(), 3);
                assert_eq!(state.total_bytes, 0);
                assert_eq!(state.txs.len(), 0);
            }
            other => panic!("expected Inline, got {other:?}"),
        }
    }

    #[test]
    fn eb_when_over_cap() {
        let mut state = MempoolState::new(100);
        populate(&mut state, &[(1, 200), (2, 200), (3, 200)]); // 600 bytes total
        let body = BodyPath::decide(&mut state, 500, EB_CAP);
        match body {
            BodyPath::Eb { manifest } => {
                assert_eq!(manifest.len(), 3);
                assert_eq!(manifest[0], vec![1u8; 32]);
                assert_eq!(manifest[1], vec![2u8; 32]);
                assert_eq!(manifest[2], vec![3u8; 32]);
                // Mempool unchanged — drain-and-pin is the wrapper's
                // follow-up commit via produce_eb.
                assert_eq!(state.txs.len(), 3);
                assert_eq!(state.total_bytes, 600);
            }
            other => panic!("expected Eb, got {other:?}"),
        }
    }

    #[test]
    fn at_cap_inlines() {
        let mut state = MempoolState::new(100);
        populate(&mut state, &[(1, 250), (2, 250)]); // 500 bytes, == cap
        let body = BodyPath::decide(&mut state, 500, EB_CAP);
        // total_bytes (500) is NOT > 500 → Inline.
        assert!(matches!(body, BodyPath::Inline(_)));
    }

    #[test]
    fn boundary_one_byte_over_cap_routes_eb() {
        let mut state = MempoolState::new(100);
        populate(&mut state, &[(1, 250), (2, 251)]); // 501, just over 500
        let body = BodyPath::decide(&mut state, 500, EB_CAP);
        assert!(matches!(body, BodyPath::Eb { .. }));
    }

    #[test]
    fn empty_mempool_yields_empty_inline() {
        let mut state = MempoolState::new(100);
        let body = BodyPath::decide(&mut state, 500, EB_CAP);
        match body {
            BodyPath::Inline(txs) => assert!(txs.is_empty()),
            other => panic!("expected Inline, got {other:?}"),
        }
    }

    #[test]
    fn eb_manifest_then_produce_eb_commits_drain() {
        let mut state = MempoolState::new(100);
        populate(&mut state, &[(1, 200), (2, 200), (3, 200)]);
        let body = BodyPath::decide(&mut state, 500, EB_CAP);
        let manifest = match body {
            BodyPath::Eb { manifest } => manifest,
            other => panic!("expected Eb, got {other:?}"),
        };
        // Simulate the wrapper committing.
        let eb_key = EbKey {
            slot: 7,
            hash: [0xAA; 32],
        };
        let (committed, _evictions) = state.produce_eb(eb_key, manifest.len());
        assert_eq!(committed, manifest);
        assert_eq!(state.txs.len(), 0);
        assert_eq!(state.total_bytes, 0);
    }

    #[test]
    fn eb_manifest_capped_by_eb_body_max_bytes() {
        // Mempool overflows the RB cap, but the EB cap is small enough
        // that only the FIFO prefix should be selected.
        let mut state = MempoolState::new(100);
        populate(&mut state, &[(1, 200), (2, 200), (3, 200), (4, 200), (5, 200)]); // 1000 bytes
        // RB cap 500, EB cap 500 → first 2 txs (400 bytes <= 500, third would push to 600)
        let body = BodyPath::decide(&mut state, 500, 500);
        let manifest = match body {
            BodyPath::Eb { manifest } => manifest,
            other => panic!("expected Eb, got {other:?}"),
        };
        assert_eq!(manifest.len(), 2);
        assert_eq!(manifest[0], vec![1u8; 32]);
        assert_eq!(manifest[1], vec![2u8; 32]);
        // Mempool still has all 5 txs until produce_eb is called.
        assert_eq!(state.txs.len(), 5);
        assert_eq!(state.total_bytes, 1000);

        let eb_key = EbKey {
            slot: 1,
            hash: [0xAB; 32],
        };
        let (committed, _) = state.produce_eb(eb_key, manifest.len());
        assert_eq!(committed.len(), 2);
        // Remaining three txs still pending.
        assert_eq!(state.txs.len(), 3);
        assert_eq!(state.total_bytes, 600);
    }

    #[test]
    fn eb_manifest_emits_one_when_first_tx_exceeds_cap() {
        let mut state = MempoolState::new(100);
        populate(&mut state, &[(1, 1000), (2, 200)]); // first alone > eb cap
        let body = BodyPath::decide(&mut state, 500, 500);
        let manifest = match body {
            BodyPath::Eb { manifest } => manifest,
            other => panic!("expected Eb, got {other:?}"),
        };
        assert_eq!(manifest.len(), 1);
        assert_eq!(manifest[0], vec![1u8; 32]);
    }
}
