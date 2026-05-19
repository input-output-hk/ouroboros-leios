//! Producer-side body-path decision: inline-RB vs announce-via-EB vs
//! empty-for-safety.
//!
//! CIP-0164 Linear Leios's overflow rule: if the mempool exceeds the
//! per-RB byte cap, the next RB's body is empty and the txs are
//! announced via an EB; otherwise the txs go directly into the RB
//! body.  Both adapters that drive [`crate::praos::PraosState`] need
//! the same decision; this module owns it.
//!
//! Producer-side safety rule (correctness, not optimization): when the
//! local node holds a chain-committed cert for an EB whose body it
//! has not validated locally, it does not know which mempool txs will
//! be claimed by that EB's closure.  Including any mempool tx in the
//! new RB body — or announcing a fresh EB that races the unvalidated
//! one — risks a duplicate at apply time, producing a provably-invalid
//! block.  The gate's state lives in [`crate::leios::LeiosState`]
//! (`endorsed_unvalidated_ebs`); `decide` reads it and returns
//! [`BodyPath::Empty`] when set, leaving the mempool untouched.
//!
//! Wire encoding stays with the consumer.  This crate picks the path and
//! either drains txs (inline) or returns the manifest (EB).  The
//! consumer then computes the EB's hash from its wire bytes and
//! commits the drain-and-pin via [`crate::mempool::MempoolState::produce_eb`].

use crate::leios::LeiosState;
use crate::mempool::{MempoolState, PendingTx, TxId};

/// Where the txs for the next self-produced RB end up.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BodyPath {
    /// The local node holds a chain-committed cert for an EB whose
    /// body it has not validated locally.  The RB body must be empty
    /// and no fresh EB may be announced; the cert itself is still
    /// emitted by the caller.  The mempool is not mutated.
    Empty,
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
    /// CIP-0164 overflow rule, gated on (1) the producer-side EB-safety
    /// check and (2) the cert-XOR-inline-body rule.
    ///
    /// First consults [`LeiosState::has_endorsed_unvalidated_eb`]; if
    /// set, short-circuits to [`BodyPath::Empty`] with the mempool
    /// untouched.
    ///
    /// `endorsement_present` is true iff the caller is about to attach
    /// a Leios certificate to this RB.  CIP-0164 forbids both a cert
    /// and inline txs in the same RB body (a validator carrying a cert
    /// must build ledger state from the endorsed EB's closure before
    /// it could validate fresh txs, and the slot budget cannot fit
    /// both).  Announcing a new EB in the header is independent of
    /// the cert, so the EB-overflow path remains available.
    ///
    /// Cases (after the EB-safety check):
    ///
    /// - `endorsement_present = false`, mempool ≤ `rb_body_max_bytes`:
    ///   drain tx bodies into [`BodyPath::Inline`].  The mempool's
    ///   free pool shrinks by the returned set.
    /// - `endorsement_present = false`, mempool > `rb_body_max_bytes`:
    ///   collect the FIFO-ordered manifest into [`BodyPath::Eb`],
    ///   capped at `eb_body_max_bytes` worth of tx bodies.  The
    ///   mempool is NOT mutated yet — the wrapper must follow up
    ///   with `produce_eb` once it has computed the EB hash from the
    ///   encoded manifest bytes.  At least one tx is always emitted
    ///   if the free pool is non-empty, even if the first tx alone
    ///   exceeds the cap.
    /// - `endorsement_present = true`, mempool ≤ `rb_body_max_bytes`:
    ///   [`BodyPath::Empty`].  The cert lands on its own; inline txs
    ///   are forbidden, and the mempool is too small to motivate an
    ///   EB.  Mempool untouched; the txs will be drained on a later
    ///   RB.
    /// - `endorsement_present = true`, mempool > `rb_body_max_bytes`:
    ///   [`BodyPath::Eb`].  The cert ships with a fresh EB
    ///   announcement; both are allowed simultaneously since the
    ///   announcement lives in the header and the body stays empty.
    pub fn decide(
        mempool: &mut MempoolState,
        rb_body_max_bytes: usize,
        eb_body_max_bytes: usize,
        leios: &LeiosState,
        endorsement_present: bool,
    ) -> Self {
        if leios.has_endorsed_unvalidated_eb() {
            return BodyPath::Empty;
        }
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
        } else if endorsement_present {
            // Cert + inline-txs would be a CIP-0164 violation; the
            // mempool is too small to motivate an EB-overflow, so the
            // RB carries the cert alone and the mempool waits for a
            // future slot.
            BodyPath::Empty
        } else {
            BodyPath::Inline(mempool.drain_up_to(rb_body_max_bytes))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::CommitteeSelection;
    use crate::elections::{Elections, ElectionsConfig};
    use crate::leios::VotingConfig;
    use crate::mempool::{EbKey, MempoolState};
    use crate::pipeline::PipelineConfig;
    use std::collections::BTreeMap;

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

    /// Minimal `LeiosState` for body-path tests.  The gate field
    /// (`endorsed_unvalidated_ebs`) is pub so tests can flip the gate
    /// state directly without driving the full chain-endorsement
    /// lifecycle.
    fn empty_leios() -> crate::leios::LeiosState {
        let pipeline = PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        };
        let elections = Elections::new(ElectionsConfig {
            node_id: "test".to_string(),
            pipeline,
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 1000,
            expected_committee_size: 100,
            quorum_weight_fraction: 0.75,
        });
        let voting = VotingConfig {
            committee_selection: CommitteeSelection::EveryoneVotes,
            stake: 100,
            total_stake: 1000,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
            persistent_seats: 1,
            retry_vote_in_window: true,
        };
        crate::leios::LeiosState::new("test".into(), elections, voting, pipeline)
    }

    // EB cap big enough to never matter for these unit cases.
    const EB_CAP: usize = 1 << 30;

    #[test]
    fn inline_when_under_cap() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 100), (2, 100), (3, 100)]); // 300 bytes total
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
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
        let leios = empty_leios();
        populate(&mut state, &[(1, 200), (2, 200), (3, 200)]); // 600 bytes total
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
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
        let leios = empty_leios();
        populate(&mut state, &[(1, 250), (2, 250)]); // 500 bytes, == cap
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        // total_bytes (500) is NOT > 500 → Inline.
        assert!(matches!(body, BodyPath::Inline(_)));
    }

    #[test]
    fn boundary_one_byte_over_cap_routes_eb() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 250), (2, 251)]); // 501, just over 500
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert!(matches!(body, BodyPath::Eb { .. }));
    }

    #[test]
    fn empty_mempool_yields_empty_inline() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        match body {
            BodyPath::Inline(txs) => assert!(txs.is_empty()),
            other => panic!("expected Inline, got {other:?}"),
        }
    }

    #[test]
    fn eb_manifest_then_produce_eb_commits_drain() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 200), (2, 200), (3, 200)]);
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
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
        let leios = empty_leios();
        populate(&mut state, &[(1, 200), (2, 200), (3, 200), (4, 200), (5, 200)]); // 1000 bytes
        // RB cap 500, EB cap 500 → first 2 txs (400 bytes <= 500, third would push to 600)
        let body = BodyPath::decide(&mut state, 500, 500, &leios, false);
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
        let leios = empty_leios();
        populate(&mut state, &[(1, 1000), (2, 200)]); // first alone > eb cap
        let body = BodyPath::decide(&mut state, 500, 500, &leios, false);
        let manifest = match body {
            BodyPath::Eb { manifest } => manifest,
            other => panic!("expected Eb, got {other:?}"),
        };
        assert_eq!(manifest.len(), 1);
        assert_eq!(manifest[0], vec![1u8; 32]);
    }

    #[test]
    fn safety_gate_returns_empty_with_mempool_untouched() {
        // Gate set: a chain-committed cert references an EB the local
        // node has not validated.  Body must be Empty, mempool intact —
        // including the overflow case which would normally route to Eb.
        let mut state = MempoolState::new(100);
        let mut leios = empty_leios();
        leios.endorsed_unvalidated_ebs.insert([0xCC; 32], 7);
        populate(&mut state, &[(1, 400), (2, 400)]); // 800 bytes, overflows 500
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert!(matches!(body, BodyPath::Empty));
        assert_eq!(state.txs.len(), 2);
        assert_eq!(state.total_bytes, 800);
    }

    #[test]
    fn safety_gate_clears_on_validated_eb() {
        // After the body validates, the gate releases and the regular
        // overflow rule resumes.
        let mut state = MempoolState::new(100);
        let mut leios = empty_leios();
        leios.endorsed_unvalidated_ebs.insert([0xDD; 32], 7);
        leios.on_validated_eb(crate::types::Point::Specific {
            slot: 7,
            hash: [0xDD; 32],
        });
        populate(&mut state, &[(1, 100)]);
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert!(matches!(body, BodyPath::Inline(_)));
    }

    #[test]
    fn endorsement_with_small_mempool_returns_empty_not_inline() {
        // CIP-0164: a cert and inline txs in the same RB body are
        // mutually exclusive.  With a cert about to attach and the
        // mempool below the overflow threshold, the only legal body
        // is empty.
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 100), (2, 100), (3, 100)]); // 300 bytes < 500
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, true);
        assert!(matches!(body, BodyPath::Empty));
        // Mempool must be untouched — the txs wait for a later RB.
        assert_eq!(state.txs.len(), 3);
        assert_eq!(state.total_bytes, 300);
    }

    #[test]
    fn endorsement_with_overflowing_mempool_routes_eb() {
        // A cert in the header coexists with a fresh EB announcement
        // (the announcement is header-side, body stays empty).  This
        // path is legal under CIP-0164.
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 400), (2, 400)]); // 800 bytes > 500
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, true);
        match body {
            BodyPath::Eb { manifest } => {
                assert_eq!(manifest.len(), 2);
            }
            other => panic!("expected Eb, got {other:?}"),
        }
    }

    #[test]
    fn no_endorsement_with_small_mempool_inlines() {
        // Sanity: with no cert this slot, the small-mempool path
        // still drains into Inline (Praos fallback).
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 100)]);
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert!(matches!(body, BodyPath::Inline(_)));
        assert_eq!(state.txs.len(), 0);
    }
}
