//! Producer-side body-path decision: how the next self-produced RB
//! distributes mempool txs between its inline body and a fresh EB
//! announcement.
//!
//! CIP-0164 Linear Leios's overflow rule: fill the RB body first (it
//! has lower inclusion latency), and only announce an EB for txs that
//! cannot fit in the base RB.  [`BodyPath`] returns both pieces so the
//! caller can write the inline txs into the body **and** announce the
//! residual via an EB in the same RB.
//!
//! Producer-side safety rule (correctness, not optimization): when the
//! local node holds a chain-committed cert for an EB whose body it
//! has not validated locally, it does not know which mempool txs will
//! be claimed by that EB's closure.  Including any mempool tx in the
//! new RB body — or announcing a fresh EB that races the unvalidated
//! one — risks a duplicate at apply time, producing a provably-invalid
//! block.  The gate's state lives in [`crate::leios::LeiosState`]
//! (`endorsed_unvalidated_ebs`); `decide` reads it and returns the
//! empty body path with the mempool untouched.
//!
//! Wire encoding stays with the consumer.  This module picks the path,
//! drains the inline portion out of the mempool's free pool, and
//! returns the manifest for the residual.  The consumer encodes the
//! manifest into wire bytes, hashes them, and commits the
//! drain-and-pin via [`crate::mempool::MempoolState::produce_eb`].

use crate::leios::LeiosState;
use crate::mempool::{MempoolState, PendingTx, TxId};

/// Where the txs for the next self-produced RB end up.
///
/// `inline` becomes the RB body; `manifest` becomes a fresh EB
/// announcement attached to the same RB header.  The four legal
/// states encode all CIP-0164-compatible combinations directly:
///
/// | `inline` | `manifest` | meaning                                                                |
/// |----------|------------|------------------------------------------------------------------------|
/// | empty    | empty      | empty body, no EB (safety gate; or cert + small mempool)               |
/// | non-emp. | empty      | inline-only body, no EB (no cert, mempool ≤ RB cap)                    |
/// | empty    | non-emp.   | empty body, EB carries the overflow (cert + overflow)                  |
/// | non-emp. | non-emp.   | inline body + EB residual (no cert, mempool > RB cap)                  |
///
/// `inline` is already drained from the mempool's free pool.  The
/// `manifest` txs are still in the free pool; the caller commits the
/// EB-pin via [`MempoolState::produce_eb`] once it has computed the
/// EB hash from the encoded manifest bytes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BodyPath {
    /// FIFO-ordered prefix of the mempool drained into the RB body.
    /// Empty when the safety gate fires, when a cert is being
    /// attached (cert XOR inline body), or when the mempool is empty.
    pub inline: Vec<PendingTx>,
    /// FIFO-ordered tx ids the caller announces as a fresh EB.
    /// Empty when the mempool fit in the RB body cap (no overflow)
    /// or when the safety gate fired.  Not yet drained — the caller
    /// follows up with [`MempoolState::produce_eb`].
    pub manifest: Vec<TxId>,
}

impl BodyPath {
    /// CIP-0164 overflow rule, gated on (1) the producer-side EB-safety
    /// check and (2) the cert-XOR-inline-body rule.
    ///
    /// First consults [`LeiosState::has_endorsed_unvalidated_eb`]; if
    /// set, short-circuits to an empty [`BodyPath`] with the mempool
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
    /// - Mempool ≤ `rb_body_max_bytes`, no cert: drain tx bodies into
    ///   `inline`.  The mempool's free pool shrinks by the returned
    ///   set; `manifest` is empty.
    /// - Mempool ≤ `rb_body_max_bytes`, cert: leave the mempool
    ///   untouched and return all-empty.  The cert lands on its own;
    ///   the mempool waits for a future slot.
    /// - Mempool > `rb_body_max_bytes`, no cert: drain
    ///   `rb_body_max_bytes` worth of txs into `inline`, then collect
    ///   the FIFO-ordered residual into `manifest`, capped at
    ///   `eb_body_max_bytes` worth of tx bodies.  If the inline drain
    ///   absorbed the entire mempool (a single oversize tx exhausts
    ///   the free pool), `manifest` is empty and no EB is announced.
    /// - Mempool > `rb_body_max_bytes`, cert: leave `inline` empty
    ///   (CIP-0164 cert-XOR-inline-body) and collect the FIFO
    ///   manifest as above.  Cert + EB-announcement is explicitly
    ///   allowed by the CIP — the announcement is header-side, the
    ///   body stays empty.
    pub fn decide(
        mempool: &mut MempoolState,
        rb_body_max_bytes: usize,
        eb_body_max_bytes: usize,
        leios: &LeiosState,
        endorsement_present: bool,
    ) -> Self {
        if leios.has_endorsed_unvalidated_eb() {
            return BodyPath::default();
        }
        if mempool.total_bytes > rb_body_max_bytes {
            // Overflow: fill the RB body first (skipped under cert per
            // CIP-0164), then announce the residual via a fresh EB.
            let inline = if endorsement_present {
                Vec::new()
            } else {
                mempool.drain_up_to(rb_body_max_bytes)
            };
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
            return BodyPath { inline, manifest };
        }
        if endorsement_present {
            BodyPath::default()
        } else {
            BodyPath {
                inline: mempool.drain_up_to(rb_body_max_bytes),
                manifest: Vec::new(),
            }
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
    fn inline_only_when_under_cap() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 100), (2, 100), (3, 100)]); // 300 bytes total
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert_eq!(body.inline.len(), 3);
        assert!(body.manifest.is_empty());
        assert_eq!(state.total_bytes, 0);
        assert_eq!(state.txs.len(), 0);
    }

    #[test]
    fn overflow_fills_body_then_announces_residual() {
        // Mempool: [200, 200, 200, 200] = 800 bytes, RB cap = 500.
        // drain_up_to(500) takes [200, 200] (400 ≤ 500; adding the
        // next would push to 600 > 500 with non-empty result).
        // Residual = [200, 200] → manifest carries both.
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 200), (2, 200), (3, 200), (4, 200)]);
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert_eq!(body.inline.len(), 2);
        assert_eq!(body.inline[0].tx_id, vec![1u8; 32]);
        assert_eq!(body.inline[1].tx_id, vec![2u8; 32]);
        assert_eq!(body.manifest.len(), 2);
        assert_eq!(body.manifest[0], vec![3u8; 32]);
        assert_eq!(body.manifest[1], vec![4u8; 32]);
        // Inline txs drained; manifest txs still in the free pool
        // pending the wrapper's produce_eb commit.
        assert_eq!(state.txs.len(), 2);
        assert_eq!(state.total_bytes, 400);
    }

    #[test]
    fn at_cap_inlines() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 250), (2, 250)]); // 500 bytes, == cap
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        // total_bytes (500) is NOT > 500 → inline-only.
        assert_eq!(body.inline.len(), 2);
        assert!(body.manifest.is_empty());
    }

    #[test]
    fn one_byte_over_cap_routes_overflow() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 250), (2, 251)]); // 501, just over 500
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        // drain_up_to(500) takes [250] (next would be 501 > 500 with
        // non-empty result).  Residual = [251] → manifest.
        assert_eq!(body.inline.len(), 1);
        assert_eq!(body.inline[0].tx_id, vec![1u8; 32]);
        assert_eq!(body.manifest, vec![vec![2u8; 32]]);
    }

    #[test]
    fn empty_mempool_yields_all_empty() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert!(body.inline.is_empty());
        assert!(body.manifest.is_empty());
    }

    #[test]
    fn overflow_then_produce_eb_commits_drain() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 200), (2, 200), (3, 200), (4, 200)]); // 800
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        // Inline drained 2; manifest still pending.
        assert_eq!(state.txs.len(), 2);
        assert_eq!(state.total_bytes, 400);
        let eb_key = EbKey {
            slot: 7,
            hash: [0xAA; 32],
        };
        let (committed, _evictions) = state.produce_eb(eb_key, body.manifest.len());
        assert_eq!(committed, body.manifest);
        assert!(state.txs.is_empty());
        assert_eq!(state.total_bytes, 0);
    }

    #[test]
    fn manifest_capped_by_eb_body_max_bytes() {
        // Overflow + EB cap small enough that only a FIFO prefix of
        // the residual ends up in the manifest.
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 200), (2, 200), (3, 200), (4, 200), (5, 200), (6, 200), (7, 200)]);
        // 1400 bytes total, RB cap 500 → drain takes [1, 2] (400);
        // residual = [3..7]. EB cap 500 → manifest = first 2 of
        // residual = [3, 4] (400 ≤ 500; next would push to 600).
        let body = BodyPath::decide(&mut state, 500, 500, &leios, false);
        assert_eq!(body.inline.len(), 2);
        assert_eq!(body.manifest.len(), 2);
        assert_eq!(body.manifest[0], vec![3u8; 32]);
        assert_eq!(body.manifest[1], vec![4u8; 32]);
        // Residual txs 3..7 still in mempool; produce_eb drains the
        // manifest prefix.
        assert_eq!(state.txs.len(), 5);
        assert_eq!(state.total_bytes, 1000);
        let eb_key = EbKey {
            slot: 1,
            hash: [0xAB; 32],
        };
        let (committed, _) = state.produce_eb(eb_key, body.manifest.len());
        assert_eq!(committed.len(), 2);
        assert_eq!(state.txs.len(), 3);
        assert_eq!(state.total_bytes, 600);
    }

    #[test]
    fn manifest_emits_one_when_first_residual_tx_exceeds_cap() {
        // [200, 1000, 200]: drain takes [200], residual = [1000, 200].
        // EB cap 500 → first residual tx is 1000 > 500, but emit it
        // anyway (the "at least one" rule on a non-empty residual);
        // the next is then skipped.
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 200), (2, 1000), (3, 200)]);
        let body = BodyPath::decide(&mut state, 500, 500, &leios, false);
        assert_eq!(body.inline.len(), 1);
        assert_eq!(body.manifest.len(), 1);
        assert_eq!(body.manifest[0], vec![2u8; 32]);
    }

    #[test]
    fn single_oversize_tx_inlines_with_no_eb() {
        // Mempool = [800], RB cap = 500.  total > cap triggers the
        // overflow branch.  drain_up_to(500) takes the lone tx (the
        // "at least one" escape clause), mempool empties.  Residual
        // is empty → manifest empty → no EB announcement.  An empty
        // EB is forbidden by CIP-0164, and the struct shape naturally
        // expresses "inline only" via the empty manifest.
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 800)]);
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert_eq!(body.inline.len(), 1);
        assert!(body.manifest.is_empty());
        assert!(state.txs.is_empty());
    }

    #[test]
    fn safety_gate_returns_all_empty_with_mempool_untouched() {
        let mut state = MempoolState::new(100);
        let mut leios = empty_leios();
        leios.endorsed_unvalidated_ebs.insert([0xCC; 32], 7);
        populate(&mut state, &[(1, 400), (2, 400)]); // 800 bytes, overflows 500
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert!(body.inline.is_empty());
        assert!(body.manifest.is_empty());
        assert_eq!(state.txs.len(), 2);
        assert_eq!(state.total_bytes, 800);
    }

    #[test]
    fn safety_gate_clears_on_validated_eb() {
        let mut state = MempoolState::new(100);
        let mut leios = empty_leios();
        leios.endorsed_unvalidated_ebs.insert([0xDD; 32], 7);
        leios.on_validated_eb(crate::types::Point::Specific {
            slot: 7,
            hash: [0xDD; 32],
        });
        populate(&mut state, &[(1, 100)]);
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert_eq!(body.inline.len(), 1);
        assert!(body.manifest.is_empty());
    }

    #[test]
    fn cert_with_small_mempool_returns_all_empty() {
        // CIP-0164: cert XOR inline-body.  Mempool below the overflow
        // threshold → mempool too small to motivate an EB → the only
        // legal body is empty; mempool waits for a later RB.
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 100), (2, 100), (3, 100)]); // 300 bytes < 500
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, true);
        assert!(body.inline.is_empty());
        assert!(body.manifest.is_empty());
        assert_eq!(state.txs.len(), 3);
        assert_eq!(state.total_bytes, 300);
    }

    #[test]
    fn cert_with_overflowing_mempool_announces_eb_with_empty_body() {
        // Cert + overflow: inline stays empty (cert XOR inline), the
        // full mempool overflow lands in the manifest.  Cert ships in
        // the header alongside the fresh EB announcement — legal
        // under CIP-0164 (announcement is header-side).
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 400), (2, 400)]); // 800 bytes > 500
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, true);
        assert!(body.inline.is_empty());
        assert_eq!(body.manifest.len(), 2);
        // Cert + inline-body is forbidden, but the mempool is left
        // intact (manifest commit happens via produce_eb).
        assert_eq!(state.txs.len(), 2);
        assert_eq!(state.total_bytes, 800);
    }

    #[test]
    fn no_cert_with_small_mempool_inlines() {
        let mut state = MempoolState::new(100);
        let leios = empty_leios();
        populate(&mut state, &[(1, 100)]);
        let body = BodyPath::decide(&mut state, 500, EB_CAP, &leios, false);
        assert_eq!(body.inline.len(), 1);
        assert!(body.manifest.is_empty());
        assert!(state.txs.is_empty());
    }
}
