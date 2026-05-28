//! `RbHeaderEquivocator` — a Praos-layer adversary that violates the
//! CIP-0164 RB-header equivocation rule by producing two or more
//! Ranking Blocks for the same `(slot, issuer)` and routing different
//! variants to disjoint peer subsets.
//!
//! Mechanics:
//!
//! - At every slot the local node wins the RB lottery, the I/O
//!   wrapper produces `ways` distinct RB variants (same
//!   `(slot, issuer, prev_hash, block_number)`, differing
//!   `body_hash`).  All variants are handed to the behaviour via
//!   [`Behaviour::record_rb_variants`].
//! - The behaviour partitions the peer set deterministically into
//!   `ways` buckets and substitutes a different variant for each
//!   bucket via [`Behaviour::transform_outbound`].
//! - When an honest peer ends up seeing two distinct header hashes at
//!   the same `(slot, issuer)` — directly from this node across two
//!   connections, or by joining variants gossiped through the
//!   topology — Praos `note_header_for_equivocation` flags the slot.
//!
//! Determinism: peer assignment is `blake2b(seed || peer_id) mod
//! ways`.  Across re-runs with the same node seed, every peer lands
//! in the same bucket.

use std::collections::BTreeMap;

use crate::behaviour::{
    Behaviour, Outbound, OutboundDecision, OwnedOutbound, RbProductionStrategy, RbVariantInput,
};
use crate::leios::LeiosState;
use crate::peer::PeerId;
use crate::praos::PraosState;

pub struct RbHeaderEquivocator {
    /// Number of distinct variants emitted per equivocation slot.
    /// `ways >= 2`; a value of `1` would degenerate to honest behaviour
    /// (no equivocation), so the constructor clamps to a minimum of 2.
    pub ways: u8,
    /// Deterministic seed for peer-to-bucket assignment.  Mixed with
    /// each peer id via Blake2b so adjacent peer ids don't land in
    /// adjacent buckets.
    pub seed: u64,
    /// Variants stashed per equivocation slot, populated by
    /// [`Behaviour::record_rb_variants`].  Indexed by slot so a slow
    /// peer can still be served a stale variant.  Eviction is naive
    /// (none) for now — the cap landing in a follow-up.
    pub variants: BTreeMap<u64, Vec<RbVariantInput>>,
}

impl RbHeaderEquivocator {
    pub fn new(ways: u8, seed: u64) -> Self {
        let ways = ways.max(2);
        Self {
            ways,
            seed,
            variants: BTreeMap::new(),
        }
    }

    /// Deterministic peer-to-bucket assignment.  `blake2b_8(seed ||
    /// peer)` % `ways`.  Returns `0..ways`.
    fn bucket_for(&self, peer: PeerId) -> usize {
        let mut h = blake2b_simd::Params::new().hash_length(8).to_state();
        h.update(&self.seed.to_le_bytes());
        h.update(&peer.0.to_le_bytes());
        let mut buf = [0u8; 8];
        buf.copy_from_slice(&h.finalize().as_bytes()[..8]);
        (u64::from_le_bytes(buf) % self.ways as u64) as usize
    }
}

impl Behaviour for RbHeaderEquivocator {
    fn name(&self) -> &'static str {
        "rb-header-equivocator"
    }

    fn rb_production_strategy(
        &mut self,
        _leios: &LeiosState,
        _praos: &PraosState,
        _slot: u64,
    ) -> RbProductionStrategy {
        RbProductionStrategy::Equivocate { ways: self.ways }
    }

    fn record_rb_variants(&mut self, slot: u64, variants: &[RbVariantInput]) {
        self.variants.insert(slot, variants.to_vec());
    }

    fn find_variant_body(&self, slot: u64, hash: &[u8; 32]) -> Option<Vec<u8>> {
        self.variants
            .get(&slot)?
            .iter()
            .find(|v| &v.hash == hash)
            .map(|v| v.body.clone())
    }

    fn transform_outbound(
        &mut self,
        peer: PeerId,
        out: Outbound<'_>,
    ) -> OutboundDecision {
        let Outbound::RbHeader { slot, header } = out;
        let Some(set) = self.variants.get(&slot) else {
            // Either this isn't a slot we equivocated on, or the cache
            // entry has been evicted.  Pass through honestly.
            return OutboundDecision::Send;
        };
        let bucket = self.bucket_for(peer);
        let variant = match set.get(bucket) {
            Some(v) => v,
            None => return OutboundDecision::Send,
        };
        if variant.header == header {
            // This peer's bucket already corresponds to the variant
            // about to go out (i.e. the primary).  Nothing to do.
            return OutboundDecision::Send;
        }
        OutboundDecision::Replace(OwnedOutbound::RbHeader {
            slot,
            header: variant.header.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dummy_states() -> (LeiosState, PraosState) {
        use crate::config::CommitteeSelection;
        use crate::elections::{Elections, ElectionsConfig};
        use crate::leios::VotingConfig;
        use crate::pipeline::PipelineConfig;

        let pipeline = PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        };
        let elections = Elections::new(ElectionsConfig {
            node_id: "t".to_string(),
            pipeline,
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 100,
            expected_total_weight: 1,
            quorum_weight_fraction: 0.75,
        });
        let voting = VotingConfig {
            committee_selection: CommitteeSelection::EveryoneVotes,
            stake: 1,
            total_stake: 100,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
            persistent_seats: 0,
            retry_vote_in_window: true,
        };
        let leios = LeiosState::new("t".to_string(), elections, voting, pipeline);
        let praos = PraosState::new("t".to_string(), 2160);
        (leios, praos)
    }

    #[test]
    fn strategy_is_equivocate_with_configured_ways() {
        let (l, p) = dummy_states();
        let mut b = RbHeaderEquivocator::new(3, 0);
        assert_eq!(
            b.rb_production_strategy(&l, &p, 42),
            RbProductionStrategy::Equivocate { ways: 3 }
        );
    }

    #[test]
    fn name_is_kebab_case() {
        let b = RbHeaderEquivocator::new(2, 0);
        assert_eq!(b.name(), "rb-header-equivocator");
    }

    #[test]
    fn ways_clamps_to_minimum_of_two() {
        let b = RbHeaderEquivocator::new(0, 0);
        assert_eq!(b.ways, 2);
        let b = RbHeaderEquivocator::new(1, 0);
        assert_eq!(b.ways, 2);
    }

    #[test]
    fn buckets_partition_peers_deterministically_and_evenly() {
        // Across many peers the distribution should be approximately
        // uniform.  With ways=2 and 1000 peers, both buckets should
        // see > 400 hits.
        let b = RbHeaderEquivocator::new(2, 0xC0FFEE);
        let mut counts = [0usize; 2];
        for i in 0..1000u64 {
            counts[b.bucket_for(PeerId(i))] += 1;
        }
        assert!(counts[0] > 400 && counts[1] > 400, "buckets: {counts:?}");
        // Determinism: same peer always lands in the same bucket.
        let probe = PeerId(123);
        assert_eq!(b.bucket_for(probe), b.bucket_for(probe));
    }

    #[test]
    fn record_then_replace_for_non_primary_bucket() {
        let mut b = RbHeaderEquivocator::new(2, 0);
        let primary_header = vec![1u8, 2, 3];
        let variant_header = vec![9u8, 8, 7];
        let primary_hash = [1u8; 32];
        let variant_hash = [2u8; 32];
        b.record_rb_variants(
            42,
            &[
                RbVariantInput {
                    hash: primary_hash,
                    header: primary_header.clone(),
                    body: vec![],
                },
                RbVariantInput {
                    hash: variant_hash,
                    header: variant_header.clone(),
                    body: vec![10, 20, 30],
                },
            ],
        );
        // Find a peer assigned to bucket 1 (i.e. the variant, not the primary).
        let mut peer_bucket1 = None;
        for i in 0..100u64 {
            if b.bucket_for(PeerId(i)) == 1 {
                peer_bucket1 = Some(PeerId(i));
                break;
            }
        }
        let peer = peer_bucket1.expect("at least one peer in bucket 1");
        let out = b.transform_outbound(
            peer,
            Outbound::RbHeader {
                slot: 42,
                header: &primary_header,
            },
        );
        match out {
            OutboundDecision::Replace(OwnedOutbound::RbHeader {
                slot,
                header,
            }) => {
                assert_eq!(slot, 42);
                assert_eq!(header, variant_header);
            }
            other => panic!("expected Replace, got {other:?}"),
        }
    }

    #[test]
    fn pass_through_for_slot_without_recorded_variants() {
        let mut b = RbHeaderEquivocator::new(2, 0);
        let out = b.transform_outbound(
            PeerId(0),
            Outbound::RbHeader {
                slot: 7,
                header: &[1, 2, 3],
            },
        );
        assert!(matches!(out, OutboundDecision::Send));
    }

    #[test]
    fn find_variant_body_returns_stored_body() {
        let mut b = RbHeaderEquivocator::new(2, 0);
        let h0 = [1u8; 32];
        let h1 = [2u8; 32];
        b.record_rb_variants(
            42,
            &[
                RbVariantInput {
                    hash: h0,
                    header: vec![1],
                    body: vec![10, 20],
                },
                RbVariantInput {
                    hash: h1,
                    header: vec![2],
                    body: vec![30, 40, 50],
                },
            ],
        );
        assert_eq!(b.find_variant_body(42, &h0), Some(vec![10, 20]));
        assert_eq!(b.find_variant_body(42, &h1), Some(vec![30, 40, 50]));
        assert_eq!(b.find_variant_body(42, &[9u8; 32]), None);
        assert_eq!(b.find_variant_body(43, &h0), None);
    }
}
