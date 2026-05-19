//! Vote aggregation, quorum detection, and certificate formation.
//!
//! Tracks votes per EB election, detects when quorum is reached.
//! Certificate formation and RB header population are in Commit 5.

use std::collections::BTreeMap;

use tracing::info;

use super::pipeline::{EbElection, PipelineConfig};

/// Returned from `record_vote` when a vote causes quorum to fire for the
/// first time. The caller uses this to emit `LeiosQuorumReached` telemetry.
pub struct QuorumFormed {
    pub eb_slot: u64,
    pub voted_weight: u64,
    pub voters: usize,
}

/// Record a vote for an EB. Deduplicates by `(voter_id, tag)`. The
/// `weight` argument is what the aggregator derived for this body —
/// for PV votes it's the cached persistent-committee seat count; for
/// NPV votes it's the result of re-running the lottery from the
/// embedded eligibility signature and the voter's stake.
///
/// If no election exists for `eb_hash`, a vote-placeholder is created
/// at `(eb_slot, current_slot)` with `body_validated_locally = false`.
/// CIP-0164 certs are independently verifiable from vote signatures,
/// so a node can aggregate votes for an EB whose body it hasn't
/// validated locally (or even fetched yet); the producer-side
/// EB-safety gate then ensures any cert built from such an aggregate
/// rides on an empty RB body until the closure validates.
///
/// Quorum: `Σ weight ≥ quorum_fraction × expected_committee_size`.
/// Returns `Some(QuorumFormed)` exactly once per election.
#[allow(clippy::too_many_arguments)]
pub fn record_vote(
    elections: &mut BTreeMap<[u8; 32], EbElection>,
    eb_hash: &[u8; 32],
    eb_slot: u64,
    voter_id: Vec<u8>,
    weight: u32,
    quorum_weight_fraction: f64,
    expected_committee_size: u32,
    current_slot: u64,
    pipeline: PipelineConfig,
    node_id: &str,
) -> Option<QuorumFormed> {
    let election = match elections.get_mut(eb_hash) {
        Some(e) => e,
        None => {
            let elapsed = current_slot.saturating_sub(eb_slot);
            let phase = pipeline.phase_for_elapsed(elapsed)?;
            elections
                .entry(*eb_hash)
                .or_insert(EbElection {
                    announced_slot: eb_slot,
                    phase,
                    seen_slot: current_slot,
                    voted: false,
                    voter_weights: BTreeMap::new(),
                    quorum_reached: false,
                    body_validated_locally: false,
                })
        }
    };

    use std::collections::btree_map::Entry;
    if let Entry::Vacant(e) = election.voter_weights.entry(voter_id) {
        e.insert(weight);
    } else {
        return None; // Duplicate voter
    }

    if election.quorum_reached {
        return None;
    }

    let voted_weight: u64 = election.voter_weights.values().map(|w| *w as u64).sum();
    let threshold = (quorum_weight_fraction * expected_committee_size as f64) as u64;
    if voted_weight < threshold {
        return None;
    }

    election.quorum_reached = true;
    let voters = election.voter_weights.len();
    info!(
        node_id = %node_id,
        eb_slot = election.announced_slot,
        eb_hash = %hex_prefix(eb_hash),
        voted_weight,
        threshold,
        voters,
        "quorum reached for eb"
    );
    Some(QuorumFormed {
        eb_slot: election.announced_slot,
        voted_weight,
        voters,
    })
}

pub(crate) fn hex_prefix(bytes: &[u8]) -> String {
    let n = bytes.len().min(4);
    let mut s = String::with_capacity(n * 2);
    for b in &bytes[..n] {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    use super::super::pipeline::{PipelineConfig, PipelinePhase};

    /// Default quorum: 75% of 1000 = 750 weight.
    const QUORUM_FRACTION: f64 = 0.75;
    const EXPECTED_COMMITTEE_SIZE: u32 = 1000;
    const EB_SLOT: u64 = 10;
    /// `current_slot = 11`, `eb_slot = 10`, delta_hdr=1 → elapsed=1 lands
    /// at the start of the Voting phase, matching `make_election`'s
    /// pre-populated entries.
    const CURRENT_SLOT: u64 = 11;

    fn test_pipeline() -> PipelineConfig {
        PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        }
    }

    fn make_election(slot: u64) -> ([u8; 32], EbElection) {
        let hash = [slot as u8; 32];
        (
            hash,
            EbElection {
                announced_slot: slot,
                phase: PipelinePhase::Voting,
                seen_slot: slot,
                voted: false,
                voter_weights: BTreeMap::new(),
                quorum_reached: false,
                body_validated_locally: true,
            },
        )
    }

    fn vote(
        elections: &mut BTreeMap<[u8; 32], EbElection>,
        hash: &[u8; 32],
        voter_id: Vec<u8>,
        weight: u32,
    ) {
        record_vote(
            elections,
            hash,
            EB_SLOT,
            voter_id,
            weight,
            QUORUM_FRACTION,
            EXPECTED_COMMITTEE_SIZE,
            CURRENT_SLOT,
            test_pipeline(),
            "test",
        );
    }

    #[test]
    fn votes_accumulate_and_dedup() {
        let mut elections = BTreeMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        vote(&mut elections, &hash, vec![1], 100);
        vote(&mut elections, &hash, vec![2], 100);
        vote(&mut elections, &hash, vec![1], 100); // duplicate

        assert_eq!(elections[&hash].voter_weights.len(), 2);
        assert!(!elections[&hash].quorum_reached);
    }

    #[test]
    fn quorum_reached_at_weight_threshold() {
        let mut elections = BTreeMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        // 300 + 200 = 500, below 750 threshold
        vote(&mut elections, &hash, vec![1], 300);
        vote(&mut elections, &hash, vec![2], 200);
        assert!(!elections[&hash].quorum_reached);

        // 500 + 250 = 750, exactly at threshold
        vote(&mut elections, &hash, vec![3], 250);
        assert!(elections[&hash].quorum_reached);
    }

    #[test]
    fn quorum_not_reached_just_below_threshold() {
        let mut elections = BTreeMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        vote(&mut elections, &hash, vec![1], 500);
        vote(&mut elections, &hash, vec![2], 249);
        assert!(!elections[&hash].quorum_reached);
    }

    #[test]
    fn many_unit_voters_reach_quorum() {
        let mut elections = BTreeMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        // 750 distinct voters × weight 1 each crosses 750 threshold.
        for i in 0u32..749 {
            vote(&mut elections, &hash, i.to_le_bytes().to_vec(), 1);
            assert!(!elections[&hash].quorum_reached);
        }
        vote(&mut elections, &hash, 749u32.to_le_bytes().to_vec(), 1);
        assert!(elections[&hash].quorum_reached);
    }

    #[test]
    fn zero_weight_voter_does_not_help_quorum() {
        let mut elections = BTreeMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        vote(&mut elections, &hash, vec![1], 0);
        vote(&mut elections, &hash, vec![2], 0);
        vote(&mut elections, &hash, vec![3], 0);
        assert!(!elections[&hash].quorum_reached);
    }

    #[test]
    fn vote_for_unknown_eb_creates_placeholder() {
        // CIP-0164 cert assembly does not require local body validation
        // — a node aggregates votes for any `eb_hash` it sees signed
        // votes for.  Verify the placeholder is created with
        // `body_validated_locally = false` so the producer-side
        // EB-safety gate can fire on certs built from such aggregates.
        let mut elections = BTreeMap::new();
        let unknown_hash = [0xFF; 32];
        vote(&mut elections, &unknown_hash, vec![1], 500);
        let e = &elections[&unknown_hash];
        assert_eq!(e.announced_slot, EB_SLOT);
        assert!(!e.body_validated_locally);
        assert_eq!(e.voter_weights.len(), 1);
    }

    #[test]
    fn vote_for_expired_eb_is_dropped() {
        // If the EB's pipeline window has already closed, the
        // placeholder is not created and the vote is dropped silently.
        let mut elections = BTreeMap::new();
        let unknown_hash = [0xFE; 32];
        // current_slot far past dedup_window — phase_for_elapsed
        // returns None, so the placeholder path bails.
        record_vote(
            &mut elections,
            &unknown_hash,
            EB_SLOT,
            vec![1],
            500,
            QUORUM_FRACTION,
            EXPECTED_COMMITTEE_SIZE,
            EB_SLOT + 1_000_000,
            test_pipeline(),
            "test",
        );
        assert!(elections.is_empty());
    }

    #[test]
    fn extra_votes_after_quorum_dont_refire() {
        let mut elections = BTreeMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        vote(&mut elections, &hash, vec![1], 400);
        vote(&mut elections, &hash, vec![2], 400);
        assert!(elections[&hash].quorum_reached);

        vote(&mut elections, &hash, vec![3], 200);
        assert!(elections[&hash].quorum_reached);
        assert_eq!(elections[&hash].voter_weights.len(), 3);
    }
}
