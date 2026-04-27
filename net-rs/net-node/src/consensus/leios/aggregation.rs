//! Vote aggregation, quorum detection, and certificate formation.
//!
//! Tracks votes per EB election, detects when quorum is reached.
//! Certificate formation and RB header population are in Commit 5.

use std::collections::HashMap;

use tracing::info;

use super::pipeline::EbElection;

/// Returned from `record_vote` when a vote causes quorum to fire for the
/// first time. The caller uses this to emit `LeiosQuorumReached` telemetry.
pub(crate) struct QuorumFormed {
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
/// Quorum: `Σ weight ≥ quorum_fraction × expected_committee_size`.
/// Returns `Some(QuorumFormed)` exactly once per election.
pub(crate) fn record_vote(
    elections: &mut HashMap<[u8; 32], EbElection>,
    eb_hash: &[u8; 32],
    voter_id: Vec<u8>,
    weight: u32,
    quorum_weight_fraction: f64,
    expected_committee_size: u32,
    node_id: &str,
) -> Option<QuorumFormed> {
    let election = elections.get_mut(eb_hash)?;

    use std::collections::hash_map::Entry;
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
        eb_point = %election.eb_point,
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

#[cfg(test)]
mod tests {
    use super::*;
    use net_core::types::Point;
    use std::time::Instant;

    use super::super::pipeline::PipelinePhase;

    /// Default quorum: 75% of 1000 = 750 weight.
    const QUORUM_FRACTION: f64 = 0.75;
    const EXPECTED_COMMITTEE_SIZE: u32 = 1000;

    fn make_election(slot: u64) -> ([u8; 32], EbElection) {
        let hash = [slot as u8; 32];
        (
            hash,
            EbElection {
                eb_point: Point::Specific { slot, hash },
                announced_slot: slot,
                phase: PipelinePhase::Voting,
                validated_at: Instant::now(),
                voted: false,
                voter_weights: HashMap::new(),
                quorum_reached: false,
            },
        )
    }

    fn vote(
        elections: &mut HashMap<[u8; 32], EbElection>,
        hash: &[u8; 32],
        voter_id: Vec<u8>,
        weight: u32,
    ) {
        record_vote(
            elections,
            hash,
            voter_id,
            weight,
            QUORUM_FRACTION,
            EXPECTED_COMMITTEE_SIZE,
            "test",
        );
    }

    #[test]
    fn votes_accumulate_and_dedup() {
        let mut elections = HashMap::new();
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
        let mut elections = HashMap::new();
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
        let mut elections = HashMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        vote(&mut elections, &hash, vec![1], 500);
        vote(&mut elections, &hash, vec![2], 249);
        assert!(!elections[&hash].quorum_reached);
    }

    #[test]
    fn many_unit_voters_reach_quorum() {
        let mut elections = HashMap::new();
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
        let mut elections = HashMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        vote(&mut elections, &hash, vec![1], 0);
        vote(&mut elections, &hash, vec![2], 0);
        vote(&mut elections, &hash, vec![3], 0);
        assert!(!elections[&hash].quorum_reached);
    }

    #[test]
    fn votes_for_unknown_eb_ignored() {
        let mut elections = HashMap::new();
        let unknown_hash = [0xFF; 32];
        vote(&mut elections, &unknown_hash, vec![1], 500);
        assert!(elections.is_empty());
    }

    #[test]
    fn extra_votes_after_quorum_dont_refire() {
        let mut elections = HashMap::new();
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
