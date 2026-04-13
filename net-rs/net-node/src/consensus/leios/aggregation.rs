//! Vote aggregation, quorum detection, and certificate formation.
//!
//! Tracks votes per EB election, detects when quorum is reached.
//! Certificate formation and RB header population are in Commit 5.

use std::collections::HashMap;

use tracing::info;

use super::pipeline::EbElection;

/// Record a vote for an EB. Deduplicates by voter_id.
/// Logs when quorum is first reached.
pub(crate) fn record_vote(
    elections: &mut HashMap<[u8; 32], EbElection>,
    eb_hash: &[u8; 32],
    voter_id: Vec<u8>,
    node_id: &str,
) {
    let Some(election) = elections.get_mut(eb_hash) else {
        return; // No election for this EB (expired or not yet seen)
    };

    if !election.voters.insert(voter_id) {
        return; // Duplicate voter
    }

    // Simple quorum check: ≥ 3 unique voters for MVP.
    // Future: use stake-weighted threshold from config.
    if !election.quorum_reached && election.voters.len() >= 3 {
        election.quorum_reached = true;
        info!(
            node_id = %node_id,
            eb_point = %election.eb_point,
            vote_count = election.voters.len(),
            "quorum reached for eb"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use net_core::types::Point;
    use std::collections::HashSet;
    use std::time::Instant;

    use super::super::pipeline::PipelinePhase;

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
                voters: HashSet::new(),
                quorum_reached: false,
            },
        )
    }

    #[test]
    fn votes_accumulate_and_dedup() {
        let mut elections = HashMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        record_vote(&mut elections, &hash, vec![1], "test");
        record_vote(&mut elections, &hash, vec![2], "test");
        record_vote(&mut elections, &hash, vec![1], "test"); // duplicate

        assert_eq!(elections[&hash].voters.len(), 2);
        assert!(!elections[&hash].quorum_reached);
    }

    #[test]
    fn quorum_reached_at_threshold() {
        let mut elections = HashMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        record_vote(&mut elections, &hash, vec![1], "test");
        record_vote(&mut elections, &hash, vec![2], "test");
        assert!(!elections[&hash].quorum_reached);

        record_vote(&mut elections, &hash, vec![3], "test");
        assert!(elections[&hash].quorum_reached);
    }

    #[test]
    fn votes_for_unknown_eb_ignored() {
        let mut elections = HashMap::new();
        let unknown_hash = [0xFF; 32];
        record_vote(&mut elections, &unknown_hash, vec![1], "test");
        assert!(elections.is_empty());
    }

    #[test]
    fn extra_votes_after_quorum_dont_refire() {
        let mut elections = HashMap::new();
        let (hash, election) = make_election(10);
        elections.insert(hash, election);

        for i in 0..10u8 {
            record_vote(&mut elections, &hash, vec![i], "test");
        }
        assert!(elections[&hash].quorum_reached);
        assert_eq!(elections[&hash].voters.len(), 10);
    }
}
