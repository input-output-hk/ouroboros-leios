//! CIP-0164 Linear Leios pipeline types and timing logic.
//!
//! Each EB progresses through pipeline phases based on elapsed slots since
//! its announcement: EquivocationCheck (3×Δhdr) → Voting (L_vote) →
//! Diffusing (L_diff) → CertEligible (held until pruned).

use std::collections::BTreeMap;

/// Pipeline phase for an EB election (CIP-0164 Linear Leios).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PipelinePhase {
    /// Waiting for equivocation detection (3 × Δhdr slots).
    EquivocationCheck,
    /// Voting window open (L_vote slots).
    Voting,
    /// Votes diffusing, certificate may form (L_diff slots).
    Diffusing,
    /// Pipeline complete, certificate may be included in an RB.
    CertEligible,
}

/// Per-EB election state.
///
/// The struct is sans-IO and carries no transport identifier for the EB —
/// callers key elections by EB hash externally and pass `eb_hash` to
/// `record_vote` for any logging that needs it.
///
/// `voter_weights` is a `BTreeMap` so iteration order is deterministic.
/// Election-side aggregations (`Σ weight`, `len()`) are commutative, so
/// determinism isn't strictly needed here, but the simulator's contract
/// is uniform: no `HashMap` traversal anywhere in shared-consensus.
pub struct EbElection {
    pub announced_slot: u64,
    pub phase: PipelinePhase,
    /// Slot at which this node first learned of the EB. Used by the
    /// `LateEB` voting predicate (CIP-0164): a voter must have received
    /// the EB before its voting window closes
    /// (`announced_slot + 3·Δhdr + L_vote`).
    pub seen_slot: u64,
    /// True after this node has cast its vote for this EB.
    pub voted: bool,
    /// Per-voter weight: voter_id+tag → derived weight.
    ///
    /// The unit is mode-dependent.  Under `WfaLs` the value is the
    /// voter's seat count; under `EveryoneVotes` it is `1`; under
    /// `StakeCentile` it is the voter's stake.  The aggregator sums
    /// these values and compares against
    /// `quorum_weight_fraction × expected_total_weight`, where
    /// `expected_total_weight` is computed in the same units (see
    /// [`crate::committee::expected_total_weight`]).
    pub voter_weights: BTreeMap<Vec<u8>, u64>,
    /// True once quorum has been reached.
    pub quorum_reached: bool,
    /// True once `on_validated_eb` has fired for this hash on the local
    /// node — i.e., the body is in hand and verified.  An election can
    /// exist with this flag false if the node received votes for an EB
    /// whose body has not yet been fetched or validated locally;
    /// CIP-0164 allows cert formation from votes alone, so the
    /// election aggregates either way.  Drives the producer-side
    /// EB-safety gate (`endorsed_unvalidated_ebs` in `LeiosState`).
    pub body_validated_locally: bool,
}

/// CIP-0164 pipeline timing configuration.
#[derive(Debug, Clone, Copy)]
pub struct PipelineConfig {
    pub delta_hdr: u64,
    pub vote_window: u64,
    pub diffuse_window: u64,
    pub dedup_window: u64,
}

impl PipelineConfig {
    /// Compute the pipeline phase for an EB given the number of slots
    /// elapsed since its announcement.  Under the strict parent-only
    /// cert rule, an EB stays attachable as a cert for as long as it
    /// is the chain tip's announcement; lifetime is governed by the
    /// chain-progress prune in [`crate::leios::LeiosState::on_slot`],
    /// not by elapsed slots.  CertEligible therefore has no time
    /// upper bound — once an EB has passed Diffusing it stays
    /// CertEligible forever (or until pruned).
    pub fn phase_for_elapsed(&self, elapsed: u64) -> PipelinePhase {
        let equivocation_end = 3 * self.delta_hdr;
        let voting_end = equivocation_end + self.vote_window;
        let diffuse_end = voting_end + self.diffuse_window;
        if elapsed < equivocation_end {
            PipelinePhase::EquivocationCheck
        } else if elapsed < voting_end {
            PipelinePhase::Voting
        } else if elapsed < diffuse_end {
            PipelinePhase::Diffusing
        } else {
            PipelinePhase::CertEligible
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pipeline config: delta_hdr=1, vote=5, diffuse=5, dedup=10
    /// Boundaries: EquivCheck [0,3), Voting [3,8), Diffusing [8,13),
    /// CertEligible [13, ∞)
    fn test_pipeline() -> PipelineConfig {
        PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        }
    }

    #[test]
    fn phase_for_elapsed_boundaries() {
        let p = test_pipeline();
        assert_eq!(p.phase_for_elapsed(0), PipelinePhase::EquivocationCheck);
        assert_eq!(p.phase_for_elapsed(2), PipelinePhase::EquivocationCheck);
        assert_eq!(p.phase_for_elapsed(3), PipelinePhase::Voting);
        assert_eq!(p.phase_for_elapsed(7), PipelinePhase::Voting);
        assert_eq!(p.phase_for_elapsed(8), PipelinePhase::Diffusing);
        assert_eq!(p.phase_for_elapsed(12), PipelinePhase::Diffusing);
        assert_eq!(p.phase_for_elapsed(13), PipelinePhase::CertEligible);
        // CertEligible has no upper bound — chain-progress prune in
        // LeiosState::on_slot is what bounds the lifetime.
        assert_eq!(p.phase_for_elapsed(100), PipelinePhase::CertEligible);
        assert_eq!(p.phase_for_elapsed(1_000_000), PipelinePhase::CertEligible);
    }
}
