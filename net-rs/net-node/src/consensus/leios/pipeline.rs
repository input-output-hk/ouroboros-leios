//! CIP-0164 Linear Leios pipeline types and timing logic.
//!
//! Each EB progresses through pipeline phases based on elapsed slots since
//! its announcement: EquivocationCheck (3×Δhdr) → Voting (L_vote) →
//! Diffusing (L_diff) → CertEligible (held until pruned).

use std::collections::HashSet;
use std::time::Instant;

use net_core::types::Point;

/// Pipeline phase for an EB election (CIP-0164 Linear Leios).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PipelinePhase {
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
pub(crate) struct EbElection {
    pub(crate) eb_point: Point,
    pub(crate) announced_slot: u64,
    pub(crate) phase: PipelinePhase,
    #[allow(dead_code)] // used by future telemetry
    pub(crate) validated_at: Instant,
    /// True after this node has cast its vote for this EB.
    pub(crate) voted: bool,
    /// Unique voter IDs that have voted for this EB.
    pub(crate) voters: HashSet<Vec<u8>>,
    /// True once quorum has been reached.
    pub(crate) quorum_reached: bool,
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
    /// elapsed since its announcement. Returns `None` if the election
    /// has expired (past dedup_window after CertEligible).
    pub(crate) fn phase_for_elapsed(&self, elapsed: u64) -> Option<PipelinePhase> {
        let equivocation_end = 3 * self.delta_hdr;
        let voting_end = equivocation_end + self.vote_window;
        let diffuse_end = voting_end + self.diffuse_window;
        let expiry = diffuse_end + self.dedup_window;
        if elapsed < equivocation_end {
            Some(PipelinePhase::EquivocationCheck)
        } else if elapsed < voting_end {
            Some(PipelinePhase::Voting)
        } else if elapsed < diffuse_end {
            Some(PipelinePhase::Diffusing)
        } else if elapsed < expiry {
            Some(PipelinePhase::CertEligible)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pipeline config: delta_hdr=1, vote=5, diffuse=5, dedup=10
    /// Boundaries: EquivCheck [0,3), Voting [3,8), Diffusing [8,13),
    /// CertEligible [13,23), expired ≥23
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
        // EquivocationCheck: elapsed 0..3
        assert_eq!(
            p.phase_for_elapsed(0),
            Some(PipelinePhase::EquivocationCheck)
        );
        assert_eq!(
            p.phase_for_elapsed(2),
            Some(PipelinePhase::EquivocationCheck)
        );
        // Voting: elapsed 3..8
        assert_eq!(p.phase_for_elapsed(3), Some(PipelinePhase::Voting));
        assert_eq!(p.phase_for_elapsed(7), Some(PipelinePhase::Voting));
        // Diffusing: elapsed 8..13
        assert_eq!(p.phase_for_elapsed(8), Some(PipelinePhase::Diffusing));
        assert_eq!(p.phase_for_elapsed(12), Some(PipelinePhase::Diffusing));
        // CertEligible: elapsed 13..23
        assert_eq!(p.phase_for_elapsed(13), Some(PipelinePhase::CertEligible));
        assert_eq!(p.phase_for_elapsed(22), Some(PipelinePhase::CertEligible));
        // Expired: elapsed ≥23
        assert_eq!(p.phase_for_elapsed(23), None);
        assert_eq!(p.phase_for_elapsed(100), None);
    }
}
