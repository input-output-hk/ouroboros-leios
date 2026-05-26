//! `LazyVoter` — never casts a vote.  Overrides the CIP-0164 voting
//! predicate to always abstain with the configured reason.  Useful for
//! measuring committee resilience to "silent" adversaries who hold
//! their stake but contribute no Leios votes.

use crate::behaviour::{Behaviour, DecisionOutcome};
use crate::leios::{LeiosState, NoVoteReason, VoteDecision};

#[derive(Debug, Clone)]
pub struct LazyVoter {
    /// Reason reported via [`crate::leios::LeiosEffect::NoVote`].  Defaults to
    /// `Declined` so telemetry can tell policy abstentions apart from
    /// honest predicate failures (`WrongEB` / `MissingTX` /
    /// `LateRBHeader`); set to one of those if a sweep specifically
    /// wants to mimic an undetectable lazy voter.
    pub reason: NoVoteReason,
}

impl Default for LazyVoter {
    fn default() -> Self {
        Self {
            reason: NoVoteReason::Declined,
        }
    }
}

impl Behaviour for LazyVoter {
    fn name(&self) -> &'static str {
        "lazy-voter"
    }

    fn decide_vote(
        &mut self,
        _state: &LeiosState,
        _eb_hash: &[u8; 32],
        _eb_slot: u64,
        _honest: &VoteDecision,
    ) -> DecisionOutcome<VoteDecision> {
        DecisionOutcome::Override(Err(self.reason))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn name_is_kebab_case() {
        assert_eq!(LazyVoter::default().name(), "lazy-voter");
    }

    #[test]
    fn overrides_to_abstain() {
        let mut voter = LazyVoter::default();
        // The honest decision doesn't matter; LazyVoter always overrides.
        let honest = Ok((true, None));
        // We can't build a LeiosState here cheaply, so just check the
        // override path returns the configured reason.  An integration
        // test in leios::tests exercises the full path.
        let dummy_hash = [0u8; 32];
        // Construct a minimal state — the hook ignores it but the
        // signature requires it.
        use crate::config::CommitteeSelection;
        use crate::elections::{Elections, ElectionsConfig};
        use crate::leios::VotingConfig;
        use crate::pipeline::PipelineConfig;
        use std::collections::BTreeMap;
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
            persistent_seats: 1,
            retry_vote_in_window: true,
        };
        let state = LeiosState::new("t".to_string(), elections, voting, pipeline);
        match voter.decide_vote(&state, &dummy_hash, 10, &honest) {
            DecisionOutcome::Override(Err(r)) => assert_eq!(r, NoVoteReason::Declined),
            other => panic!("expected Override(Err(Declined)), got {other:?}"),
        }
    }
}
