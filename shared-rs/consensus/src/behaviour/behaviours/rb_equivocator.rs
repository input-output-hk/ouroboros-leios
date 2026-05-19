//! `RbEquivocator` — every time the local node would emit an honest
//! RB for a slot it wins, also emit a duplicate carrying a different
//! body.  Triggers CIP-0164 RB-header equivocation detection on peers.
//!
//! Implemented as a single strategy hook
//! ([`Behaviour::rb_production_strategy`]) returning
//! [`RbProductionStrategy::Equivocate`].  The wrapper sees the strategy
//! and signs two RBs from one lottery win; this crate does not own the
//! wire-format RB construction path.

use crate::behaviour::{Behaviour, RbProductionStrategy};
use crate::leios::LeiosState;
use crate::praos::PraosState;

#[derive(Debug, Default)]
pub struct RbEquivocator;

impl Behaviour for RbEquivocator {
    fn name(&self) -> &'static str {
        "rb-equivocator"
    }

    fn rb_production_strategy(
        &mut self,
        _leios: &LeiosState,
        _praos: &PraosState,
        _slot: u64,
    ) -> RbProductionStrategy {
        RbProductionStrategy::Equivocate
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
            expected_committee_size: 1,
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
    fn strategy_is_equivocate() {
        let (l, p) = dummy_states();
        let mut b = RbEquivocator::default();
        assert_eq!(
            b.rb_production_strategy(&l, &p, 42),
            RbProductionStrategy::Equivocate
        );
    }

    #[test]
    fn name_is_kebab_case() {
        let b = RbEquivocator::default();
        assert_eq!(b.name(), "rb-equivocator");
    }
}
