use crate::behaviour::{Behaviour, BehaviourOutcome};
use crate::leios::{LeiosEffect, LeiosState};
use crate::peer::PeerId;
use crate::types::Point;
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use tracing::info;

#[derive(Debug, Default)]
pub struct T22ThreatBehaviour {
    pub vote_threshold: u8,
    pub non_voting_threshold: u8,
    pub hide_eb_tx_received: bool,
}

impl T22ThreatBehaviour {
    pub fn new(vote_threshold: u8, hide_eb_tx_received: bool, non_voting_threshold: u8) -> Self {
        Self {
            vote_threshold,
            hide_eb_tx_received,
            non_voting_threshold
        }
    }

    /// Returns true, if eb_data should be processed.
    fn should_process_eb_data(&self, nm: &str, state: &LeiosState, point: &Point) -> bool {
        let persistent_seats = state.voting_config.persistent_seats;
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        if let Point::Specific { hash, .. } = point {
            hash.hash(&mut hasher);
        }
        state.node_id.hash(&mut hasher);

        let checksum = hasher.finish();
        let threshold = if persistent_seats > 0 {
            self.vote_threshold
        } else {
            self.non_voting_threshold
        };
        let decision = (checksum % 100) as u8 <= threshold;
        info!(
            "[T22] {nm}: decision={decision}, sum={checksum}, threshold={threshold}, persistent_seats={persistent_seats}",
        );
        decision
    }
}

impl Behaviour for T22ThreatBehaviour {
    fn name(&self) -> &'static str {
        "t22"
    }

    fn on_eb_offered(
        &mut self,
        state: &LeiosState,
        point: &Point,
        _peer: PeerId,
    ) -> BehaviourOutcome<LeiosEffect> {
        let should_process = self.should_process_eb_data("on_eb_offered", state, point);
        if should_process {
            BehaviourOutcome::Continue
        } else {
            BehaviourOutcome::Replace(vec![])
        }
    }

    fn on_eb_txs_offered(
        &mut self,
        state: &LeiosState,
        point: &Point,
        _peer: PeerId,
        _bitmap: &BTreeMap<u16, u64>,
    ) -> BehaviourOutcome<LeiosEffect> {
        let should_process = self.should_process_eb_data("on_eb_txs_offered", state, point);
        if should_process {
            BehaviourOutcome::Continue
        } else {
            BehaviourOutcome::Replace(vec![])
        }
    }

    fn on_eb_received(
        &mut self,
        state: &LeiosState,
        point: &Point,
        _tx_hashes: &[[u8; 32]],
    ) -> BehaviourOutcome<LeiosEffect> {
        let skip_process =
            self.hide_eb_tx_received && !self.should_process_eb_data("on_eb_received", state, point);
        if skip_process {
            BehaviourOutcome::Replace(vec![])
        } else {
            BehaviourOutcome::Continue
        }
    }

    fn on_tx_received(
        &mut self,
        _state: &crate::mempool::MempoolState,
        _tx_id: &crate::mempool::TxId,
        _body: &[u8],
    ) -> BehaviourOutcome<crate::mempool::MempoolEffect> {
        let skip_process = self.hide_eb_tx_received;
        if skip_process {
            BehaviourOutcome::Replace(vec![])
        } else {
            BehaviourOutcome::Continue
        }
    }
}