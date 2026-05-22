use crate::behaviour::{Behaviour, BehaviourOutcome};
use crate::leios::{LeiosEffect, LeiosState};
use crate::peer::PeerId;
use crate::types::Point;
use std::collections::BTreeMap;
use tracing::info;

#[derive(Debug, Default)]
pub struct T22ThreatBehaviour {
    pub vote_threshold: u8,
    pub hide_eb_tx_recieved: bool,
}

impl T22ThreatBehaviour {
    pub fn new(vote_threshold: u8, hide_eb_tx_received: bool) -> Self {
        Self {
            vote_threshold,
            hide_eb_tx_recieved: hide_eb_tx_received,
        }
    }

    /// Returns true, if eb_data should be processed.
    fn should_process_eb_data(&self, nm: &str, state: &LeiosState, point: &Point) -> bool {
        let persistent_seats = state.voting_config.persistent_seats;
        if persistent_seats == 0 {
            return true;
        }

        let point_checksum = match point {
            Point::Specific { hash, .. } => hash.iter().fold(0u32, |acc, b| acc + *b as u32),
            _ => 0,
        };
        let node_id_checksum = state
            .node_id
            .as_bytes()
            .iter()
            .fold(0u32, |acc, b| acc + *b as u32);

        let checksum = point_checksum + node_id_checksum;
        let decision = (checksum % 100) as u8 <= self.vote_threshold;
        info!(
            "[T22] {nm}: decision={decision}, sum={checksum}, threshold={}, persistent_seats={persistent_seats}",
            self.vote_threshold
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
            self.hide_eb_tx_recieved && !self.should_process_eb_data("on_eb_received", state, point);
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
        let skip_process = self.hide_eb_tx_recieved;
        if skip_process {
            BehaviourOutcome::Replace(vec![])
        } else {
            BehaviourOutcome::Continue
        }
    }
}