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
    fn should_process_eb_data(&self, state: &LeiosState, point: &Point) -> bool {
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
        (checksum % 100) as u8 <= self.vote_threshold
    }

    fn trace_decision(&self, fn_name: &str, processed: bool, persistent_seats: u32, point: Option<&Point>) {
        let decision = if processed { "processed" } else { "declined" };
        info!("[T22] {}: decision={}, persistent_seats={}", fn_name, decision, persistent_seats);
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
        let should_process = self.should_process_eb_data(state, point);
        self.trace_decision(
            "on_eb_offered",
            should_process,
            state.voting_config.persistent_seats,
            Some(point),
        );
        if should_process {
            BehaviourOutcome::Continue
        } else {
            BehaviourOutcome::Replace(vec![]) // отклонить EB
        }
    }

    fn on_eb_txs_offered(
        &mut self,
        state: &LeiosState,
        point: &Point,
        _peer: PeerId,
        _bitmap: &BTreeMap<u16, u64>,
    ) -> BehaviourOutcome<LeiosEffect> {
        let should_process = self.should_process_eb_data(state, point);
        self.trace_decision(
            "on_eb_txs_offered",
            should_process,
            state.voting_config.persistent_seats,
            Some(point),
        );
        if should_process {
            BehaviourOutcome::Continue
        } else {
            BehaviourOutcome::Replace(vec![]) // отклонить EB txs
        }
    }

    fn on_eb_received(
        &mut self,
        state: &LeiosState,
        point: &Point,
        _tx_hashes: &[[u8; 32]],
    ) -> BehaviourOutcome<LeiosEffect> {
        let skip_process = self.hide_eb_tx_recieved && !self.should_process_eb_data(state, point);
        self.trace_decision(
            "on_eb_received",
            !skip_process,
            state.voting_config.persistent_seats,
            Some(point),
        );
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
        self.trace_decision("on_tx_received", !skip_process, 0, None);
        if skip_process {
            BehaviourOutcome::Replace(vec![])
        } else {
            BehaviourOutcome::Continue
        }
    }
}