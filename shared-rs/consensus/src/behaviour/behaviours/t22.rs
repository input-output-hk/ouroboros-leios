/*!

T21 and T22 Threats: selectively withhold data from voting committee (T21) and honest nodes (T22).

General description:
--------------------
This behaviour emulates network disruption, implied by T21 and T22 threat models. Irrespective of
the method of disruption, the outcome is always the same: EB-related messages don't come to
the committee nodes (T21) or honest nodes (T22).

This threat implementation emulates the final effect: it drops incoming EB-related messages for
some nodes (according to provided parameters).

EB-messages filtering details:
------------------------------
For each point and node, a deterministic checksum is calculated using the point hash and node id.
If the checksum is above the provided threshold, EB-related messages are dropped. Thus, the set of
nodes that are affected by the threat is deterministic, but unpredictable. Also, the set is
different for each point.

The thresholds are specified separately for voting and non-voting nodes, so the behaviour can be
configured to emulate T21 (drop EB messages for voting nodes) or T22 (drop EB messages for
non-voting nodes).

This implementation is more stressful for the network than the original T21/T22 definition, since
here we assume that any partial disruption is achievable (some of possible disruptions
could be unimplementable in practice, e.g. in case of direct links between honest nodes).

Parameters:
-----------
- `vote_threshold`: Percentage of EB-related messages (0-100), that are to be delivered to
   voting (committee) nodes.
- `non_voting_threshold`: Percentage of EB-related messages (0-100), that are to be delivered
   to non-voting (non-committee) nodes.
- `hide_eb_tx_received`: In case of `false`, only eb-offered, eb-txs-offered events are
   ignored (so block offers are dropped). In case of `true`, also eb-received and tx-received
   events are ignored.

The threshold parameters are probabilistic: they specify average cutoff. So, if some threshold
is set to 70, it means that for some points 75% of nodes will have hash%100 > 70 (and pass the
threshold); but also for some other points only 65% of nodes will make it.

*/

use crate::behaviour::{Behaviour, BehaviourOutcome};
use crate::leios::{LeiosEffect, LeiosState};
use crate::peer::PeerId;
use crate::types::Point;
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

#[derive(Debug, Default)]
pub struct T22ThreatBehaviour {
    pub vote_threshold: u8,
    pub non_voting_threshold: u8,
    pub hide_eb_tx_received: bool,
}

impl T22ThreatBehaviour {
    pub fn new(vote_threshold: u8, non_voting_threshold: u8, hide_eb_tx_received: bool) -> Self {
        Self {
            vote_threshold,
            non_voting_threshold,
            hide_eb_tx_received,
        }
    }

    /// Returns true, if eb_data should be processed.
    fn should_process_eb_data(&self, _nm: &str, state: &LeiosState, point: &Point) -> bool {
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
        // `checksum % 100` yields values in 0..=99, so use `< threshold` to make
        // threshold semantics match percentages exactly: 0 => 0%, 100 => 100%.
        let decision = ((checksum % 100) as u8) < threshold;
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
        BehaviourOutcome::Continue
    }
}