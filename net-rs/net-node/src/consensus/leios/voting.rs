//! EB-triggered vote production with committee selection.
//!
//! When an EB's election enters the Voting phase, this module decides
//! whether the local node should vote (via CommitteeSelection) and, if
//! so, builds and injects the vote into the network.

use net_core::multi_peer::types::NetworkCommand;
use tokio::sync::mpsc;
use tracing::info;

use crate::config::CommitteeSelection;
use crate::production::VoteBody;

use super::wfa;

/// Voting-related configuration extracted from ProductionConfig.
pub struct VotingConfig {
    pub committee_selection: CommitteeSelection,
    pub stake: u64,
    pub total_stake: u64,
    pub persistent_vote_bytes: usize,
    pub non_persistent_vote_bytes: usize,
    /// Number of PV seats this node holds in the persistent committee.
    /// Pre-computed at startup from the registry; 0 means no PV vote.
    pub persistent_seats: u32,
}

/// Try to vote on an EB. Returns true if at least one vote body was
/// injected. Under WfaLs a node may emit both a PV and an NPV vote for
/// the same EB; under EveryoneVotes / StakeCentile only PV (with weight 1).
///
/// No RNG argument: PV emission is deterministic from the cached
/// committee, and NPV is deterministic from the eligibility signature.
pub(crate) async fn try_vote_on_eb(
    node_id: &str,
    eb_hash: &[u8; 32],
    eb_slot: u64,
    config: &VotingConfig,
    commands: &mpsc::Sender<NetworkCommand>,
) -> bool {
    let mut bodies: Vec<(usize, VoteBody)> = Vec::new();

    // Persistent: emit one body iff this pool has at least one PV seat.
    // The body carries no weight; the aggregator looks up persistent_seats
    // for voter_id from the cached committee.
    if config.persistent_seats > 0 {
        bodies.push((
            config.persistent_vote_bytes,
            VoteBody::stub_persistent(eb_slot, node_id.as_bytes(), config.stake, eb_hash),
        ));
    }

    // Non-persistent: only WfaLs emits NPV. Compute the deterministic
    // eligibility proof (a stand-in for the VRF output), then count this
    // pool's lottery wins from it. Embed the proof — never the count —
    // in the vote body. The aggregator independently re-runs the lottery
    // from the proof + the voter's ledger-resolved stake to derive the
    // same count.
    let n_npv = config.committee_selection.non_persistent_voters();
    if n_npv > 0 {
        let signature = wfa::npv_eligibility_signature(node_id.as_bytes(), eb_hash, eb_slot);
        let wins = wfa::count_npv_wins(&signature, config.stake, config.total_stake, n_npv);
        if wins > 0 {
            bodies.push((
                config.non_persistent_vote_bytes,
                VoteBody::stub_non_persistent(
                    eb_slot,
                    node_id.as_bytes(),
                    config.stake,
                    signature,
                    eb_hash,
                ),
            ));
        }
    }

    if bodies.is_empty() {
        return false;
    }

    let mut votes = Vec::with_capacity(bodies.len());
    let mut data = Vec::with_capacity(bodies.len());
    for (size, body) in &bodies {
        let encoded = body.encode(*size);
        info!(
            node_id = %node_id,
            eb_slot,
            tag = body.tag,
            pv_seats = config.persistent_seats,
            size = encoded.len(),
            "vote produced for eb"
        );
        // Distinguish PV vs NPV in the vote_id so a node can issue both.
        let mut id_bytes = node_id.as_bytes().to_vec();
        id_bytes.push(body.tag);
        votes.push((eb_slot, id_bytes));
        data.push(encoded);
    }

    let _ = commands
        .send(NetworkCommand::InjectLeiosVotes { votes, data })
        .await;

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn everyone_votes_config(stake: u64, total_stake: u64, persistent_seats: u32) -> VotingConfig {
        VotingConfig {
            committee_selection: CommitteeSelection::EveryoneVotes,
            stake,
            total_stake,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
            persistent_seats,
        }
    }

    #[tokio::test]
    async fn pv_vote_produced_when_seated() {
        let (tx, mut rx) = mpsc::channel(8);
        let config = everyone_votes_config(100, 1000, 1);
        let hash = [0xAB; 32];

        let voted = try_vote_on_eb("node-0", &hash, 10, &config, &tx).await;
        assert!(voted);

        match rx.try_recv() {
            Ok(NetworkCommand::InjectLeiosVotes { votes, data }) => {
                assert_eq!(votes.len(), 1);
                assert_eq!(votes[0].0, 10); // eb_slot
                assert!(!data.is_empty());
                assert!(data[0].len() >= 130);
            }
            other => panic!("expected InjectLeiosVotes, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn no_vote_when_no_seats_and_no_npv() {
        let (tx, mut rx) = mpsc::channel(8);
        let config = everyone_votes_config(100, 1000, 0);
        let hash = [0xAB; 32];

        let voted = try_vote_on_eb("node-0", &hash, 10, &config, &tx).await;
        assert!(!voted);
        assert!(rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn wfa_ls_emits_pv_and_npv_when_both_win() {
        let (tx, mut rx) = mpsc::channel(8);
        let config = VotingConfig {
            committee_selection: CommitteeSelection::WfaLs {
                persistent_voters: 480,
                non_persistent_voters: 120,
            },
            stake: 400, // 40% of total → high NPV win probability
            total_stake: 1000,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
            persistent_seats: 5,
        };
        let hash = [0xAB; 32];

        let voted = try_vote_on_eb("node-0", &hash, 10, &config, &tx).await;
        assert!(voted);

        match rx.try_recv() {
            Ok(NetworkCommand::InjectLeiosVotes { votes, data }) => {
                // Two bodies: one PV (tag=0), one NPV (tag=1).
                assert_eq!(votes.len(), 2);
                assert_eq!(data.len(), 2);
                let decoded: Vec<_> = data.iter().map(|d| VoteBody::decode(d).unwrap()).collect();
                let tags: Vec<u8> = decoded.iter().map(|b| b.tag).collect();
                assert!(tags.contains(&0));
                assert!(tags.contains(&1));
                let npv = decoded.iter().find(|b| b.tag == 1).unwrap();
                assert!(npv.eligibility_signature.is_some());
            }
            other => panic!("expected InjectLeiosVotes, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn wfa_ls_no_pv_seats_only_npv() {
        let (tx, mut rx) = mpsc::channel(8);
        let config = VotingConfig {
            committee_selection: CommitteeSelection::WfaLs {
                persistent_voters: 480,
                non_persistent_voters: 1000, // very high → almost certain NPV win
            },
            stake: 100,
            total_stake: 1000,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
            persistent_seats: 0,
        };
        let hash = [0xAB; 32];

        let voted = try_vote_on_eb("node-0", &hash, 10, &config, &tx).await;
        assert!(voted);

        match rx.try_recv() {
            Ok(NetworkCommand::InjectLeiosVotes { votes, data }) => {
                assert_eq!(votes.len(), 1);
                let body = VoteBody::decode(&data[0]).unwrap();
                assert_eq!(body.tag, 1); // NPV only
            }
            other => panic!("expected InjectLeiosVotes, got {:?}", other),
        }
    }
}
