//! EB-triggered vote production with committee selection.
//!
//! When an EB's election enters the Voting phase, this module decides
//! whether the local node should vote (via CommitteeSelection) and, if
//! so, builds and injects the vote into the network.

use net_core::multi_peer::types::NetworkCommand;
use rand::rngs::StdRng;
use tokio::sync::mpsc;
use tracing::info;

use crate::config::{CommitteeSelection, VoteDecision};
use crate::production::VoteBody;

/// Voting-related configuration extracted from ProductionConfig.
pub struct VotingConfig {
    pub committee_selection: CommitteeSelection,
    pub stake: u64,
    pub total_stake: u64,
    pub persistent_vote_bytes: usize,
    pub non_persistent_vote_bytes: usize,
}

/// Try to vote on an EB. Returns true if a vote was produced and injected.
#[allow(clippy::too_many_arguments)]
pub(crate) async fn try_vote_on_eb(
    node_id: &str,
    eb_hash: &[u8; 32],
    eb_slot: u64,
    config: &VotingConfig,
    vote_probability: f64,
    rng: &mut StdRng,
    commands: &mpsc::Sender<NetworkCommand>,
) -> bool {
    let decision = config.committee_selection.decide_vote(
        config.stake,
        config.total_stake,
        vote_probability,
        rng,
    );

    let (vote_bytes, body) = match decision {
        VoteDecision::NoVote => return false,
        VoteDecision::PersistentVote => (
            config.persistent_vote_bytes,
            VoteBody::stub_persistent(eb_slot, node_id.as_bytes(), eb_hash),
        ),
        VoteDecision::NonPersistentVote => (
            config.non_persistent_vote_bytes,
            VoteBody::stub_non_persistent(eb_slot, node_id.as_bytes(), eb_hash),
        ),
    };

    let encoded = body.encode(vote_bytes);
    let vote_id = (eb_slot, node_id.as_bytes().to_vec());

    info!(
        node_id = %node_id,
        eb_slot,
        size = encoded.len(),
        "vote produced for eb"
    );

    let _ = commands
        .send(NetworkCommand::InjectLeiosVotes {
            votes: vec![vote_id],
            data: vec![encoded],
        })
        .await;

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::SeedableRng;

    fn everyone_votes_config(stake: u64, total_stake: u64) -> VotingConfig {
        VotingConfig {
            committee_selection: CommitteeSelection::EveryoneVotes,
            stake,
            total_stake,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
        }
    }

    #[tokio::test]
    async fn vote_produced_everyone_votes() {
        let (tx, mut rx) = mpsc::channel(8);
        let config = everyone_votes_config(100, 1000);
        let mut rng = StdRng::seed_from_u64(42);
        let hash = [0xAB; 32];

        let voted = try_vote_on_eb("node-0", &hash, 10, &config, 1.0, &mut rng, &tx).await;
        assert!(voted);

        match rx.try_recv() {
            Ok(NetworkCommand::InjectLeiosVotes { votes, data }) => {
                assert_eq!(votes.len(), 1);
                assert_eq!(votes[0].0, 10); // eb_slot
                assert!(!data.is_empty());
                assert!(data[0].len() >= 130); // persistent vote size
            }
            other => panic!("expected InjectLeiosVotes, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn no_vote_zero_stake() {
        let (tx, mut rx) = mpsc::channel(8);
        let config = everyone_votes_config(0, 1000);
        let mut rng = StdRng::seed_from_u64(42);
        let hash = [0xAB; 32];

        let voted = try_vote_on_eb("node-0", &hash, 10, &config, 1.0, &mut rng, &tx).await;
        assert!(!voted);
        assert!(rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn no_vote_low_centile() {
        use rand::SeedableRng;
        let (tx, mut rx) = mpsc::channel(8);
        let config = VotingConfig {
            committee_selection: CommitteeSelection::StakeCentile {
                top_centile_of_stake: 0.0, // nobody votes
            },
            stake: 100,
            total_stake: 1000,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
        };
        let mut rng = StdRng::seed_from_u64(42);
        let hash = [0xAB; 32];

        let voted = try_vote_on_eb("node-0", &hash, 10, &config, 1.0, &mut rng, &tx).await;
        assert!(!voted);
        assert!(rx.try_recv().is_err());
    }
}
