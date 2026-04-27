//! Leios consensus layer.
//!
//! Tracks per-EB elections following the CIP-0164 Linear Leios pipeline model.
//! Each validated EB gets its own election with phases driven by slot ticks
//! and pipeline timing parameters (3×Δhdr + L_vote + L_diff). When an election
//! enters the Voting phase, committee selection determines whether this node
//! votes, and if so, a structured vote body is injected into the network.
//!
//! Submodules:
//! - `pipeline` — phase types, timing config, pure phase computation
//! - `voting` — EB-triggered vote production with committee selection
//! - `aggregation` — (future) vote tallies, quorum detection, certificates

mod aggregation;
mod pipeline;
pub(crate) mod voting;

use std::collections::HashMap;
use std::time::{Duration, Instant};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::Point;
use rand::rngs::StdRng;
use rand::SeedableRng;
use tokio::sync::{mpsc, watch};
use tracing::info;

use crate::config::DynamicConfig;
use crate::telemetry::NodeEvent;
use crate::validation::{LedgerCommand, Validator};

use pipeline::EbElection;
pub use pipeline::PipelineConfig;
use pipeline::PipelinePhase;
pub use voting::VotingConfig;

/// How long an in-flight Leios fetch entry remains active before being
/// considered stale. Matches the Praos in-flight TTL.
const IN_FLIGHT_TTL: Duration = Duration::from_secs(15);

pub struct LeiosConsensus {
    node_id: String,
    commands: mpsc::Sender<NetworkCommand>,
    validator: Validator,
    /// Leios points currently being fetched.
    in_flight: HashMap<Point, Instant>,
    /// Pipeline timing parameters.
    pipeline: PipelineConfig,
    /// Current slot (advanced by `on_slot`).
    current_slot: u64,
    /// Per-EB elections, keyed by EB hash.
    elections: HashMap<[u8; 32], EbElection>,
    /// Voting configuration (committee selection, stake, vote sizes).
    voting_config: VotingConfig,
    /// Fraction of total stake required for quorum (0.0–1.0).
    quorum_stake_fraction: f64,
    /// Total stake across all nodes in the network.
    total_stake: u64,
    /// RNG for committee selection sortition.
    rng: StdRng,
    /// Dynamic config for vote_generation_probability.
    dyn_config: watch::Receiver<DynamicConfig>,
    /// Telemetry events buffered for the caller to drain.
    pending_telemetry: Vec<NodeEvent>,
}

impl LeiosConsensus {
    pub fn new(
        node_id: String,
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
        pipeline: PipelineConfig,
        voting_config: VotingConfig,
        quorum_stake_fraction: f64,
        total_stake: u64,
        seed: Option<u64>,
        dyn_config: watch::Receiver<DynamicConfig>,
    ) -> Self {
        Self {
            node_id,
            commands,
            validator,
            in_flight: HashMap::new(),
            pipeline,
            current_slot: 0,
            elections: HashMap::new(),
            voting_config,
            quorum_stake_fraction,
            total_stake,
            rng: match seed {
                Some(s) => StdRng::seed_from_u64(s),
                None => StdRng::from_entropy(),
            },
            dyn_config,
            pending_telemetry: Vec::new(),
        }
    }

    /// Drain buffered telemetry events. Caller emits each via the telemetry sink.
    pub fn drain_telemetry(&mut self) -> Vec<NodeEvent> {
        std::mem::take(&mut self.pending_telemetry)
    }

    /// Slot of the earliest EB that's both at quorum and CertEligible.
    /// Used by the RB producer to populate `RbCertifiedEb` telemetry when
    /// the produced header carries `certified_eb=true`.
    pub fn certified_eb_slot(&self) -> Option<u64> {
        self.elections
            .values()
            .filter(|e| e.quorum_reached && e.phase == PipelinePhase::CertEligible)
            .map(|e| e.announced_slot)
            .min()
    }

    // -- Slot tick ----------------------------------------------------------

    /// Advance slot tracking. Updates pipeline phases, triggers voting
    /// for elections entering the Voting phase, and prunes expired ones.
    pub async fn on_slot(&mut self, slot: u64) {
        self.current_slot = slot;

        // Find elections that are in Voting phase and haven't been voted on.
        let to_vote: Vec<([u8; 32], u64)> = self
            .elections
            .iter()
            .filter(|(_, e)| {
                let elapsed = slot.saturating_sub(e.announced_slot);
                matches!(
                    self.pipeline.phase_for_elapsed(elapsed),
                    Some(PipelinePhase::Voting)
                ) && !e.voted
            })
            .map(|(hash, e)| (*hash, e.announced_slot))
            .collect();

        // Vote on each eligible EB.
        let vote_prob = self.dyn_config.borrow().vote_generation_probability;
        for (hash, eb_slot) in to_vote {
            if voting::try_vote_on_eb(
                &self.node_id,
                &hash,
                eb_slot,
                &self.voting_config,
                vote_prob,
                &mut self.rng,
                &self.commands,
            )
            .await
            {
                if let Some(election) = self.elections.get_mut(&hash) {
                    election.voted = true;
                }
            }
        }

        // Update phases and prune expired. Emit telemetry for each pruned election.
        let node_id = &self.node_id;
        let pending = &mut self.pending_telemetry;
        self.elections.retain(|_, election| {
            match self
                .pipeline
                .phase_for_elapsed(slot.saturating_sub(election.announced_slot))
            {
                Some(phase) => {
                    election.phase = phase;
                    true
                }
                None => {
                    pending.push(NodeEvent::LeiosElectionExpired {
                        node: node_id.clone(),
                        eb_slot: election.announced_slot,
                        had_quorum: election.quorum_reached,
                        voted_stake: election.voter_stakes.values().sum(),
                        voters: election.voter_stakes.len(),
                    });
                    false
                }
            }
        });
    }

    // -- Network event routing ----------------------------------------------

    /// Handle one Leios-shaped network event. Returns true if the event was
    /// consumed by this layer (caller should not log it separately).
    pub async fn handle_event(&mut self, event: &NetworkEvent) -> bool {
        self.evict_stale_in_flight();
        match event {
            NetworkEvent::LeiosBlockOffered { point } => {
                if !self.in_flight.contains_key(point) {
                    self.mark_in_flight(point.clone());
                    info!(node_id = %self.node_id, %point, "fetching leios block");
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchLeiosBlock {
                            point: point.clone(),
                        })
                        .await;
                }
                true
            }
            NetworkEvent::LeiosBlockTxsOffered { point } => {
                let key = Point::Specific {
                    slot: match point {
                        Point::Specific { slot, .. } => *slot,
                        _ => 0,
                    },
                    hash: [0xFE; 32],
                };
                if !self.in_flight.contains_key(&key) {
                    self.mark_in_flight(key);
                    info!(node_id = %self.node_id, %point, "fetching leios block txs");
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchLeiosBlockTxs {
                            point: point.clone(),
                            bitmap: std::collections::BTreeMap::new(),
                        })
                        .await;
                }
                true
            }
            NetworkEvent::LeiosVotesOffered { votes } => {
                if !votes.is_empty() {
                    info!(
                        node_id = %self.node_id,
                        count = votes.len(),
                        "fetching leios votes"
                    );
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchLeiosVotes {
                            votes: votes.clone(),
                        })
                        .await;
                }
                true
            }
            NetworkEvent::LeiosBlockReceived { point, .. } => {
                self.in_flight.remove(point);
                self.validator
                    .submit(LedgerCommand::ValidateEb {
                        point: point.clone(),
                    })
                    .await;
                true
            }
            NetworkEvent::LeiosVotesReceived {
                vote_ids,
                vote_data,
            } => {
                self.validator
                    .submit(LedgerCommand::ValidateVotes {
                        vote_ids: vote_ids.clone(),
                        vote_data: vote_data.clone(),
                    })
                    .await;
                true
            }
            NetworkEvent::LeiosBlockTxsReceived {
                point,
                transactions,
            } => {
                info!(
                    node_id = %self.node_id,
                    %point,
                    count = transactions.len(),
                    "leios block txs received"
                );
                true
            }
            _ => false,
        }
    }

    // -- Validation outcome handlers ----------------------------------------

    /// Called when EB validation completes. Creates a per-EB election
    /// with the appropriate pipeline phase based on elapsed time.
    pub fn on_validated_eb(&mut self, point: Point) {
        let (slot, hash) = match &point {
            Point::Specific { slot, hash } => (*slot, *hash),
            Point::Origin => return,
        };

        if self.elections.contains_key(&hash) {
            return;
        }

        let elapsed = self.current_slot.saturating_sub(slot);
        if let Some(phase) = self.pipeline.phase_for_elapsed(elapsed) {
            info!(
                node_id = %self.node_id,
                %point,
                ?phase,
                "eb election created"
            );
            self.elections.insert(
                hash,
                EbElection {
                    eb_point: point,
                    announced_slot: slot,
                    phase,
                    validated_at: Instant::now(),
                    voted: false,
                    voter_stakes: HashMap::new(),
                    quorum_reached: false,
                },
            );
        }
    }

    /// Called when vote validation completes. Attributes each vote to
    /// its EB election and checks for quorum.
    pub fn on_validated_votes(&mut self, vote_data: &[Vec<u8>]) {
        for blob in vote_data {
            if let Some(body) = crate::production::VoteBody::decode(blob) {
                if let Some(formed) = aggregation::record_vote(
                    &mut self.elections,
                    &body.endorser_block_hash,
                    body.voter_id.clone(),
                    body.voter_stake,
                    self.quorum_stake_fraction,
                    self.total_stake,
                    &self.node_id,
                ) {
                    self.pending_telemetry.push(NodeEvent::LeiosQuorumReached {
                        node: self.node_id.clone(),
                        eb_slot: formed.eb_slot,
                        voted_stake: formed.voted_stake,
                        voters: formed.voters,
                    });
                }
            }
        }
    }

    // -- Queries ------------------------------------------------------------

    /// Returns true if any EB election has reached quorum and is in
    /// CertEligible phase (full pipeline elapsed). Used by the RB
    /// producer to set the certified_eb header flag.
    pub fn has_certified_eb(&self) -> bool {
        self.elections
            .values()
            .any(|e| e.quorum_reached && e.phase == PipelinePhase::CertEligible)
    }

    #[cfg(test)]
    fn election_phase(&self, hash: &[u8; 32]) -> Option<PipelinePhase> {
        self.elections.get(hash).map(|e| e.phase)
    }

    #[cfg(test)]
    fn election_count(&self) -> usize {
        self.elections.len()
    }

    #[cfg(test)]
    fn election_voted(&self, hash: &[u8; 32]) -> bool {
        self.elections.get(hash).map(|e| e.voted).unwrap_or(false)
    }

    #[cfg(test)]
    fn election_quorum(&self, hash: &[u8; 32]) -> bool {
        self.elections
            .get(hash)
            .map(|e| e.quorum_reached)
            .unwrap_or(false)
    }

    #[cfg(test)]
    fn election_voter_count(&self, hash: &[u8; 32]) -> usize {
        self.elections
            .get(hash)
            .map(|e| e.voter_stakes.len())
            .unwrap_or(0)
    }

    // -- Housekeeping -------------------------------------------------------

    fn mark_in_flight(&mut self, point: Point) {
        self.in_flight.insert(point, Instant::now());
    }

    fn evict_stale_in_flight(&mut self) {
        let now = Instant::now();
        self.in_flight
            .retain(|_, started| now.duration_since(*started) < IN_FLIGHT_TTL);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::CommitteeSelection;

    fn point(slot: u64) -> Point {
        Point::Specific {
            slot,
            hash: [slot as u8; 32],
        }
    }

    fn point_hash(slot: u64) -> [u8; 32] {
        [slot as u8; 32]
    }

    fn test_dyn_config() -> watch::Receiver<DynamicConfig> {
        let config = DynamicConfig {
            rb_generation_probability: 0.0,
            eb_generation_probability: 0.0,
            vote_generation_probability: 1.0, // always vote in tests
            rb_head_validation_ms: 0.0,
            rb_body_validation_ms_constant: 0.0,
            rb_body_validation_ms_per_byte: 0.0,
            eb_validation_ms: 0.0,
            vote_validation_ms: 0.0,
            tx_rate: 0.0,
        };
        watch::channel(config).1
    }

    fn test_validator() -> (Validator, mpsc::Receiver<crate::validation::LedgerOutcome>) {
        Validator::new(test_dyn_config())
    }

    /// Pipeline config: delta_hdr=1, vote=5, diffuse=5, dedup=10
    fn test_pipeline() -> PipelineConfig {
        PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        }
    }

    fn test_voting_config() -> VotingConfig {
        VotingConfig {
            committee_selection: CommitteeSelection::EveryoneVotes,
            stake: 100,
            total_stake: 1000,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
        }
    }

    fn test_leios(commands: mpsc::Sender<NetworkCommand>, validator: Validator) -> LeiosConsensus {
        LeiosConsensus::new(
            "test".into(),
            commands,
            validator,
            test_pipeline(),
            test_voting_config(),
            0.75, // quorum_stake_fraction
            1000, // total_stake
            Some(42),
            test_dyn_config(),
        )
    }

    // -- Election lifecycle tests -------------------------------------------

    #[tokio::test]
    async fn eb_creates_election() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(10).await;
        leios.on_validated_eb(point(10));
        assert_eq!(leios.election_count(), 1);
        assert_eq!(
            leios.election_phase(&point_hash(10)),
            Some(PipelinePhase::EquivocationCheck)
        );
    }

    #[tokio::test]
    async fn election_advances_to_voting() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(10).await;
        leios.on_validated_eb(point(10));
        leios.on_slot(13).await;
        assert_eq!(
            leios.election_phase(&point_hash(10)),
            Some(PipelinePhase::Voting)
        );
    }

    #[tokio::test]
    async fn election_advances_through_all_phases() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::EquivocationCheck)
        );

        leios.on_slot(3).await;
        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::Voting)
        );

        leios.on_slot(8).await;
        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::Diffusing)
        );

        leios.on_slot(13).await;
        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::CertEligible)
        );

        leios.on_slot(23).await;
        assert_eq!(leios.election_phase(&point_hash(0)), None);
        assert_eq!(leios.election_count(), 0);
    }

    #[tokio::test]
    async fn duplicate_eb_deduped() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(10).await;
        leios.on_validated_eb(point(10));
        leios.on_validated_eb(point(10));
        assert_eq!(leios.election_count(), 1);
    }

    #[tokio::test]
    async fn old_election_pruned() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));
        assert_eq!(leios.election_count(), 1);

        leios.on_slot(23).await;
        assert_eq!(leios.election_count(), 0);
    }

    #[tokio::test]
    async fn multiple_ebs_concurrent() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(5).await;
        leios.on_validated_eb(point(0));
        leios.on_validated_eb(point(5));

        assert_eq!(leios.election_count(), 2);
        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::Voting)
        );
        assert_eq!(
            leios.election_phase(&point_hash(5)),
            Some(PipelinePhase::EquivocationCheck)
        );
    }

    #[tokio::test]
    async fn eb_arriving_late_starts_in_correct_phase() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(10).await;
        leios.on_validated_eb(point(0));
        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::Diffusing)
        );
    }

    #[tokio::test]
    async fn expired_eb_not_tracked() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(30).await;
        leios.on_validated_eb(point(0));
        assert_eq!(leios.election_count(), 0);
    }

    // -- Voting tests -------------------------------------------------------

    #[tokio::test]
    async fn on_slot_triggers_vote_when_entering_voting_phase() {
        let (tx, mut rx) = mpsc::channel(16);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));
        // No vote yet — still in EquivocationCheck.
        assert!(!leios.election_voted(&point_hash(0)));

        // Advance to Voting phase (elapsed=3).
        leios.on_slot(3).await;
        assert!(leios.election_voted(&point_hash(0)));

        // Check that InjectLeiosVotes was sent.
        match rx.try_recv() {
            Ok(NetworkCommand::InjectLeiosVotes { votes, data }) => {
                assert_eq!(votes.len(), 1);
                assert!(!data.is_empty());
            }
            other => panic!("expected InjectLeiosVotes, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn no_double_vote_same_eb() {
        let (tx, mut rx) = mpsc::channel(16);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        // First slot in Voting → vote produced.
        leios.on_slot(3).await;
        assert!(rx.try_recv().is_ok());

        // Second slot in Voting → no duplicate vote.
        leios.on_slot(4).await;
        assert!(rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn no_vote_during_equivocation_check() {
        let (tx, mut rx) = mpsc::channel(16);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        // Still in EquivocationCheck (elapsed=2).
        leios.on_slot(2).await;
        assert!(!leios.election_voted(&point_hash(0)));
        assert!(rx.try_recv().is_err());
    }

    // -- Network event tests ------------------------------------------------

    #[tokio::test]
    async fn block_offered_issues_fetch() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _outcome_rx) = test_validator();
        let mut leios = test_leios(tx, validator);

        let p = point(100);
        assert!(
            leios
                .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
                .await
        );

        match rx.try_recv() {
            Ok(NetworkCommand::FetchLeiosBlock { point: got }) => assert_eq!(got, p),
            other => panic!("expected FetchLeiosBlock, got {:?}", other),
        }
    }

    #[tokio::test]
    async fn duplicate_block_offer_dedup() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _outcome_rx) = test_validator();
        let mut leios = test_leios(tx, validator);

        let p = point(100);
        leios
            .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
            .await;

        assert!(matches!(
            rx.try_recv(),
            Ok(NetworkCommand::FetchLeiosBlock { .. })
        ));
        assert!(rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn received_clears_in_flight() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _outcome_rx) = test_validator();
        let mut leios = test_leios(tx, validator);

        let p = point(200);
        leios
            .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: p.clone(),
                block: vec![],
            })
            .await;
        assert!(!leios.in_flight.contains_key(&p));
    }

    #[tokio::test]
    async fn non_leios_event_not_consumed() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _outcome_rx) = test_validator();
        let mut leios = test_leios(tx, validator);

        let consumed = leios
            .handle_event(&NetworkEvent::PeerDisconnected {
                peer_id: net_core::peer::PeerId(0),
                reason: String::new(),
            })
            .await;
        assert!(!consumed);
    }

    #[tokio::test]
    async fn block_received_triggers_eb_validation() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, mut outcome_rx) = test_validator();
        let mut leios = test_leios(tx, validator);

        let p = point(99);
        leios
            .handle_event(&NetworkEvent::LeiosBlockOffered { point: p.clone() })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: p.clone(),
                block: vec![],
            })
            .await;

        match outcome_rx.recv().await.expect("outcome") {
            crate::validation::LedgerOutcome::EbValidated { point: got } => {
                assert_eq!(got, p);
            }
            other => panic!("expected EbValidated, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn votes_received_triggers_vote_validation() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, mut outcome_rx) = test_validator();
        let mut leios = test_leios(tx, validator);

        let vote_ids = vec![(10u64, vec![0xAAu8])];
        leios
            .handle_event(&NetworkEvent::LeiosVotesReceived {
                vote_ids: vote_ids.clone(),
                vote_data: vec![vec![0x01]],
            })
            .await;

        match outcome_rx.recv().await.expect("outcome") {
            crate::validation::LedgerOutcome::VotesValidated { vote_ids: got, .. } => {
                assert_eq!(got, vote_ids);
            }
            other => panic!("expected VotesValidated, got {other:?}"),
        }
    }

    // -- Vote aggregation tests ---------------------------------------------

    #[tokio::test]
    async fn votes_attributed_to_eb_election() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        // Create an election for EB at slot 0.
        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        // Build a vote body referencing that EB's hash.
        let eb_hash = point_hash(0);
        let body = crate::production::VoteBody::stub_persistent(0, b"voter-1", 100, &eb_hash);
        let encoded = body.encode(130);

        leios.on_validated_votes(&[encoded]);
        assert_eq!(leios.election_voter_count(&eb_hash), 1);
        assert!(!leios.election_quorum(&eb_hash));
    }

    #[tokio::test]
    async fn quorum_reached_after_enough_stake() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        // total_stake=1000, quorum=0.75 → threshold=750
        let eb_hash = point_hash(0);
        let body1 = crate::production::VoteBody::stub_persistent(0, &[1], 400, &eb_hash);
        let body2 = crate::production::VoteBody::stub_persistent(0, &[2], 350, &eb_hash);
        leios.on_validated_votes(&[body1.encode(130), body2.encode(130)]);

        assert_eq!(leios.election_voter_count(&eb_hash), 2);
        assert!(leios.election_quorum(&eb_hash));
    }

    #[tokio::test]
    async fn quorum_emits_cert_formed_telemetry() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        let eb_hash = point_hash(0);
        let body1 = crate::production::VoteBody::stub_persistent(0, &[1], 400, &eb_hash);
        let body2 = crate::production::VoteBody::stub_persistent(0, &[2], 350, &eb_hash);
        leios.on_validated_votes(&[body1.encode(130), body2.encode(130)]);

        let drained = leios.drain_telemetry();
        let cert = drained
            .iter()
            .find(|e| matches!(e, NodeEvent::LeiosQuorumReached { .. }))
            .expect("LeiosQuorumReached emitted");
        if let NodeEvent::LeiosQuorumReached {
            eb_slot,
            voted_stake,
            voters,
            ..
        } = cert
        {
            assert_eq!(*eb_slot, 0);
            assert_eq!(*voted_stake, 750);
            assert_eq!(*voters, 2);
        }

        // Second call doesn't re-emit.
        let body3 = crate::production::VoteBody::stub_persistent(0, &[3], 100, &eb_hash);
        leios.on_validated_votes(&[body3.encode(130)]);
        let drained2 = leios.drain_telemetry();
        assert!(!drained2
            .iter()
            .any(|e| matches!(e, NodeEvent::LeiosQuorumReached { .. })));
    }

    #[tokio::test]
    async fn pruned_election_emits_expired_telemetry() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));
        let _ = leios.drain_telemetry(); // discard creation-side events

        // Advance past expiry (dedup_window=10, full pipeline=23).
        leios.on_slot(23).await;

        let drained = leios.drain_telemetry();
        let expired = drained
            .iter()
            .find(|e| matches!(e, NodeEvent::LeiosElectionExpired { .. }))
            .expect("LeiosElectionExpired emitted");
        if let NodeEvent::LeiosElectionExpired {
            eb_slot,
            had_quorum,
            voters,
            ..
        } = expired
        {
            assert_eq!(*eb_slot, 0);
            assert!(!*had_quorum);
            assert_eq!(*voters, 0);
        }
    }

    #[tokio::test]
    async fn certified_eb_slot_returns_min_quorum_election() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        // Two EBs at different slots, both reaching quorum.
        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));
        leios.on_slot(5).await;
        leios.on_validated_eb(point(5));

        let body_a1 = crate::production::VoteBody::stub_persistent(0, &[1], 400, &point_hash(0));
        let body_a2 = crate::production::VoteBody::stub_persistent(0, &[2], 350, &point_hash(0));
        let body_b1 = crate::production::VoteBody::stub_persistent(5, &[1], 400, &point_hash(5));
        let body_b2 = crate::production::VoteBody::stub_persistent(5, &[2], 350, &point_hash(5));
        leios.on_validated_votes(&[
            body_a1.encode(130),
            body_a2.encode(130),
            body_b1.encode(130),
            body_b2.encode(130),
        ]);

        // Neither is CertEligible yet.
        assert_eq!(leios.certified_eb_slot(), None);

        // Advance to make EB at slot 0 CertEligible (elapsed=13 from slot 0).
        leios.on_slot(13).await;
        assert_eq!(leios.certified_eb_slot(), Some(0));

        // Advance further; both eligible — earliest wins.
        leios.on_slot(18).await;
        assert_eq!(leios.certified_eb_slot(), Some(0));
    }

    #[tokio::test]
    async fn duplicate_voter_not_counted() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        let eb_hash = point_hash(0);
        let body = crate::production::VoteBody::stub_persistent(0, b"same-voter", 500, &eb_hash);
        let encoded = body.encode(130);

        leios.on_validated_votes(&[encoded.clone()]);
        leios.on_validated_votes(&[encoded]);
        assert_eq!(leios.election_voter_count(&eb_hash), 1);
    }
}
