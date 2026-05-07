//! Leios consensus layer — thin I/O wrapper around `con_rs::leios::LeiosState`.
//!
//! Public methods take wire-format args (`NetworkEvent`, `LedgerOutcome`,
//! `BlockBody`/`WrappedHeader` indirectly via the production wire codec),
//! translate to logical args, run the state machine, and dispatch the
//! returned `Vec<LeiosEffect>` to the network-command channel and
//! validator actor.  Vote-body construction lives here too: the state
//! machine emits `EmitVote` carrying logical args (PV flag, NPV
//! eligibility signature) and this layer encodes the wire-format body.

use std::collections::BTreeMap;
use std::time::Instant;

use con_rs::elections::{Elections, ElectionsConfig};
use con_rs::leios::{
    ChainTipContext, LeiosEffect, LeiosState, LeiosTelemetryEvent, ValidatedVote, VotingConfig,
};
pub use con_rs::leios::EbTxMatchOutcome;
#[cfg(test)]
use con_rs::pipeline::PipelinePhase;
pub use con_rs::pipeline::PipelineConfig;
use con_rs::wfa;
use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::Point;
use rand::rngs::StdRng;
use rand::SeedableRng;
use tokio::sync::{mpsc, watch};
use tracing::info;

use crate::config::{CommitteeSelection, DynamicConfig, StakeEntry};
use crate::production::{decode_overflow_eb, VoteBody};
use crate::telemetry::NodeEvent;
use crate::validation::{LedgerCommand, Validator};

pub struct LeiosConsensus {
    pub(crate) state: LeiosState,
    commands: mpsc::Sender<NetworkCommand>,
    validator: Validator,
    /// Local mempool. Used to compute the bitmap of missing txs when a
    /// peer announces an EB's transactions.
    mempool: crate::mempool::SharedMempool,
    /// RNG reserved for future randomization (currently unused: PV is
    /// deterministic from the cached committee, NPV from the signature).
    #[allow(dead_code)]
    rng: StdRng,
    /// Dynamic config (currently unused; reserved for future hot-reload).
    #[allow(dead_code)]
    dyn_config: watch::Receiver<DynamicConfig>,
    /// Telemetry events buffered for the caller to drain.
    pending_telemetry: Vec<NodeEvent>,
}

impl LeiosConsensus {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        node_id: String,
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
        mempool: crate::mempool::SharedMempool,
        pipeline: PipelineConfig,
        committee_selection: CommitteeSelection,
        stake: u64,
        stake_registry_entries: &[StakeEntry],
        persistent_vote_bytes: usize,
        non_persistent_vote_bytes: usize,
        quorum_weight_fraction: f64,
        committee_seed: u64,
        rng_seed: Option<u64>,
        dyn_config: watch::Receiver<DynamicConfig>,
    ) -> Self {
        let total_stake: u64 = stake_registry_entries.iter().map(|e| e.stake).sum();
        let persistent_committee =
            wfa::build_committee(&committee_selection, stake_registry_entries, committee_seed);
        let expected_committee_size =
            wfa::expected_committee_size(&committee_selection, &persistent_committee);
        let persistent_seats = persistent_committee.get(&node_id).copied().unwrap_or(0);
        let stake_registry: BTreeMap<String, u64> = stake_registry_entries
            .iter()
            .map(|e| (e.node_id.clone(), e.stake))
            .collect();
        let voting_config = VotingConfig {
            committee_selection: committee_selection.clone(),
            stake,
            total_stake,
            persistent_vote_bytes,
            non_persistent_vote_bytes,
            persistent_seats,
        };
        info!(
            node_id = %node_id,
            persistent_seats,
            expected_committee_size,
            committee_pools = persistent_committee.len(),
            "leios committee initialized"
        );
        let elections = Elections::new(ElectionsConfig {
            node_id: node_id.clone(),
            pipeline,
            committee_selection,
            persistent_committee,
            stake_registry,
            total_stake,
            expected_committee_size,
            quorum_weight_fraction,
        });
        let state = LeiosState::new(node_id, elections, voting_config, pipeline);
        Self {
            state,
            commands,
            validator,
            mempool,
            rng: match rng_seed {
                Some(s) => StdRng::seed_from_u64(s),
                None => StdRng::from_entropy(),
            },
            dyn_config,
            pending_telemetry: Vec::new(),
        }
    }

    /// Drain buffered telemetry events.
    pub fn drain_telemetry(&mut self) -> Vec<NodeEvent> {
        std::mem::take(&mut self.pending_telemetry)
    }

    /// Slot of the earliest EB that's both at quorum and CertEligible.
    /// Used by the RB producer to populate `RbCertifiedEb` telemetry.
    pub fn certified_eb_slot(&self) -> Option<u64> {
        self.state.certified_eb_slot()
    }

    /// Whether any EB has a valid certificate.
    pub fn has_certified_eb(&self) -> bool {
        self.state.has_certified_eb()
    }

    /// Update the adopted-chain-tip metadata used by the CIP-0164
    /// voting predicates (`LateRBHeader`, `WrongEB`).  The Praos
    /// adapter calls this whenever a new RB is adopted as the chain
    /// tip — passing the slot at which the RB header arrived locally
    /// and the EB hash (if any) the header announces.
    pub fn set_chain_tip_context(&mut self, ctx: ChainTipContext) {
        self.state.set_chain_tip_context(ctx);
    }

    /// Advance slot tracking, drive elections, dispatch any effects.
    pub async fn on_slot(&mut self, slot: u64) {
        // Snapshot the mempool's tx-id set so the predicate-checking
        // path inside `LeiosState::on_slot` can answer "is this EB's
        // referenced TX known locally?" for the CIP-0164 MissingTX
        // check without holding the mempool lock across the call.
        let known = self.mempool.lock().unwrap().current_tx_ids();
        let tx_known = |h: &[u8; 32]| known.contains(h.as_slice());
        let fx = self.state.on_slot(slot, &tx_known);
        self.dispatch(fx).await;
    }

    /// Handle a Leios-shaped network event.
    pub async fn handle_event(&mut self, event: &NetworkEvent) -> bool {
        let now = Instant::now();
        let (consumed, fx): (bool, Vec<LeiosEffect>) = match event {
            NetworkEvent::LeiosBlockOffered { peer_id, point } => (
                true,
                self.state.on_eb_offered(point.clone(), *peer_id, now),
            ),
            NetworkEvent::LeiosBlockTxsOffered { peer_id, point } => {
                let bitmap = self.bitmap_for_missing_txs(point);
                (
                    true,
                    self.state
                        .on_eb_txs_offered(point.clone(), *peer_id, bitmap, now),
                )
            }
            NetworkEvent::LeiosVotesOffered { peer_id, votes } => (
                true,
                self.state.on_votes_offered(*peer_id, votes.clone()),
            ),
            NetworkEvent::LeiosBlockReceived { point, block } => {
                let manifest = decode_overflow_eb(block).map(|(_, hashes)| hashes);
                (true, self.state.on_eb_received(point.clone(), manifest))
            }
            NetworkEvent::LeiosVotesReceived {
                vote_ids,
                vote_data,
            } => (
                true,
                self.state.on_votes_received(vote_ids.clone(), vote_data.clone()),
            ),
            NetworkEvent::LeiosBlockTxsReceived {
                point,
                transactions,
            } => {
                self.state.on_eb_txs_received(point, transactions.len());
                (true, Vec::new())
            }
            _ => (false, Vec::new()),
        };
        self.dispatch(fx).await;
        consumed
    }

    /// EB validation completed; create an election.
    pub fn on_validated_eb(&mut self, point: Point) {
        self.state.on_validated_eb(point);
    }

    /// Vote validation completed; record each vote, fire quorum
    /// telemetry if quorum forms.
    pub fn on_validated_votes(&mut self, vote_data: &[Vec<u8>]) {
        // Decode wire-format vote bodies up front so we can lend them
        // to the state machine as borrowed `ValidatedVote` views.
        let decoded: Vec<VoteBody> = vote_data
            .iter()
            .filter_map(|b| VoteBody::decode(b))
            .collect();
        let bodies: Vec<ValidatedVote> = decoded
            .iter()
            .map(|body| ValidatedVote {
                voter_id: &body.voter_id,
                tag: body.tag,
                eligibility_signature: body.eligibility_signature.as_deref(),
                endorser_block_hash: &body.endorser_block_hash,
            })
            .collect();
        let fx = self.state.on_validated_votes(bodies);
        // Only telemetry effects come out of this path; fold them into
        // the pending buffer inline so the caller can stay sync.
        for eff in fx {
            if let LeiosEffect::EmitTelemetry(LeiosTelemetryEvent::QuorumReached {
                eb_slot,
                voted_weight,
                voters,
            }) = eff
            {
                self.pending_telemetry.push(NodeEvent::LeiosQuorumReached {
                    node: self.state.node_id.clone(),
                    eb_slot,
                    voted_weight,
                    voters,
                });
            }
        }
    }

    /// Verify a `LeiosBlockTxsReceived` response against the cached
    /// manifest.  Bodies are blake2b-hashed here (the wire-format body
    /// hash) before being matched, since con-rs is format-agnostic.
    pub fn match_eb_tx_response(
        &mut self,
        point: &Point,
        bodies: &[Vec<u8>],
    ) -> EbTxMatchOutcome {
        let bodies_with_hashes: Vec<(Vec<u8>, [u8; 32])> = bodies
            .iter()
            .map(|body| {
                let h = blake2b_simd::Params::new().hash_length(32).hash(body);
                let mut hash = [0u8; 32];
                hash.copy_from_slice(h.as_bytes());
                (body.clone(), hash)
            })
            .collect();
        self.state.match_eb_tx_response(point, &bodies_with_hashes)
    }

    /// Re-issue a `FetchLeiosBlockTxs` for the still-missing indices.
    pub async fn retry_eb_tx_fetch(&mut self, point: Point, bitmap: BTreeMap<u16, u64>) {
        let fx = self.state.retry_eb_tx_fetch(point, bitmap);
        self.dispatch(fx).await;
    }

    // -- Helpers ------------------------------------------------------------

    /// Build the sparse bitmap of transactions we don't already have
    /// for an EB-tx offer.  If the manifest isn't cached yet, fall back
    /// to selecting all indices so the request is still useful.
    fn bitmap_for_missing_txs(&self, point: &Point) -> BTreeMap<u16, u64> {
        use net_core::protocols::leios_fetch::bitmap;
        let hash = match point {
            Point::Specific { hash, .. } => hash,
            Point::Origin => return BTreeMap::new(),
        };
        let Some((_, tx_hashes)) = self.state.eb_tx_hashes.get(hash) else {
            let max_txs =
                (net_core::protocols::leios_fetch::MAX_BITMAP_ENTRIES as u32).saturating_mul(64);
            return bitmap::select_all(max_txs);
        };
        let have = self.mempool.lock().unwrap().current_tx_ids();
        let missing: Vec<u32> = tx_hashes
            .iter()
            .enumerate()
            .filter_map(|(i, h)| {
                if have.contains(h.as_slice()) {
                    None
                } else {
                    Some(i as u32)
                }
            })
            .collect();
        bitmap::from_indices(&missing)
    }

    async fn dispatch(&mut self, fx: Vec<LeiosEffect>) {
        for eff in fx {
            match eff {
                LeiosEffect::FetchLeiosBlock { point, peers } => {
                    for peer_id in peers {
                        let _ = self
                            .commands
                            .send(NetworkCommand::FetchLeiosBlock {
                                peer_id,
                                point: point.clone(),
                            })
                            .await;
                    }
                }
                LeiosEffect::FetchLeiosBlockTxs {
                    point,
                    bitmap,
                    peers,
                } => {
                    for peer_id in peers {
                        let _ = self
                            .commands
                            .send(NetworkCommand::FetchLeiosBlockTxs {
                                peer_id,
                                point: point.clone(),
                                bitmap: bitmap.clone(),
                            })
                            .await;
                    }
                }
                LeiosEffect::FetchLeiosVotes { per_peer } => {
                    for (peer_id, votes) in per_peer {
                        let _ = self
                            .commands
                            .send(NetworkCommand::FetchLeiosVotes { peer_id, votes })
                            .await;
                    }
                }
                LeiosEffect::RecordLeiosEbManifest { point, tx_hashes } => {
                    let _ = self
                        .commands
                        .send(NetworkCommand::RecordLeiosEbManifest { point, tx_hashes })
                        .await;
                }
                LeiosEffect::EmitVote {
                    eb_slot,
                    eb_hash,
                    emit_pv,
                    npv_signature,
                } => {
                    self.emit_vote(eb_slot, eb_hash, emit_pv, npv_signature)
                        .await;
                }
                LeiosEffect::NoVote {
                    eb_slot, reason, ..
                } => {
                    self.pending_telemetry.push(NodeEvent::LeiosNoVote {
                        node: self.state.node_id.clone(),
                        eb_slot,
                        reason: format!("{reason:?}"),
                    });
                }
                LeiosEffect::ValidateEb { point } => {
                    self.validator
                        .submit(LedgerCommand::ValidateEb { point })
                        .await;
                }
                LeiosEffect::ValidateVotes {
                    vote_ids,
                    vote_data,
                } => {
                    self.validator
                        .submit(LedgerCommand::ValidateVotes {
                            vote_ids,
                            vote_data,
                        })
                        .await;
                }
                LeiosEffect::EmitTelemetry(event) => {
                    let node_id = self.state.node_id.clone();
                    let node_event = match event {
                        LeiosTelemetryEvent::QuorumReached {
                            eb_slot,
                            voted_weight,
                            voters,
                        } => NodeEvent::LeiosQuorumReached {
                            node: node_id,
                            eb_slot,
                            voted_weight,
                            voters,
                        },
                        LeiosTelemetryEvent::ElectionExpired {
                            eb_slot,
                            had_quorum,
                            voted_weight,
                            voters,
                        } => NodeEvent::LeiosElectionExpired {
                            node: node_id,
                            eb_slot,
                            had_quorum,
                            voted_weight,
                            voters,
                        },
                    };
                    self.pending_telemetry.push(node_event);
                }
            }
        }
    }

    /// Build and inject the vote bodies for an EB.  Encodes the
    /// wire-format vote body — con-rs handed us the logical args.
    async fn emit_vote(
        &mut self,
        eb_slot: u64,
        eb_hash: [u8; 32],
        emit_pv: bool,
        npv_signature: Option<Vec<u8>>,
    ) {
        let voter_id = self.state.node_id.as_bytes().to_vec();
        let stake = self.state.voting_config.stake;
        let pv_size = self.state.voting_config.persistent_vote_bytes;
        let npv_size = self.state.voting_config.non_persistent_vote_bytes;
        let pv_seats = self.state.voting_config.persistent_seats;
        let mut votes = Vec::new();
        let mut data = Vec::new();
        if emit_pv {
            let body = VoteBody::stub_persistent(eb_slot, &voter_id, stake, &eb_hash);
            let encoded = body.encode(pv_size);
            info!(
                node_id = %self.state.node_id,
                eb_slot, tag = body.tag, pv_seats, size = encoded.len(),
                "vote produced for eb"
            );
            let mut id = voter_id.clone();
            id.push(0);
            votes.push((eb_slot, id));
            data.push(encoded);
        }
        if let Some(sig) = npv_signature {
            let body =
                VoteBody::stub_non_persistent(eb_slot, &voter_id, stake, sig, &eb_hash);
            let encoded = body.encode(npv_size);
            info!(
                node_id = %self.state.node_id,
                eb_slot, tag = body.tag, pv_seats, size = encoded.len(),
                "vote produced for eb"
            );
            let mut id = voter_id.clone();
            id.push(1);
            votes.push((eb_slot, id));
            data.push(encoded);
        }
        if !votes.is_empty() {
            let _ = self
                .commands
                .send(NetworkCommand::InjectLeiosVotes { votes, data })
                .await;
        }
    }

    // -- Test helpers (delegate through state) -----------------------------

    #[cfg(test)]
    fn election_phase(&self, hash: &[u8; 32]) -> Option<PipelinePhase> {
        self.state.elections.phase(hash)
    }

    #[cfg(test)]
    fn election_count(&self) -> usize {
        self.state.elections.count()
    }

    #[cfg(test)]
    fn election_voted(&self, hash: &[u8; 32]) -> bool {
        self.state.elections.voted(hash)
    }

    #[cfg(test)]
    fn election_quorum(&self, hash: &[u8; 32]) -> bool {
        self.state.elections.quorum(hash)
    }

    #[cfg(test)]
    fn election_voter_count(&self, hash: &[u8; 32]) -> usize {
        self.state.elections.voter_count(hash)
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

    fn test_registry() -> Vec<StakeEntry> {
        // "test" + 9 peers, each 100 stake → total 1000. EveryoneVotes
        // mode gives each pool 1 PV seat.
        let mut entries = vec![StakeEntry {
            node_id: "test".to_string(),
            stake: 100,
        }];
        entries.extend((0..9).map(|i| StakeEntry {
            node_id: format!("peer-{i}"),
            stake: 100,
        }));
        entries
    }

    fn test_leios(commands: mpsc::Sender<NetworkCommand>, validator: Validator) -> LeiosConsensus {
        test_leios_with_mempool(commands, validator, crate::mempool::new_mempool(1000))
    }

    fn test_leios_with_mempool(
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
        mempool: crate::mempool::SharedMempool,
    ) -> LeiosConsensus {
        let registry = test_registry();
        LeiosConsensus::new(
            "test".into(),
            commands,
            validator,
            mempool,
            test_pipeline(),
            CommitteeSelection::EveryoneVotes,
            100, // own stake
            &registry,
            130,      // persistent_vote_bytes
            180,      // non_persistent_vote_bytes
            0.75,     // quorum_weight_fraction
            42,       // committee_seed
            Some(42), // rng_seed
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
        // Make the chain-tip context match the EB so the CIP-0164
        // predicates (LateRBHeader, WrongEB) accept this vote.
        leios.set_chain_tip_context(ChainTipContext {
            rb_header_arrival_slot: Some(0),
            eb_announcement: Some(point_hash(0)),
        });
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
        leios.set_chain_tip_context(ChainTipContext {
            rb_header_arrival_slot: Some(0),
            eb_announcement: Some(point_hash(0)),
        });

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
                .handle_event(&NetworkEvent::LeiosBlockOffered {
                peer_id: net_core::peer::PeerId(1),
                point: p.clone(),
            })
                .await
        );

        match rx.try_recv() {
            Ok(NetworkCommand::FetchLeiosBlock { point: got, .. }) => assert_eq!(got, p),
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
            .handle_event(&NetworkEvent::LeiosBlockOffered {
                peer_id: net_core::peer::PeerId(1),
                point: p.clone(),
            })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockOffered {
                peer_id: net_core::peer::PeerId(1),
                point: p.clone(),
            })
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
            .handle_event(&NetworkEvent::LeiosBlockOffered {
                peer_id: net_core::peer::PeerId(1),
                point: p.clone(),
            })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: p.clone(),
                block: vec![],
            })
            .await;
        assert!(!leios.state.in_flight.contains_key(&p));
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
            .handle_event(&NetworkEvent::LeiosBlockOffered {
                peer_id: net_core::peer::PeerId(1),
                point: p.clone(),
            })
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
    //
    // Under EveryoneVotes (test_leios mode) every registered pool has 1
    // PV seat, so each PV vote contributes weight 1. The 10-pool test
    // registry yields expected_committee_size=10; quorum at 0.75 needs
    // ≥7 distinct voters. Voter ids in tests must match registry node_ids
    // ("test", "peer-0".."peer-8") for the PV-lookup weight to be 1.

    #[tokio::test]
    async fn votes_attributed_to_eb_election() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        let eb_hash = point_hash(0);
        let body = crate::production::VoteBody::stub_persistent(0, b"peer-0", 100, &eb_hash);
        leios.on_validated_votes(&[body.encode(130)]);
        assert_eq!(leios.election_voter_count(&eb_hash), 1);
        assert!(!leios.election_quorum(&eb_hash));
    }

    #[tokio::test]
    async fn quorum_reached_after_enough_voters() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        // expected_committee_size=10 (10 pools × 1 PV seat each), quorum
        // at 0.75 → 7 distinct voters needed.
        let eb_hash = point_hash(0);
        let voters = [
            "test", "peer-0", "peer-1", "peer-2", "peer-3", "peer-4", "peer-5",
        ];
        let bodies: Vec<Vec<u8>> = voters
            .iter()
            .map(|v| {
                crate::production::VoteBody::stub_persistent(0, v.as_bytes(), 100, &eb_hash)
                    .encode(130)
            })
            .collect();
        leios.on_validated_votes(&bodies);

        assert_eq!(leios.election_voter_count(&eb_hash), 7);
        assert!(leios.election_quorum(&eb_hash));
    }

    #[tokio::test]
    async fn quorum_emits_cert_formed_telemetry() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));
        let _ = leios.drain_telemetry();

        let eb_hash = point_hash(0);
        let voters = [
            "test", "peer-0", "peer-1", "peer-2", "peer-3", "peer-4", "peer-5",
        ];
        let bodies: Vec<Vec<u8>> = voters
            .iter()
            .map(|v| {
                crate::production::VoteBody::stub_persistent(0, v.as_bytes(), 100, &eb_hash)
                    .encode(130)
            })
            .collect();
        leios.on_validated_votes(&bodies);

        let drained = leios.drain_telemetry();
        let cert = drained
            .iter()
            .find(|e| matches!(e, NodeEvent::LeiosQuorumReached { .. }))
            .expect("LeiosQuorumReached emitted");
        if let NodeEvent::LeiosQuorumReached {
            eb_slot,
            voted_weight,
            voters,
            ..
        } = cert
        {
            assert_eq!(*eb_slot, 0);
            assert_eq!(*voted_weight, 7);
            assert_eq!(*voters, 7);
        }

        // Subsequent votes don't re-fire.
        let body8 = crate::production::VoteBody::stub_persistent(0, b"peer-6", 100, &eb_hash);
        leios.on_validated_votes(&[body8.encode(130)]);
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
    async fn pruned_election_drops_eb_manifests() {
        // Once an election is pruned, eb_tx_hashes and
        // pending_eb_tx_fetches for that EB hash should also be dropped.
        // Otherwise a long-running node leaks one manifest per EB seen.
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        // Simulate the LeiosBlockReceived insert + a pending tx fetch.
        let hash0 = point_hash(0);
        leios
            .state
            .eb_tx_hashes
            .insert(hash0, (0, vec![[0xAAu8; 32], [0xBBu8; 32]]));
        leios
            .state
            .pending_eb_tx_fetches
            .insert(hash0, (0, std::collections::BTreeMap::from([(0u16, 1u64)])));
        assert_eq!(leios.state.eb_tx_hashes.len(), 1);
        assert_eq!(leios.state.pending_eb_tx_fetches.len(), 1);

        // Advance past the pipeline expiry (test pipeline expires at 23).
        leios.on_slot(23).await;

        assert_eq!(
            leios.state.eb_tx_hashes.len(),
            0,
            "eb_tx_hashes should drop entries whose election expired"
        );
        assert_eq!(
            leios.state.pending_eb_tx_fetches.len(),
            0,
            "pending_eb_tx_fetches should drop entries whose election expired"
        );
    }

    #[tokio::test]
    async fn certified_eb_slot_returns_min_quorum_election() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));
        leios.on_slot(5).await;
        leios.on_validated_eb(point(5));

        let voters = [
            "test", "peer-0", "peer-1", "peer-2", "peer-3", "peer-4", "peer-5",
        ];
        let mut all_bodies = Vec::new();
        for slot in [0u64, 5u64] {
            let hash = point_hash(slot);
            for v in &voters {
                let body =
                    crate::production::VoteBody::stub_persistent(slot, v.as_bytes(), 100, &hash);
                all_bodies.push(body.encode(130));
            }
        }
        leios.on_validated_votes(&all_bodies);

        // Neither is CertEligible yet.
        assert_eq!(leios.certified_eb_slot(), None);

        // Advance to make EB at slot 0 CertEligible (elapsed=13 from slot 0).
        leios.on_slot(13).await;
        assert_eq!(leios.certified_eb_slot(), Some(0));

        // Advance further; both eligible — earliest wins.
        leios.on_slot(18).await;
        assert_eq!(leios.certified_eb_slot(), Some(0));
    }

    // -- Bitmap construction tests ------------------------------------------

    use net_core::protocols::leios_fetch::bitmap as bitmap_helpers;
    use net_core::protocols::txsubmission::{PendingTx, TxBody, TxId};

    /// Build the manifest bytes that the producer would emit for a given
    /// list of 32-byte tx hashes at `slot`. Returns the same CBOR shape as
    /// `make_overflow_eb` (`[slot, [hash, ...]]`) plus the EB hash.
    fn make_manifest(slot: u64, hashes: &[[u8; 32]]) -> (Vec<u8>, [u8; 32]) {
        let mut data = Vec::new();
        let mut enc = minicbor::Encoder::new(&mut data);
        let _ = enc
            .array(2)
            .and_then(|e| e.u64(slot))
            .and_then(|e| e.array(hashes.len() as u64));
        for h in hashes {
            let _ = minicbor::Encoder::new(&mut data).bytes(h);
        }
        let hash_result = blake2b_simd::Params::new().hash_length(32).hash(&data);
        let mut eb_hash = [0u8; 32];
        eb_hash.copy_from_slice(hash_result.as_bytes());
        (data, eb_hash)
    }

    /// Drain the consensus command channel until a FetchLeiosBlockTxs
    /// arrives. Skips the RecordLeiosEbManifest emitted earlier on
    /// LeiosBlockReceived so the assertion can focus on the fetch.
    async fn next_fetch_cmd(rx: &mut mpsc::Receiver<NetworkCommand>) -> NetworkCommand {
        loop {
            let cmd = rx.recv().await.expect("command emitted");
            if matches!(cmd, NetworkCommand::FetchLeiosBlockTxs { .. }) {
                return cmd;
            }
        }
    }

    /// Drain until a RecordLeiosEbManifest arrives.
    async fn next_record_cmd(rx: &mut mpsc::Receiver<NetworkCommand>) -> NetworkCommand {
        loop {
            let cmd = rx.recv().await.expect("command emitted");
            if matches!(cmd, NetworkCommand::RecordLeiosEbManifest { .. }) {
                return cmd;
            }
        }
    }

    fn push_tx_with_id(mempool: &crate::mempool::SharedMempool, id: [u8; 32]) {
        let tx = PendingTx {
            tx_id: TxId(id.to_vec()),
            body: TxBody(vec![]),
            size: 0,
        };
        mempool.lock().unwrap().push(tx);
    }

    #[tokio::test]
    async fn bitmap_for_offered_txs_skips_ids_already_in_mempool() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mempool = crate::mempool::new_mempool(1000);
        let mut leios = test_leios_with_mempool(tx, validator, mempool.clone());

        // Three txs in the EB; we already have #0 and #2 in the mempool.
        let h0 = [0xA0u8; 32];
        let h1 = [0xA1u8; 32];
        let h2 = [0xA2u8; 32];
        push_tx_with_id(&mempool, h0);
        push_tx_with_id(&mempool, h2);

        let (manifest, eb_hash) = make_manifest(7, &[h0, h1, h2]);
        let eb_point = Point::Specific {
            slot: 7,
            hash: eb_hash,
        };

        // EB arrives → manifest cached.
        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: eb_point.clone(),
                block: manifest,
            })
            .await;

        // Tx availability announcement → should fetch only the missing index (#1).
        leios
            .handle_event(&NetworkEvent::LeiosBlockTxsOffered {
                peer_id: net_core::peer::PeerId(1),
                point: eb_point.clone(),
            })
            .await;

        let cmd = next_fetch_cmd(&mut rx).await;
        match cmd {
            NetworkCommand::FetchLeiosBlockTxs { point, bitmap, .. } => {
                assert_eq!(point, eb_point);
                let indices: Vec<u32> = bitmap_helpers::iter_indices(&bitmap).collect();
                assert_eq!(indices, vec![1]);
            }
            other => panic!("expected FetchLeiosBlockTxs, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn bitmap_for_offered_txs_falls_back_to_select_all_when_manifest_unknown() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mempool = crate::mempool::new_mempool(1000);
        let mut leios = test_leios_with_mempool(tx, validator, mempool.clone());

        // No manifest cached for this EB.
        let eb_point = Point::Specific {
            slot: 9,
            hash: [0xCC; 32],
        };
        leios
            .handle_event(&NetworkEvent::LeiosBlockTxsOffered {
                peer_id: net_core::peer::PeerId(1),
                point: eb_point,
            })
            .await;

        let cmd = next_fetch_cmd(&mut rx).await;
        match cmd {
            NetworkCommand::FetchLeiosBlockTxs { bitmap, .. } => {
                // Spec-faithful fallback: select_all up to the protocol's
                // max bitmap entries.
                assert_eq!(
                    bitmap.len(),
                    net_core::protocols::leios_fetch::MAX_BITMAP_ENTRIES,
                    "fallback should fill the bitmap"
                );
            }
            other => panic!("expected FetchLeiosBlockTxs, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn bitmap_is_empty_when_mempool_already_has_every_tx() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mempool = crate::mempool::new_mempool(1000);
        let mut leios = test_leios_with_mempool(tx, validator, mempool.clone());

        let h0 = [0xB0u8; 32];
        let h1 = [0xB1u8; 32];
        push_tx_with_id(&mempool, h0);
        push_tx_with_id(&mempool, h1);

        let (manifest, eb_hash) = make_manifest(3, &[h0, h1]);
        let eb_point = Point::Specific {
            slot: 3,
            hash: eb_hash,
        };

        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: eb_point.clone(),
                block: manifest,
            })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockTxsOffered {
                peer_id: net_core::peer::PeerId(1),
                point: eb_point,
            })
            .await;

        let cmd = next_fetch_cmd(&mut rx).await;
        match cmd {
            NetworkCommand::FetchLeiosBlockTxs { bitmap, .. } => {
                assert!(bitmap.is_empty(), "every tx is local; nothing to request");
            }
            other => panic!("expected FetchLeiosBlockTxs, got {other:?}"),
        }
    }

    // -- Response matching tests --------------------------------------------

    /// Helper: hash a tx body the same way `tx_from_received_bytes` does.
    fn body_hash(body: &[u8]) -> [u8; 32] {
        let h = blake2b_simd::Params::new().hash_length(32).hash(body);
        let mut buf = [0u8; 32];
        buf.copy_from_slice(h.as_bytes());
        buf
    }

    #[tokio::test]
    async fn match_eb_tx_response_keeps_only_manifest_hashes_in_order() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mempool = crate::mempool::new_mempool(1000);
        let mut leios = test_leios_with_mempool(tx, validator, mempool);

        // Three bodies → three manifest hashes. We want indices 0 and 2.
        let body0 = b"body-zero".to_vec();
        let body1 = b"body-one".to_vec();
        let body2 = b"body-two".to_vec();
        let h0 = body_hash(&body0);
        let h1 = body_hash(&body1);
        let h2 = body_hash(&body2);
        let bogus = b"unrelated-tx".to_vec();

        let (manifest, eb_hash) = make_manifest(11, &[h0, h1, h2]);
        let eb_point = Point::Specific {
            slot: 11,
            hash: eb_hash,
        };

        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: eb_point.clone(),
                block: manifest,
            })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockTxsOffered {
                peer_id: net_core::peer::PeerId(1),
                point: eb_point.clone(),
            })
            .await;
        let _record = next_record_cmd(&mut rx).await; // drain manifest record
        let cmd = next_fetch_cmd(&mut rx).await;
        // Sanity: the bitmap was {0,1,2}.
        if let NetworkCommand::FetchLeiosBlockTxs { bitmap, .. } = cmd {
            let indices: Vec<u32> = bitmap_helpers::iter_indices(&bitmap).collect();
            assert_eq!(indices, vec![0, 1, 2]);
        }

        // Server returns only [body0, body2] plus a bogus tx out of nowhere.
        let outcome = leios.match_eb_tx_response(&eb_point, &[body0.clone(), body2.clone(), bogus]);
        assert_eq!(outcome.requested, 3);
        assert_eq!(outcome.matched_bodies, vec![body0, body2]);
    }

    #[tokio::test]
    async fn match_eb_tx_response_with_unknown_manifest_passes_through() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mempool = crate::mempool::new_mempool(1000);
        let mut leios = test_leios_with_mempool(tx, validator, mempool);

        // No EB cached for this point.
        let eb_point = Point::Specific {
            slot: 99,
            hash: [0xAA; 32],
        };
        let body = vec![1, 2, 3];
        let outcome = leios.match_eb_tx_response(&eb_point, &[body.clone()]);
        // Manifest unknown → requested=0 (we can't verify), bodies forwarded.
        assert_eq!(outcome.requested, 0);
        assert_eq!(outcome.matched_bodies, vec![body]);
    }

    #[tokio::test]
    async fn match_eb_tx_response_partial_emits_remaining_bitmap() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mempool = crate::mempool::new_mempool(1000);
        let mut leios = test_leios_with_mempool(tx, validator, mempool);

        // Three bodies, request all three, server returns only the middle one.
        let body0 = b"alpha".to_vec();
        let body1 = b"bravo".to_vec();
        let body2 = b"charlie".to_vec();
        let h0 = body_hash(&body0);
        let h1 = body_hash(&body1);
        let h2 = body_hash(&body2);

        let (manifest, eb_hash) = make_manifest(20, &[h0, h1, h2]);
        let eb_point = Point::Specific {
            slot: 20,
            hash: eb_hash,
        };

        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: eb_point.clone(),
                block: manifest,
            })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockTxsOffered {
                peer_id: net_core::peer::PeerId(1),
                point: eb_point.clone(),
            })
            .await;
        let _ = next_record_cmd(&mut rx).await;
        let _ = next_fetch_cmd(&mut rx).await;

        let outcome = leios.match_eb_tx_response(&eb_point, &[body1.clone()]);
        assert_eq!(outcome.matched_bodies, vec![body1]);
        assert_eq!(outcome.requested, 3);
        let remaining: Vec<u32> = bitmap_helpers::iter_indices(&outcome.remaining_bitmap).collect();
        assert_eq!(remaining, vec![0, 2]);

        // A second peer offers the same EB-txs, giving the retry a
        // fresh candidate (con-rs's EbTxsFetchPolicy excludes the
        // previously-attempted peer).
        leios
            .handle_event(&NetworkEvent::LeiosBlockTxsOffered {
                peer_id: net_core::peer::PeerId(2),
                point: eb_point.clone(),
            })
            .await;

        // Retry path: caller issues a fresh fetch with the remaining bitmap.
        leios
            .retry_eb_tx_fetch(eb_point.clone(), outcome.remaining_bitmap)
            .await;
        let cmd = next_fetch_cmd(&mut rx).await;
        match cmd {
            NetworkCommand::FetchLeiosBlockTxs { point, bitmap, .. } => {
                assert_eq!(point, eb_point);
                let indices: Vec<u32> = bitmap_helpers::iter_indices(&bitmap).collect();
                assert_eq!(indices, vec![0, 2]);
            }
            other => panic!("expected FetchLeiosBlockTxs, got {other:?}"),
        }

        // Second response from a different peer fills in the rest.
        let outcome2 = leios.match_eb_tx_response(&eb_point, &[body0.clone(), body2.clone()]);
        assert_eq!(outcome2.matched_bodies, vec![body0, body2]);
        assert_eq!(outcome2.requested, 2);
        assert!(outcome2.remaining_bitmap.is_empty());
    }

    #[tokio::test]
    async fn retry_eb_tx_fetch_with_empty_bitmap_is_noop() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mempool = crate::mempool::new_mempool(1000);
        let mut leios = test_leios_with_mempool(tx, validator, mempool);
        let p = Point::Specific {
            slot: 1,
            hash: [0; 32],
        };
        leios
            .retry_eb_tx_fetch(p, std::collections::BTreeMap::new())
            .await;
        // Channel should have nothing.
        assert!(rx.try_recv().is_err());
    }

    #[tokio::test]
    async fn match_eb_tx_response_pending_bitmap_cleared_after_match() {
        let (tx, mut rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mempool = crate::mempool::new_mempool(1000);
        let mut leios = test_leios_with_mempool(tx, validator, mempool);

        let body = b"x".to_vec();
        let h = body_hash(&body);
        let (manifest, eb_hash) = make_manifest(2, &[h]);
        let eb_point = Point::Specific {
            slot: 2,
            hash: eb_hash,
        };

        leios
            .handle_event(&NetworkEvent::LeiosBlockReceived {
                point: eb_point.clone(),
                block: manifest,
            })
            .await;
        leios
            .handle_event(&NetworkEvent::LeiosBlockTxsOffered {
                peer_id: net_core::peer::PeerId(1),
                point: eb_point.clone(),
            })
            .await;
        let _ = next_record_cmd(&mut rx).await;
        let _ = next_fetch_cmd(&mut rx).await;

        // First match.
        let outcome = leios.match_eb_tx_response(&eb_point, &[body.clone()]);
        assert_eq!(outcome.requested, 1);
        // Second match — pending bitmap was consumed, so requested=0 now.
        let outcome2 = leios.match_eb_tx_response(&eb_point, &[body]);
        assert_eq!(outcome2.requested, 0);
    }

    #[tokio::test]
    async fn duplicate_voter_not_counted() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        let eb_hash = point_hash(0);
        let body = crate::production::VoteBody::stub_persistent(0, b"peer-0", 100, &eb_hash);
        let encoded = body.encode(130);

        leios.on_validated_votes(&[encoded.clone()]);
        leios.on_validated_votes(&[encoded]);
        assert_eq!(leios.election_voter_count(&eb_hash), 1);
    }
}
