//! Leios consensus layer — thin I/O wrapper around `shared_consensus::leios::LeiosState`.
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

use shared_consensus::elections::{Elections, ElectionsConfig};
use shared_consensus::leios::{
    ChainTipContext, LeiosEffect, LeiosState, LeiosTelemetryEvent, VotingConfig,
};
pub use shared_consensus::leios::EbTxMatchOutcome;
pub use shared_consensus::pipeline::PipelineConfig;
use shared_consensus::committee;
use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::{Point, Vote};
use rand::rngs::StdRng;
use rand::SeedableRng;
use tokio::sync::{mpsc, watch};
use tracing::info;

use crate::config::{CommitteeSelection, DynamicConfig, StakeEntry};
use crate::production::decode_overflow_eb;
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
            committee::build_committee(&committee_selection, stake_registry_entries, committee_seed);
        let expected_total_weight = committee::expected_total_weight(
            &committee_selection,
            &persistent_committee,
            total_stake,
        );
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
            // Net-rs keeps the CIP-0164 retry semantics; the
            // single-shot collapse is sim-only for like-for-like
            // comparison against `linear_leios.rs`.
            retry_vote_in_window: true,
        };
        info!(
            node_id = %node_id,
            persistent_seats,
            expected_total_weight,
            committee_pools = persistent_committee.len(),
            "leios committee initialized"
        );
        let elections_config = ElectionsConfig {
            node_id: node_id.clone(),
            pipeline,
            committee_selection,
            persistent_committee,
            stake_registry,
            total_stake,
            expected_total_weight,
            quorum_weight_fraction,
        };
        // σ_c > τ — CIP-164 PR #1196.  Unreachable-quorum configs
        // produce no certificates; surface the misconfiguration at
        // boot rather than running silently.
        if let Err(err) = elections_config.validate() {
            panic!("leios elections config invalid: {err}");
        }
        let elections = Elections::new(elections_config);
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

    /// If the EB at `eb_hash` has reached quorum and entered
    /// CertEligible, return its announced slot; otherwise `None`.
    /// The Praos adapter combines this with the parent RB's announced
    /// EB hash to decide whether to attach a cert (linear-Leios rule:
    /// the cert can only target the parent RB's EB).
    pub fn eb_certifiable_slot(&self, eb_hash: &[u8; 32]) -> Option<u64> {
        self.state.eb_certifiable_slot(eb_hash)
    }

    /// Update the adopted-chain-tip metadata used by the CIP-0164
    /// voting predicates (`LateRBHeader`, `WrongEB`).  The Praos
    /// adapter calls this whenever a new RB is adopted as the chain
    /// tip — passing the slot at which the RB header arrived locally
    /// and the EB hash (if any) the header announces.
    pub fn set_chain_tip_context(&mut self, ctx: ChainTipContext) {
        self.state.set_chain_tip_context(ctx);
    }

    /// Replace the per-peer RTT oracle the EB / EB-tx / vote fetch
    /// policies consult.  The Consensus facade calls this with the
    /// shared [`shared_consensus::fetch::PeerRttCache`] the coordinator's
    /// `peer_rtt_observer` callback writes into.
    pub fn set_rtt(&mut self, rtt: shared_consensus::fetch::PeerRttCache) {
        self.state.set_rtt(Box::new(rtt));
    }

    /// Replace the EbFetchPolicy shared-consensus consults when emitting
    /// `FetchLeiosBlock`.
    pub fn set_eb_policy(
        &mut self,
        policy: Box<dyn shared_consensus::fetch::EbFetchPolicy + Send + Sync>,
    ) {
        self.state.set_eb_policy(policy);
    }

    /// Replace the EbTxsFetchPolicy shared-consensus consults when emitting
    /// `FetchLeiosBlockTxs`.  Driven by `fetch_policy.eb_txs` — fanning
    /// out EB-txs is the primary research lever we have to characterise
    /// the cluster collapse mode.
    pub fn set_eb_txs_policy(
        &mut self,
        policy: Box<dyn shared_consensus::fetch::EbTxsFetchPolicy + Send + Sync>,
    ) {
        self.state.set_eb_txs_policy(policy);
    }

    /// Replace the VoteFetchPolicy shared-consensus consults when emitting
    /// `FetchLeiosVotes`.
    pub fn set_vote_policy(
        &mut self,
        policy: Box<dyn shared_consensus::fetch::VoteFetchPolicy + Send + Sync>,
    ) {
        self.state.set_vote_policy(policy);
    }

    /// Install a shared behaviour handle on the underlying state.  The
    /// `Consensus` facade hands the same handle to every owned state
    /// machine and the coordinator.
    pub fn install_behaviour_handle(
        &mut self,
        handle: shared_consensus::behaviour::BehaviourHandle,
    ) {
        self.state.behaviour = handle;
    }

    /// Mutable borrow of [`LeiosState`] for the few wrapper paths that
    /// need to drive the take/restore behaviour helpers (e.g.
    /// `ask_rb_production_strategy`).
    pub(crate) fn state_mut(&mut self) -> &mut shared_consensus::leios::LeiosState {
        &mut self.state
    }

    /// Advance slot tracking, drive elections, dispatch any effects.
    pub async fn on_slot(&mut self, slot: u64) {
        // Snapshot every locally available tx id — the FIFO mempool
        // plus EB-pinned bodies — so the CIP-0164 `MissingTX` predicate
        // sees both the producer's own pinned EB closure and any bodies
        // a receiver has merged via `LeiosFetch BlockTxs`.  Snapshot
        // upfront so we don't hold the mempool lock across the call.
        let known = self.mempool.lock().unwrap().all_known_tx_ids();
        let tx_known = |h: &[u8; 32]| known.contains(h.as_slice());
        let mut fx = self.state.on_slot(slot, &tx_known);
        fx.push(LeiosEffect::EmitTelemetry(LeiosTelemetryEvent::LeiosElectionInfo {
            eb_slot: slot,
            perm_committee: self.state.voting_config.persistent_seats > 0,
        }));
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
            NetworkEvent::LeiosBlockReceived { point, block } => {
                let manifest = decode_overflow_eb(block).map(|(_, hashes)| hashes);
                (true, self.state.on_eb_received(point.clone(), manifest))
            }
            NetworkEvent::LeiosVotesReceived { votes, .. } => {
                // Inline votes: feed straight into aggregation (the mocked
                // signature needs no ledger validation step).
                (true, self.state.on_votes_received(votes.clone()))
            }
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

    /// Register a self-produced EB.  Decodes the manifest, runs the
    /// same `on_eb_received` path receivers go through (so the
    /// `RecordLeiosEbManifest` effect lands in the LeiosStore and
    /// peer offers fire), and marks the EB validated immediately —
    /// the producer trusts its own work.
    pub async fn register_self_produced_eb(&mut self, point: Point, eb_data: &[u8]) {
        let manifest = decode_overflow_eb(eb_data).map(|(_, hashes)| hashes);
        let fx = self.state.on_eb_received(point.clone(), manifest);
        self.dispatch(fx).await;
        self.state.on_validated_eb(point);
    }

    /// Verify a `LeiosBlockTxsReceived` response against the cached
    /// manifest.  Bodies are blake2b-hashed here (the wire-format body
    /// hash) before being matched, since shared-consensus is format-agnostic.
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
    /// for an EB-tx offer.  Delegates to
    /// [`shared_consensus::leios::LeiosState::missing_eb_tx_bitmap`]; an empty
    /// result here suppresses the fetch (manifest unknown or every
    /// referenced tx already locally available).
    fn bitmap_for_missing_txs(&self, point: &Point) -> BTreeMap<u16, u64> {
        let hash = match point {
            Point::Specific { hash, .. } => hash,
            Point::Origin => return BTreeMap::new(),
        };
        let mempool = self.mempool.lock().unwrap();
        self.state.missing_eb_tx_bitmap(hash, mempool.as_inner())
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
                        LeiosTelemetryEvent::LeiosElectionInfo {
                            eb_slot,
                            perm_committee,
                        } => NodeEvent::LeiosElectionInfo {
                            node: node_id,
                            slot: eb_slot,
                            pers_committee_member: perm_committee,
                        }
                    };
                    self.pending_telemetry.push(node_event);
                }
            }
        }
    }

    /// Build and inject the inline vote for an EB.  The CIP-0164
    /// prototype vote carries no PV/NPV tag, so an eligible node (PV
    /// seat and/or NPV win) emits a single structured vote keyed by its
    /// compact voter index from the shared registry.
    async fn emit_vote(
        &mut self,
        eb_slot: u64,
        eb_hash: [u8; 32],
        emit_pv: bool,
        npv_signature: Option<Vec<u8>>,
    ) {
        if !emit_pv && npv_signature.is_none() {
            return;
        }
        let node_id = self.state.node_id.clone();
        let Some(voter_id) = self.state.elections.voter_index(&node_id) else {
            // Not in the shared voter registry — can't produce a vote
            // that downstream nodes could resolve to a weight.
            return;
        };
        let vote = Vote {
            slot: eb_slot,
            eb_hash,
            voter_id,
            // Signature is mocked in the prototype.
            vote_signature: true,
        };
        info!(
            node_id = %node_id,
            eb_slot, voter_id, "vote produced for eb"
        );
        self.pending_telemetry.push(NodeEvent::VTBundleGenerated {
            node: node_id,
            slot: eb_slot,
            count: 1,
        });
        let _ = self
            .commands
            .send(NetworkCommand::InjectLeiosVotes { votes: vec![vote] })
            .await;
    }

    // -- Test helpers (delegate through state) -----------------------------

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
    use std::time::Duration;

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

    // Pure election-lifecycle / pipeline-phase behaviour is covered in
    // `shared-consensus/src/elections.rs` and `shared-consensus/src/pipeline.rs`.  The tests
    // below exercise only the wrapper-side translation work: effects →
    // NetworkCommands, validator submissions, telemetry mapping, and
    // the mempool-aware bitmap computation.

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
            ..Default::default()
        });
        // No vote yet — still in EquivocationCheck.
        assert!(!leios.election_voted(&point_hash(0)));

        // Advance to Voting phase (elapsed=3).
        leios.on_slot(3).await;
        assert!(leios.election_voted(&point_hash(0)));

        // Check that InjectLeiosVotes was sent with one inline vote.
        match rx.try_recv() {
            Ok(NetworkCommand::InjectLeiosVotes { votes }) => {
                assert_eq!(votes.len(), 1);
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
            ..Default::default()
        });

        // First slot in Voting → vote produced.
        leios.on_slot(3).await;
        assert!(rx.try_recv().is_ok());

        // Second slot in Voting → no duplicate vote.
        leios.on_slot(4).await;
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

    // -- Vote aggregation tests ---------------------------------------------
    //
    // Under EveryoneVotes (test_leios mode) every registered pool has 1
    // PV seat, so each inline vote contributes weight 1. The 10-pool test
    // registry yields expected_total_weight=10; quorum at 0.75 needs
    // ≥7 distinct voters. Voter ids are compact indices into the sorted
    // registry: "peer-0".."peer-8" → 0..8, "test" → 9.

    /// An inline vote for `eb_hash` at `slot` from voter index `voter_id`.
    fn inline_vote(slot: u64, eb_hash: [u8; 32], voter_id: u16) -> Vote {
        Vote {
            slot,
            eb_hash,
            voter_id,
            vote_signature: true,
        }
    }

    #[tokio::test]
    async fn votes_received_records_vote() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _outcome_rx) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));
        let eb_hash = point_hash(0);

        // peer-0 is voter index 0 in the sorted registry.
        leios
            .handle_event(&NetworkEvent::LeiosVotesReceived {
                peer_id: net_core::peer::PeerId(1),
                votes: vec![inline_vote(0, eb_hash, 0)],
            })
            .await;

        assert_eq!(leios.election_voter_count(&eb_hash), 1);
        assert!(!leios.election_quorum(&eb_hash));
    }

    #[tokio::test]
    async fn votes_attributed_to_eb_election() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));

        let eb_hash = point_hash(0);
        leios
            .handle_event(&NetworkEvent::LeiosVotesReceived {
                peer_id: net_core::peer::PeerId(1),
                votes: vec![inline_vote(0, eb_hash, 0)],
            })
            .await;
        assert_eq!(leios.election_voter_count(&eb_hash), 1);
        assert!(!leios.election_quorum(&eb_hash));
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
        // 8 distinct voter indices reach the τ = 0.75 quorum: in
        // `EveryoneVotes` each pool has weight 1, so the threshold is
        // `ceil(0.75 × 10) = 8`.  test(9) + peer-0..peer-6 (0..6).
        let votes: Vec<Vote> = [9u16, 0, 1, 2, 3, 4, 5, 6]
            .iter()
            .map(|&id| inline_vote(0, eb_hash, id))
            .collect();
        leios
            .handle_event(&NetworkEvent::LeiosVotesReceived {
                peer_id: net_core::peer::PeerId(1),
                votes,
            })
            .await;

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
            assert_eq!(*voted_weight, 8);
            assert_eq!(*voters, 8);
        }

        // Subsequent votes don't re-fire (peer-7 → index 7, a new voter).
        leios
            .handle_event(&NetworkEvent::LeiosVotesReceived {
                peer_id: net_core::peer::PeerId(1),
                votes: vec![inline_vote(0, eb_hash, 7)],
            })
            .await;
        let drained2 = leios.drain_telemetry();
        assert!(!drained2
            .iter()
            .any(|e| matches!(e, NodeEvent::LeiosQuorumReached { .. })));
    }

    #[tokio::test]
    async fn eb_certifiable_slot_targets_specific_hash() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0).await;
        leios.on_validated_eb(point(0));
        leios.on_slot(5).await;
        leios.on_validated_eb(point(5));

        let hash0 = point_hash(0);
        let hash5 = point_hash(5);
        // 8 distinct voter indices reach the τ = 0.75 quorum
        // (ceil(0.75 × 10) = 8): test(9) + peer-0..peer-6.
        let voter_ids = [9u16, 0, 1, 2, 3, 4, 5, 6];
        let mut all_votes = Vec::new();
        for slot in [0u64, 5u64] {
            let hash = point_hash(slot);
            for &id in &voter_ids {
                all_votes.push(inline_vote(slot, hash, id));
            }
        }
        leios
            .handle_event(&NetworkEvent::LeiosVotesReceived {
                peer_id: net_core::peer::PeerId(1),
                votes: all_votes,
            })
            .await;

        // Neither is CertEligible yet.
        assert_eq!(leios.eb_certifiable_slot(&hash0), None);
        assert_eq!(leios.eb_certifiable_slot(&hash5), None);

        // Advance to make EB at slot 0 CertEligible (elapsed=13 from slot 0).
        // EB at slot 5 is still Diffusing (elapsed=8).
        leios.on_slot(13).await;
        assert_eq!(leios.eb_certifiable_slot(&hash0), Some(0));
        assert_eq!(leios.eb_certifiable_slot(&hash5), None);

        // Both reach CertEligible — each lookup is independent.
        leios.on_slot(18).await;
        assert_eq!(leios.eb_certifiable_slot(&hash0), Some(0));
        assert_eq!(leios.eb_certifiable_slot(&hash5), Some(5));

        // An unrelated hash never matches.
        assert_eq!(leios.eb_certifiable_slot(&[0xAA; 32]), None);
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

    /// Returns true if no `FetchLeiosBlockTxs` arrives within `window`.
    /// Drains and ignores any other command kinds so the assertion only
    /// cares about the fetch effect.
    async fn no_fetch_cmd_within(
        rx: &mut mpsc::Receiver<NetworkCommand>,
        window: Duration,
    ) -> bool {
        let deadline = tokio::time::Instant::now() + window;
        loop {
            let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
            if remaining.is_zero() {
                return true;
            }
            match tokio::time::timeout(remaining, rx.recv()).await {
                Err(_) => return true,
                Ok(None) => return true,
                Ok(Some(NetworkCommand::FetchLeiosBlockTxs { .. })) => return false,
                Ok(Some(_)) => continue,
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
    async fn no_fetch_emitted_when_manifest_unknown() {
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

        // With no manifest cached, the wrapper computes an empty bitmap
        // and shared-consensus short-circuits before emitting a fetch.
        assert!(
            no_fetch_cmd_within(&mut rx, Duration::from_millis(50)).await,
            "fetch should be deferred until the manifest is received"
        );
    }

    #[tokio::test]
    async fn no_fetch_emitted_when_mempool_already_has_every_tx() {
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

        assert!(
            no_fetch_cmd_within(&mut rx, Duration::from_millis(50)).await,
            "every tx is local; nothing to request, so no fetch should be emitted"
        );
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

        let outcome = leios.match_eb_tx_response(&eb_point, std::slice::from_ref(&body1));
        assert_eq!(outcome.matched_bodies, vec![body1]);
        assert_eq!(outcome.requested, 3);
        let remaining: Vec<u32> = bitmap_helpers::iter_indices(&outcome.remaining_bitmap).collect();
        assert_eq!(remaining, vec![0, 2]);

        // A second peer offers the same EB-txs, giving the retry a
        // fresh candidate (shared-consensus's EbTxsFetchPolicy excludes the
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

}
