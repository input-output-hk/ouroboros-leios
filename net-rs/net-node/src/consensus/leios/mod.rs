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
mod wfa;

use std::collections::{BTreeMap, HashMap};
use std::time::{Duration, Instant};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::Point;
use rand::rngs::StdRng;
use rand::SeedableRng;
use tokio::sync::{mpsc, watch};
use tracing::info;

use crate::config::{CommitteeSelection, DynamicConfig, StakeEntry};
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
    /// Local mempool. Used to compute the bitmap of missing txs when a
    /// peer announces an EB's transactions.
    mempool: crate::mempool::SharedMempool,
    /// Per-EB ordered tx hash list, decoded from the EB manifest on
    /// `LeiosBlockReceived`. Drives the missing-tx bitmap on
    /// `LeiosBlockTxsOffered`.
    eb_tx_hashes: HashMap<[u8; 32], Vec<[u8; 32]>>,
    /// Leios points currently being fetched.
    in_flight: HashMap<Point, Instant>,
    /// Pipeline timing parameters.
    pipeline: PipelineConfig,
    /// Current slot (advanced by `on_slot`).
    current_slot: u64,
    /// Per-EB elections, keyed by EB hash.
    elections: HashMap<[u8; 32], EbElection>,
    /// Committee selection mode.
    committee_selection: CommitteeSelection,
    /// Voting configuration (committee selection, stake, vote sizes).
    voting_config: VotingConfig,
    /// Per-pool persistent committee allocation, identical on every node.
    persistent_committee: BTreeMap<String, u32>,
    /// Network-wide stake registry. Used to look up a voter's stake when
    /// re-running the NPV lottery for incoming votes.
    stake_registry: BTreeMap<String, u64>,
    /// Total network stake (sum of stake_registry).
    total_stake: u64,
    /// Fraction of expected committee weight required for quorum.
    quorum_weight_fraction: f64,
    /// Σ persistent_seats + non_persistent_voters. Threshold base.
    expected_committee_size: u32,
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
        Self {
            node_id,
            commands,
            validator,
            mempool,
            eb_tx_hashes: HashMap::new(),
            in_flight: HashMap::new(),
            pipeline,
            current_slot: 0,
            elections: HashMap::new(),
            committee_selection,
            voting_config,
            persistent_committee,
            stake_registry,
            total_stake,
            quorum_weight_fraction,
            expected_committee_size,
            rng: match rng_seed {
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
        for (hash, eb_slot) in to_vote {
            if voting::try_vote_on_eb(
                &self.node_id,
                &hash,
                eb_slot,
                &self.voting_config,
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
                        voted_weight: election.voter_weights.values().map(|w| *w as u64).sum(),
                        voters: election.voter_weights.len(),
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
                    let bitmap = self.bitmap_for_missing_txs(point);
                    info!(
                        node_id = %self.node_id,
                        %point,
                        bitmap_segments = bitmap.len(),
                        "fetching leios block txs"
                    );
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchLeiosBlockTxs {
                            point: point.clone(),
                            bitmap,
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
            NetworkEvent::LeiosBlockReceived { point, block } => {
                self.in_flight.remove(point);
                if let Point::Specific { hash, .. } = point {
                    if let Some((_slot, hashes)) = crate::production::decode_overflow_eb(block) {
                        self.eb_tx_hashes.insert(*hash, hashes.clone());
                        // Tell the coordinator's LeiosStore so this node
                        // can re-serve EB tx requests via the mempool-
                        // backed resolver.
                        let _ = self
                            .commands
                            .send(NetworkCommand::RecordLeiosEbManifest {
                                point: point.clone(),
                                tx_hashes: hashes,
                            })
                            .await;
                    }
                }
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
                    voter_weights: HashMap::new(),
                    quorum_reached: false,
                },
            );
        }
    }

    /// Called when vote validation completes. Derives each vote's weight
    /// (PV: persistent committee lookup; NPV: re-run the lottery from
    /// the embedded eligibility signature and the voter's ledger stake)
    /// and attributes it to the relevant EB election, checking quorum.
    pub fn on_validated_votes(&mut self, vote_data: &[Vec<u8>]) {
        for blob in vote_data {
            let Some(body) = crate::production::VoteBody::decode(blob) else {
                continue;
            };
            let voter_id_str = String::from_utf8_lossy(&body.voter_id).into_owned();
            let weight = match (body.tag, &body.eligibility_signature) {
                (0, _) => self
                    .persistent_committee
                    .get(&voter_id_str)
                    .copied()
                    .unwrap_or(0),
                (1, Some(sig)) => {
                    let stake = self.stake_registry.get(&voter_id_str).copied().unwrap_or(0);
                    wfa::count_npv_wins(
                        sig,
                        stake,
                        self.total_stake,
                        self.committee_selection.non_persistent_voters(),
                    )
                }
                _ => 0,
            };
            if weight == 0 {
                continue;
            }
            // Dedup key: voter_id + tag (a node may issue both a PV and
            // an NPV body for the same EB).
            let mut key = body.voter_id.clone();
            key.push(body.tag);
            if let Some(formed) = aggregation::record_vote(
                &mut self.elections,
                &body.endorser_block_hash,
                key,
                weight,
                self.quorum_weight_fraction,
                self.expected_committee_size,
                &self.node_id,
            ) {
                self.pending_telemetry.push(NodeEvent::LeiosQuorumReached {
                    node: self.node_id.clone(),
                    eb_slot: formed.eb_slot,
                    voted_weight: formed.voted_weight,
                    voters: formed.voters,
                });
            }
        }
    }

    /// Build the sparse bitmap of transactions we don't already have for
    /// a peer's `LeiosBlockTxsOffered` for `point`. If the EB manifest
    /// is unknown (we haven't received the EB yet, or it failed to
    /// decode), fall back to selecting all transactions so the request
    /// is still useful.
    fn bitmap_for_missing_txs(&self, point: &Point) -> std::collections::BTreeMap<u16, u64> {
        use net_core::protocols::leios_fetch::bitmap;
        let hash = match point {
            Point::Specific { hash, .. } => hash,
            Point::Origin => return BTreeMap::new(),
        };
        let Some(tx_hashes) = self.eb_tx_hashes.get(hash) else {
            // We learned about txs before fetching/validating the EB
            // (notification re-flooded ahead of our local EB fetch).
            // Fall back to "every tx the protocol supports"; the server
            // returns only what it actually has.
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
            .map(|e| e.voter_weights.len())
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
                point: eb_point.clone(),
            })
            .await;

        let cmd = next_fetch_cmd(&mut rx).await;
        match cmd {
            NetworkCommand::FetchLeiosBlockTxs { point, bitmap } => {
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
            .handle_event(&NetworkEvent::LeiosBlockTxsOffered { point: eb_point })
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
            .handle_event(&NetworkEvent::LeiosBlockTxsOffered { point: eb_point })
            .await;

        let cmd = next_fetch_cmd(&mut rx).await;
        match cmd {
            NetworkCommand::FetchLeiosBlockTxs { bitmap, .. } => {
                assert!(bitmap.is_empty(), "every tx is local; nothing to request");
            }
            other => panic!("expected FetchLeiosBlockTxs, got {other:?}"),
        }
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
