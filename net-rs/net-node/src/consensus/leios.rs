//! Leios consensus layer.
//!
//! Tracks per-EB elections following the CIP-0164 Linear Leios pipeline model.
//! Each validated EB gets its own election with phases driven by slot ticks
//! and pipeline timing parameters (3×Δhdr + L_vote + L_diff). Future commits
//! add vote aggregation, certificate formation, and certified-EB extraction
//! for RB header population.

use std::collections::HashMap;
use std::time::{Duration, Instant};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::Point;
use tokio::sync::mpsc;
use tracing::info;

use crate::validation::{LedgerCommand, Validator};

/// How long an in-flight Leios fetch entry remains active before being
/// considered stale. Matches the Praos in-flight TTL.
const IN_FLIGHT_TTL: Duration = Duration::from_secs(15);

// ---------------------------------------------------------------------------
// CIP-0164 pipeline types
// ---------------------------------------------------------------------------

/// Pipeline phase for an EB election (CIP-0164 Linear Leios).
///
/// Each EB progresses through these phases based on elapsed slots since
/// its announcement: EquivocationCheck (3×Δhdr) → Voting (L_vote) →
/// Diffusing (L_diff) → CertEligible (held until pruned).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PipelinePhase {
    /// Waiting for equivocation detection (3 × Δhdr slots).
    EquivocationCheck,
    /// Voting window open (L_vote slots).
    Voting,
    /// Votes diffusing, certificate may form (L_diff slots).
    Diffusing,
    /// Pipeline complete, certificate may be included in an RB.
    CertEligible,
}

/// Per-EB election state.
struct EbElection {
    #[allow(dead_code)] // used by future vote aggregation
    eb_point: Point,
    announced_slot: u64,
    phase: PipelinePhase,
    #[allow(dead_code)] // used by future telemetry
    validated_at: Instant,
}

/// CIP-0164 pipeline timing configuration.
#[derive(Debug, Clone, Copy)]
pub struct PipelineConfig {
    pub delta_hdr: u64,
    pub vote_window: u64,
    pub diffuse_window: u64,
    pub dedup_window: u64,
}

// ---------------------------------------------------------------------------
// LeiosConsensus
// ---------------------------------------------------------------------------

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
}

impl LeiosConsensus {
    pub fn new(
        node_id: String,
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
        pipeline: PipelineConfig,
    ) -> Self {
        Self {
            node_id,
            commands,
            validator,
            in_flight: HashMap::new(),
            pipeline,
            current_slot: 0,
            elections: HashMap::new(),
        }
    }

    // -- Slot tick ----------------------------------------------------------

    /// Advance slot tracking. Updates pipeline phases for all active
    /// elections and prunes expired ones.
    pub fn on_slot(&mut self, slot: u64) {
        self.current_slot = slot;
        self.elections.retain(|_, election| {
            match self
                .pipeline
                .phase_for_elapsed(slot.saturating_sub(election.announced_slot))
            {
                Some(phase) => {
                    election.phase = phase;
                    true
                }
                None => false, // expired
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
            NetworkEvent::LeiosVotesReceived { vote_ids, .. } => {
                self.validator
                    .submit(LedgerCommand::ValidateVotes {
                        vote_ids: vote_ids.clone(),
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

        // Dedup: skip if we already have an election for this EB.
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
                },
            );
        }
        // else: EB is already expired, drop silently
    }

    /// Called when vote validation completes.
    pub fn on_validated_votes(&mut self, vote_ids: &[(u64, Vec<u8>)]) {
        info!(node_id = %self.node_id, count = vote_ids.len(), "votes validated");
    }

    // -- Queries ------------------------------------------------------------

    /// Current pipeline phase for an EB, if it has an active election.
    #[cfg(test)]
    fn election_phase(&self, hash: &[u8; 32]) -> Option<PipelinePhase> {
        self.elections.get(hash).map(|e| e.phase)
    }

    /// Number of active elections.
    #[cfg(test)]
    fn election_count(&self) -> usize {
        self.elections.len()
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

impl PipelineConfig {
    /// Compute the pipeline phase for an EB given the number of slots
    /// elapsed since its announcement. Returns `None` if the election
    /// has expired (past dedup_window after CertEligible).
    fn phase_for_elapsed(&self, elapsed: u64) -> Option<PipelinePhase> {
        let equivocation_end = 3 * self.delta_hdr;
        let voting_end = equivocation_end + self.vote_window;
        let diffuse_end = voting_end + self.diffuse_window;
        let expiry = diffuse_end + self.dedup_window;
        if elapsed < equivocation_end {
            Some(PipelinePhase::EquivocationCheck)
        } else if elapsed < voting_end {
            Some(PipelinePhase::Voting)
        } else if elapsed < diffuse_end {
            Some(PipelinePhase::Diffusing)
        } else if elapsed < expiry {
            Some(PipelinePhase::CertEligible)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::DynamicConfig;
    use tokio::sync::watch;

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
            vote_generation_probability: 0.0,
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
    /// Boundaries: EquivCheck [0,3), Voting [3,8), Diffusing [8,13), CertEligible [13,23), expired ≥23
    fn test_pipeline() -> PipelineConfig {
        PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        }
    }

    fn test_leios(commands: mpsc::Sender<NetworkCommand>, validator: Validator) -> LeiosConsensus {
        LeiosConsensus::new("test".into(), commands, validator, test_pipeline())
    }

    // -- Pipeline phase tests -----------------------------------------------

    #[test]
    fn phase_for_elapsed_boundaries() {
        let p = test_pipeline();
        // EquivocationCheck: elapsed 0..3
        assert_eq!(
            p.phase_for_elapsed(0),
            Some(PipelinePhase::EquivocationCheck)
        );
        assert_eq!(
            p.phase_for_elapsed(2),
            Some(PipelinePhase::EquivocationCheck)
        );
        // Voting: elapsed 3..8
        assert_eq!(p.phase_for_elapsed(3), Some(PipelinePhase::Voting));
        assert_eq!(p.phase_for_elapsed(7), Some(PipelinePhase::Voting));
        // Diffusing: elapsed 8..13
        assert_eq!(p.phase_for_elapsed(8), Some(PipelinePhase::Diffusing));
        assert_eq!(p.phase_for_elapsed(12), Some(PipelinePhase::Diffusing));
        // CertEligible: elapsed 13..23
        assert_eq!(p.phase_for_elapsed(13), Some(PipelinePhase::CertEligible));
        assert_eq!(p.phase_for_elapsed(22), Some(PipelinePhase::CertEligible));
        // Expired: elapsed ≥23
        assert_eq!(p.phase_for_elapsed(23), None);
        assert_eq!(p.phase_for_elapsed(100), None);
    }

    // -- Election lifecycle tests -------------------------------------------

    #[tokio::test]
    async fn eb_creates_election() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(10);
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

        leios.on_slot(10);
        leios.on_validated_eb(point(10));
        // Advance past 3×Δhdr (3 slots) → Voting
        leios.on_slot(13);
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

        leios.on_slot(0);
        leios.on_validated_eb(point(0));

        // EquivocationCheck at slot 0
        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::EquivocationCheck)
        );

        // Voting at slot 3 (3×1)
        leios.on_slot(3);
        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::Voting)
        );

        // Diffusing at slot 8 (3+5)
        leios.on_slot(8);
        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::Diffusing)
        );

        // CertEligible at slot 13 (3+5+5)
        leios.on_slot(13);
        assert_eq!(
            leios.election_phase(&point_hash(0)),
            Some(PipelinePhase::CertEligible)
        );

        // Expired at slot 23 (13+10 dedup)
        leios.on_slot(23);
        assert_eq!(leios.election_phase(&point_hash(0)), None);
        assert_eq!(leios.election_count(), 0);
    }

    #[tokio::test]
    async fn duplicate_eb_deduped() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(10);
        leios.on_validated_eb(point(10));
        leios.on_validated_eb(point(10));
        assert_eq!(leios.election_count(), 1);
    }

    #[tokio::test]
    async fn old_election_pruned() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(0);
        leios.on_validated_eb(point(0));
        assert_eq!(leios.election_count(), 1);

        // Advance past expiry (23 slots with our config)
        leios.on_slot(23);
        assert_eq!(leios.election_count(), 0);
    }

    #[tokio::test]
    async fn multiple_ebs_concurrent() {
        let (tx, _rx) = mpsc::channel(8);
        let (validator, _) = test_validator();
        let mut leios = test_leios(tx, validator);

        leios.on_slot(5);
        leios.on_validated_eb(point(0)); // elapsed=5 → Voting
        leios.on_validated_eb(point(5)); // elapsed=0 → EquivocationCheck

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

        // EB from slot 0 arrives when current_slot=10 → elapsed=10 → Diffusing
        leios.on_slot(10);
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

        // EB from slot 0 arrives at slot 30 → elapsed=30 → expired
        leios.on_slot(30);
        leios.on_validated_eb(point(0));
        assert_eq!(leios.election_count(), 0);
    }

    // -- Existing network event tests ---------------------------------------

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
            crate::validation::LedgerOutcome::VotesValidated { vote_ids: got } => {
                assert_eq!(got, vote_ids);
            }
            other => panic!("expected VotesValidated, got {other:?}"),
        }
    }
}
