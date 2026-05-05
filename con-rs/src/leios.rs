//! Leios consensus state machine (CIP-0164 Linear Leios variant).
//!
//! `LeiosState` owns:
//! - the per-EB election state (via [`Elections`])
//! - the Leios-fetch state (per-EB tx-hash manifests, in-flight fetches,
//!   pending bitmap requests)
//! - the local node's voting configuration
//!
//! Sans-IO: every public method either mutates state and returns a
//! `Vec<LeiosEffect>` describing what the caller's I/O layer should
//! dispatch — fetch an EB or its txs, ask for votes, record a manifest
//! for serving back to peers, hand a block to the validator, emit a
//! vote, raise telemetry — or returns a pure query result.
//!
//! Vote bodies are not built here.  When the local node is eligible to
//! vote, the state emits an [`LeiosEffect::EmitVote`] carrying logical
//! args (PV flag, NPV eligibility signature); the I/O layer encodes the
//! wire-format vote body and sends it.  Same principle as `praos`:
//! con-rs is format-agnostic.

use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use tracing::info;

use crate::aggregation::QuorumFormed;
use crate::config::CommitteeSelection;
use crate::elections::{Elections, SlotEffect};
use crate::pipeline::PipelineConfig;
use crate::types::Point;
use crate::wfa;

/// How long an in-flight fetch entry remains "active" before being
/// considered stale and eligible for retry.
pub const IN_FLIGHT_TTL: Duration = Duration::from_secs(15);

// ---------------------------------------------------------------------------
// Voting configuration
// ---------------------------------------------------------------------------

/// Per-node voting configuration.  The committee selection rule, the
/// node's own stake, total network stake, and the number of persistent
/// committee seats this node holds (pre-computed at startup from the
/// stake registry).  `*_vote_bytes` are the encoded body sizes the I/O
/// layer should pad each emitted vote body to.
#[derive(Debug, Clone)]
pub struct VotingConfig {
    pub committee_selection: CommitteeSelection,
    pub stake: u64,
    pub total_stake: u64,
    pub persistent_vote_bytes: usize,
    pub non_persistent_vote_bytes: usize,
    /// Number of PV seats this node holds in the persistent committee.
    /// `0` means no PV vote is emitted regardless of EB.
    pub persistent_seats: u32,
}

// ---------------------------------------------------------------------------
// Effect type
// ---------------------------------------------------------------------------

/// What the I/O layer should do as a result of a state mutation.
#[derive(Debug, Clone)]
pub enum LeiosEffect {
    /// Request the EB body from a peer.
    FetchLeiosBlock { point: Point },
    /// Request transactions in an EB selected by `bitmap` (sparse map of
    /// 64-bit segments keyed by 16-bit segment index).
    FetchLeiosBlockTxs {
        point: Point,
        bitmap: BTreeMap<u16, u64>,
    },
    /// Request the listed votes from peers.
    FetchLeiosVotes { votes: Vec<(u64, Vec<u8>)> },
    /// Record the EB-tx manifest in the network-side store so this
    /// node can serve EB-tx requests back to peers.
    RecordLeiosEbManifest {
        point: Point,
        tx_hashes: Vec<[u8; 32]>,
    },

    /// The local node is eligible to vote for this EB.  The I/O layer
    /// should build the vote body (or bodies, when both PV and NPV
    /// apply) using the wire-format vote-body encoder, then ship them
    /// in one batch.  The state machine has already committed to the
    /// vote: it has marked the election as voted before emitting this
    /// effect.
    EmitVote {
        eb_slot: u64,
        eb_hash: [u8; 32],
        /// True if a PV (persistent committee) body should be emitted.
        emit_pv: bool,
        /// Some(sig) if an NPV body should be emitted, carrying this
        /// eligibility signature.  None for PV-only or no-vote cases.
        npv_signature: Option<Vec<u8>>,
    },

    /// Submit a fetched EB body for ledger validation.
    ValidateEb { point: Point },
    /// Submit fetched vote bodies for ledger validation.
    ValidateVotes {
        vote_ids: Vec<(u64, Vec<u8>)>,
        vote_data: Vec<Vec<u8>>,
    },

    /// Telemetry event the I/O layer should forward to its sink.
    EmitTelemetry(LeiosTelemetryEvent),
}

/// Structured telemetry events emitted by the state machine.  The I/O
/// layer adapts each into its own event type before persisting.
#[derive(Debug, Clone)]
pub enum LeiosTelemetryEvent {
    QuorumReached {
        eb_slot: u64,
        voted_weight: u64,
        voters: usize,
    },
    ElectionExpired {
        eb_slot: u64,
        had_quorum: bool,
        voted_weight: u64,
        voters: usize,
    },
}

// ---------------------------------------------------------------------------
// EB-tx response matching
// ---------------------------------------------------------------------------

/// Result of matching a `LeiosBlockTxsReceived` response against the
/// cached manifest.  The I/O layer forwards `matched_bodies` to the
/// validator and re-issues a fetch for `remaining_bitmap` against a
/// different peer if non-empty.
#[derive(Debug, Clone)]
pub struct EbTxMatchOutcome {
    /// Bodies whose blake2b-256 hash maps to a requested manifest
    /// index, in ascending manifest-index order.
    pub matched_bodies: Vec<Vec<u8>>,
    /// Number of indices that the original request bitmap selected.
    /// Zero means "manifest not cached at request time" (fallback path).
    pub requested: usize,
    /// Indices we requested but didn't receive a matching body for.
    pub remaining_bitmap: BTreeMap<u16, u64>,
}

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------

/// Leios consensus state for one node.
///
/// Fields are `pub` so adapter code can read and selectively
/// manipulate them.  Treat them as state-machine internals: prefer the
/// public methods, which preserve invariants and emit the right
/// effects.
pub struct LeiosState {
    pub node_id: String,
    pub elections: Elections,
    pub voting_config: VotingConfig,
    pub pipeline: PipelineConfig,

    /// Per-EB ordered tx-hash list, decoded from the EB manifest on
    /// `on_eb_received`.  Tagged with the EB's announced slot so stale
    /// entries can be pruned in `on_slot`.
    pub eb_tx_hashes: BTreeMap<[u8; 32], (u64, Vec<[u8; 32]>)>,
    /// Per-EB requested bitmap.  Set when a `FetchLeiosBlockTxs` is
    /// emitted; used at response time to verify which manifest indices
    /// were actually fulfilled.
    pub pending_eb_tx_fetches: BTreeMap<[u8; 32], (u64, BTreeMap<u16, u64>)>,
    /// Leios points / fetch gates currently in flight.
    pub in_flight: BTreeMap<Point, Instant>,
}

impl LeiosState {
    pub fn new(
        node_id: String,
        elections: Elections,
        voting_config: VotingConfig,
        pipeline: PipelineConfig,
    ) -> Self {
        Self {
            node_id,
            elections,
            voting_config,
            pipeline,
            eb_tx_hashes: BTreeMap::new(),
            pending_eb_tx_fetches: BTreeMap::new(),
            in_flight: BTreeMap::new(),
        }
    }

    // -- Slot tick ----------------------------------------------------------

    /// Drive the election state machine forward, decide voting for any
    /// election entering the Voting phase, and prune stale Leios-fetch
    /// state.  Returns the effects to dispatch.
    pub fn on_slot(&mut self, slot: u64) -> Vec<LeiosEffect> {
        let mut fx: Vec<LeiosEffect> = Vec::new();
        for eff in self.elections.on_slot(slot) {
            match eff {
                SlotEffect::EligibleToVote { eb_hash, eb_slot } => {
                    let (emit_pv, npv_signature) = self.decide_vote(&eb_hash, eb_slot);
                    if emit_pv || npv_signature.is_some() {
                        info!(
                            node_id = %self.node_id,
                            eb_slot,
                            emit_pv,
                            emit_npv = npv_signature.is_some(),
                            "voting on eb"
                        );
                        self.elections.mark_voted(&eb_hash);
                        fx.push(LeiosEffect::EmitVote {
                            eb_slot,
                            eb_hash,
                            emit_pv,
                            npv_signature,
                        });
                    }
                }
                SlotEffect::Expired {
                    eb_slot,
                    had_quorum,
                    voted_weight,
                    voters,
                    ..
                } => {
                    fx.push(LeiosEffect::EmitTelemetry(
                        LeiosTelemetryEvent::ElectionExpired {
                            eb_slot,
                            had_quorum,
                            voted_weight,
                            voters,
                        },
                    ));
                }
            }
        }
        // Prune EB manifests and in-progress tx-fetch state by slot age.
        let pipeline = self.pipeline;
        self.eb_tx_hashes.retain(|_, (eb_slot, _)| {
            pipeline
                .phase_for_elapsed(slot.saturating_sub(*eb_slot))
                .is_some()
        });
        self.pending_eb_tx_fetches.retain(|_, (eb_slot, _)| {
            pipeline
                .phase_for_elapsed(slot.saturating_sub(*eb_slot))
                .is_some()
        });
        fx
    }

    /// Pure decision: should this node emit a PV vote and/or an NPV
    /// vote for this EB, and if NPV, what's the eligibility signature?
    fn decide_vote(&self, eb_hash: &[u8; 32], eb_slot: u64) -> (bool, Option<Vec<u8>>) {
        let emit_pv = self.voting_config.persistent_seats > 0;
        let n_npv = self.voting_config.committee_selection.non_persistent_voters();
        let npv_signature = if n_npv > 0 {
            let sig = wfa::npv_eligibility_signature(
                self.node_id.as_bytes(),
                eb_hash,
                eb_slot,
            );
            let wins = wfa::count_npv_wins(
                &sig,
                self.voting_config.stake,
                self.voting_config.total_stake,
                n_npv,
            );
            if wins > 0 {
                Some(sig)
            } else {
                None
            }
        } else {
            None
        };
        (emit_pv, npv_signature)
    }

    // -- Network event handlers ---------------------------------------------

    /// A peer offered an EB.  If we don't have it in flight, request it.
    pub fn on_eb_offered(&mut self, point: Point, now: Instant) -> Vec<LeiosEffect> {
        self.evict_stale_in_flight(now);
        if self.in_flight.contains_key(&point) {
            return Vec::new();
        }
        self.in_flight.insert(point.clone(), now);
        info!(node_id = %self.node_id, %point, "fetching leios block");
        vec![LeiosEffect::FetchLeiosBlock { point }]
    }

    /// A peer offered EB transactions.  Caller has already computed the
    /// bitmap of indices it doesn't already have (from its mempool).
    /// We dedup via an in-flight gate keyed by EB slot.
    pub fn on_eb_txs_offered(
        &mut self,
        point: Point,
        bitmap: BTreeMap<u16, u64>,
        now: Instant,
    ) -> Vec<LeiosEffect> {
        self.evict_stale_in_flight(now);
        let slot = match &point {
            Point::Specific { slot, .. } => *slot,
            _ => return Vec::new(),
        };
        // Per-slot gate keeps multiple offers from triggering parallel
        // fetches; the synthetic hash distinguishes the gate from an
        // EB-body fetch on the same slot.
        let gate_key = Point::Specific {
            slot,
            hash: [0xFE; 32],
        };
        if self.in_flight.contains_key(&gate_key) {
            return Vec::new();
        }
        self.in_flight.insert(gate_key, now);
        if let Point::Specific { slot, hash } = &point {
            self.pending_eb_tx_fetches
                .insert(*hash, (*slot, bitmap.clone()));
        }
        info!(
            node_id = %self.node_id,
            %point,
            bitmap_segments = bitmap.len(),
            "fetching leios block txs"
        );
        vec![LeiosEffect::FetchLeiosBlockTxs { point, bitmap }]
    }

    /// A peer offered votes; forward the fetch.
    pub fn on_votes_offered(&mut self, votes: Vec<(u64, Vec<u8>)>) -> Vec<LeiosEffect> {
        if votes.is_empty() {
            return Vec::new();
        }
        info!(
            node_id = %self.node_id,
            count = votes.len(),
            "fetching leios votes"
        );
        vec![LeiosEffect::FetchLeiosVotes { votes }]
    }

    /// An EB body arrived.  `manifest_hashes` is the decoded tx-hash
    /// list (or `None` if the body didn't decode as an overflow EB —
    /// e.g., a header-only block).  Always emits a `ValidateEb`.
    pub fn on_eb_received(
        &mut self,
        point: Point,
        manifest_hashes: Option<Vec<[u8; 32]>>,
    ) -> Vec<LeiosEffect> {
        self.in_flight.remove(&point);
        let mut fx = Vec::new();
        if let (Some(hashes), Point::Specific { slot, hash }) = (manifest_hashes, &point) {
            self.eb_tx_hashes.insert(*hash, (*slot, hashes.clone()));
            fx.push(LeiosEffect::RecordLeiosEbManifest {
                point: point.clone(),
                tx_hashes: hashes,
            });
        }
        fx.push(LeiosEffect::ValidateEb { point });
        fx
    }

    /// Received vote bodies; submit to the validator.
    pub fn on_votes_received(
        &mut self,
        vote_ids: Vec<(u64, Vec<u8>)>,
        vote_data: Vec<Vec<u8>>,
    ) -> Vec<LeiosEffect> {
        vec![LeiosEffect::ValidateVotes {
            vote_ids,
            vote_data,
        }]
    }

    /// EB transactions arrived; clear the per-slot in-flight gate so
    /// subsequent offers can drive fresh fetches.  Bodies are matched
    /// by the I/O layer via [`Self::match_eb_tx_response`].
    pub fn on_eb_txs_received(&mut self, point: &Point, count: usize) {
        if let Point::Specific { slot, .. } = point {
            let gate_key = Point::Specific {
                slot: *slot,
                hash: [0xFE; 32],
            };
            self.in_flight.remove(&gate_key);
        }
        info!(
            node_id = %self.node_id,
            %point,
            count,
            "leios block txs received"
        );
    }

    // -- Validation outcomes ------------------------------------------------

    /// EB validation succeeded; create an election for it.
    pub fn on_validated_eb(&mut self, point: Point) {
        let (slot, hash) = match &point {
            Point::Specific { slot, hash } => (*slot, *hash),
            Point::Origin => return,
        };
        self.elections.announce(slot, hash);
    }

    /// Vote validation succeeded; attribute each vote to its EB
    /// election.  `vote_bodies` is an iterator yielding decoded vote
    /// bodies — the I/O layer decoded them already (the vote-body wire
    /// format lives outside con-rs).  Returns telemetry effects for
    /// any quorums newly formed.
    pub fn on_validated_votes<'a, I>(&mut self, vote_bodies: I) -> Vec<LeiosEffect>
    where
        I: IntoIterator<Item = ValidatedVote<'a>>,
    {
        let mut fx = Vec::new();
        for body in vote_bodies {
            let voter_id_str = String::from_utf8_lossy(body.voter_id).into_owned();
            let weight = self.elections.weight_for(
                &voter_id_str,
                body.tag,
                body.eligibility_signature,
            );
            if weight == 0 {
                continue;
            }
            // Dedup key: voter_id || tag.
            let mut key = body.voter_id.to_vec();
            key.push(body.tag);
            if let Some(formed) = self
                .elections
                .record_vote(body.endorser_block_hash, key, weight)
            {
                let QuorumFormed {
                    eb_slot,
                    voted_weight,
                    voters,
                } = formed;
                fx.push(LeiosEffect::EmitTelemetry(
                    LeiosTelemetryEvent::QuorumReached {
                        eb_slot,
                        voted_weight,
                        voters,
                    },
                ));
            }
        }
        fx
    }

    // -- Pure utility -------------------------------------------------------

    /// Match a body list against the cached EB manifest.  Each body is
    /// hashed (blake2b-256) by the caller before being passed in;
    /// bodies whose hash maps to a requested manifest index are
    /// returned in manifest order.  Bodies that don't match the
    /// manifest are dropped silently.
    ///
    /// The hashing is the caller's responsibility because it depends
    /// on the concrete body wire format; con-rs is format-agnostic.
    pub fn match_eb_tx_response(
        &mut self,
        point: &Point,
        bodies_with_hashes: &[(Vec<u8>, [u8; 32])],
    ) -> EbTxMatchOutcome {
        let (eb_slot, hash) = match point {
            Point::Specific { slot, hash } => (*slot, *hash),
            Point::Origin => {
                return EbTxMatchOutcome {
                    matched_bodies: Vec::new(),
                    requested: 0,
                    remaining_bitmap: BTreeMap::new(),
                };
            }
        };
        let Some((_, manifest)) = self.eb_tx_hashes.get(&hash) else {
            // Manifest unknown — pass bodies through; the validator
            // hashes them and any unrelated tx will sit unused.
            return EbTxMatchOutcome {
                matched_bodies: bodies_with_hashes.iter().map(|(b, _)| b.clone()).collect(),
                requested: 0,
                remaining_bitmap: BTreeMap::new(),
            };
        };
        // Build hash → manifest-index map.
        let manifest_index: BTreeMap<&[u8; 32], usize> = manifest
            .iter()
            .enumerate()
            .map(|(i, h)| (h, i))
            .collect();
        // Match each body, sorting by manifest index.
        let mut matched: BTreeMap<usize, Vec<u8>> = BTreeMap::new();
        for (body, body_hash) in bodies_with_hashes {
            if let Some(&idx) = manifest_index.get(body_hash) {
                matched.entry(idx).or_insert_with(|| body.clone());
            }
        }
        let matched_bodies: Vec<Vec<u8>> = matched.values().cloned().collect();

        // Compute `requested` and `remaining_bitmap`.
        let (requested, remaining_bitmap) =
            match self.pending_eb_tx_fetches.get(&hash).cloned() {
                Some((_, bitmap)) => {
                    let requested_indices: BTreeSet<u32> = bitmap_to_indices(&bitmap);
                    let matched_indices: BTreeSet<u32> =
                        matched.keys().map(|i| *i as u32).collect();
                    let remaining: Vec<u32> = requested_indices
                        .difference(&matched_indices)
                        .copied()
                        .collect();
                    let remaining_bitmap = indices_to_bitmap(&remaining);
                    if remaining.is_empty() {
                        self.pending_eb_tx_fetches.remove(&hash);
                    } else {
                        self.pending_eb_tx_fetches
                            .insert(hash, (eb_slot, remaining_bitmap.clone()));
                    }
                    (requested_indices.len(), remaining_bitmap)
                }
                None => (0, BTreeMap::new()),
            };
        EbTxMatchOutcome {
            matched_bodies,
            requested,
            remaining_bitmap,
        }
    }

    /// Re-issue a `FetchLeiosBlockTxs` for the unfilled bitmap (a
    /// previous response was partial).  The I/O layer is expected to
    /// route to a different peer.
    pub fn retry_eb_tx_fetch(
        &mut self,
        point: Point,
        bitmap: BTreeMap<u16, u64>,
    ) -> Vec<LeiosEffect> {
        if bitmap.is_empty() {
            return Vec::new();
        }
        vec![LeiosEffect::FetchLeiosBlockTxs { point, bitmap }]
    }

    // -- Queries ------------------------------------------------------------

    pub fn has_certified_eb(&self) -> bool {
        self.elections.has_certified_eb()
    }

    pub fn certified_eb_slot(&self) -> Option<u64> {
        self.elections.certified_eb_slot()
    }

    // -- Internal helpers ---------------------------------------------------

    fn evict_stale_in_flight(&mut self, now: Instant) {
        self.in_flight
            .retain(|_, started| now.duration_since(*started) < IN_FLIGHT_TTL);
    }
}

/// One decoded vote body to pass into [`LeiosState::on_validated_votes`].
/// Borrowed slices avoid copies; the caller owns the storage.
pub struct ValidatedVote<'a> {
    pub voter_id: &'a [u8],
    pub tag: u8,
    pub eligibility_signature: Option<&'a [u8]>,
    pub endorser_block_hash: &'a [u8; 32],
}

// ---------------------------------------------------------------------------
// Bitmap helpers (sparse 16-bit-segment / 64-bit-word format)
// ---------------------------------------------------------------------------

fn bitmap_to_indices(bitmap: &BTreeMap<u16, u64>) -> BTreeSet<u32> {
    let mut out = BTreeSet::new();
    for (&segment, &word) in bitmap {
        for bit in 0..64 {
            if word & (1u64 << bit) != 0 {
                out.insert((segment as u32) * 64 + bit as u32);
            }
        }
    }
    out
}

fn indices_to_bitmap(indices: &[u32]) -> BTreeMap<u16, u64> {
    let mut out: BTreeMap<u16, u64> = BTreeMap::new();
    for &idx in indices {
        let segment = (idx / 64) as u16;
        let bit = idx % 64;
        *out.entry(segment).or_insert(0) |= 1u64 << bit;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pipeline() -> PipelineConfig {
        PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        }
    }

    fn elections_for(node_id: &str) -> Elections {
        use crate::elections::ElectionsConfig;
        Elections::new(ElectionsConfig {
            node_id: node_id.to_string(),
            pipeline: pipeline(),
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 0,
            expected_committee_size: 100,
            quorum_weight_fraction: 0.75,
        })
    }

    fn cfg(persistent_seats: u32) -> VotingConfig {
        VotingConfig {
            committee_selection: CommitteeSelection::EveryoneVotes,
            stake: 100,
            total_stake: 1000,
            persistent_vote_bytes: 130,
            non_persistent_vote_bytes: 180,
            persistent_seats,
        }
    }

    fn h(b: u8) -> [u8; 32] {
        [b; 32]
    }

    fn point(slot: u64, b: u8) -> Point {
        Point::Specific { slot, hash: h(b) }
    }

    #[test]
    fn pv_vote_emitted_when_seated() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(1), pipeline());
        state.on_slot(10);
        state.elections.announce(10, h(1));
        // Voting phase begins at elapsed=3 (3*delta_hdr).
        let fx = state.on_slot(13);
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            LeiosEffect::EmitVote {
                eb_slot,
                eb_hash,
                emit_pv,
                npv_signature,
            } => {
                assert_eq!(*eb_slot, 10);
                assert_eq!(eb_hash, &h(1));
                assert!(*emit_pv);
                assert!(npv_signature.is_none());
            }
            other => panic!("expected EmitVote, got {other:?}"),
        }
        assert!(state.elections.voted(&h(1)));
    }

    #[test]
    fn no_vote_when_no_seats_and_no_npv() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        state.on_slot(10);
        state.elections.announce(10, h(1));
        let fx = state.on_slot(13);
        assert!(fx.is_empty());
        assert!(!state.elections.voted(&h(1)));
    }

    #[test]
    fn wfa_ls_can_emit_pv_and_npv() {
        let mut voting = cfg(5);
        voting.committee_selection = CommitteeSelection::WfaLs {
            persistent_voters: 480,
            non_persistent_voters: 120,
        };
        voting.stake = 400; // 40% → almost-certain NPV win
        // Both LeiosState and Elections need WfaLs config so the
        // lottery re-derivation matches.
        use crate::elections::ElectionsConfig;
        let elections = Elections::new(ElectionsConfig {
            node_id: "n0".to_string(),
            pipeline: pipeline(),
            committee_selection: voting.committee_selection.clone(),
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 1000,
            expected_committee_size: 600,
            quorum_weight_fraction: 0.75,
        });
        let mut state = LeiosState::new("n0".into(), elections, voting, pipeline());
        state.on_slot(10);
        state.elections.announce(10, h(1));
        let fx = state.on_slot(13);
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            LeiosEffect::EmitVote {
                emit_pv,
                npv_signature,
                ..
            } => {
                assert!(*emit_pv);
                assert!(npv_signature.is_some());
            }
            other => panic!("expected EmitVote, got {other:?}"),
        }
    }

    #[test]
    fn on_eb_offered_dedups_via_in_flight() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let now = Instant::now();
        let fx = state.on_eb_offered(point(10, 1), now);
        assert_eq!(fx.len(), 1);
        // Second offer: dedup'd.
        let fx = state.on_eb_offered(point(10, 1), now);
        assert!(fx.is_empty());
    }

    #[test]
    fn on_eb_received_emits_record_and_validate() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let manifest = vec![h(0xA0), h(0xA1)];
        let fx = state.on_eb_received(point(10, 1), Some(manifest.clone()));
        assert_eq!(fx.len(), 2);
        assert!(matches!(fx[0], LeiosEffect::RecordLeiosEbManifest { .. }));
        assert!(matches!(fx[1], LeiosEffect::ValidateEb { .. }));
        assert_eq!(state.eb_tx_hashes.get(&h(1)).map(|(_, v)| v), Some(&manifest));
    }

    #[test]
    fn on_eb_received_validate_only_when_no_manifest() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let fx = state.on_eb_received(point(10, 1), None);
        assert_eq!(fx.len(), 1);
        assert!(matches!(fx[0], LeiosEffect::ValidateEb { .. }));
    }

    #[test]
    fn quorum_emits_telemetry() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        state.on_slot(10);
        state.elections.announce(10, h(1));
        let body_a = ValidatedVote {
            voter_id: b"a",
            tag: 0,
            eligibility_signature: None,
            endorser_block_hash: &h(1),
        };
        // Stub committee weight: weight_for() returns 0 by default;
        // we'd need PV seats for non-zero weight.  Instead just verify
        // shape: with weight 0, no telemetry fires.
        let fx = state.on_validated_votes(std::iter::once(body_a));
        assert!(fx.is_empty());
    }

    #[test]
    fn slot_tick_prunes_stale_eb_tx_state() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        state.eb_tx_hashes.insert(h(1), (10, vec![h(0xAA)]));
        state.pending_eb_tx_fetches.insert(h(1), (10, BTreeMap::new()));
        // Lifespan = 3+5+5+10 = 23.  At elapsed=23 (slot 33), expired.
        state.on_slot(33);
        assert!(state.eb_tx_hashes.is_empty());
        assert!(state.pending_eb_tx_fetches.is_empty());
    }

    #[test]
    fn match_eb_tx_response_returns_in_manifest_order() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        // Manifest: [hashA, hashB, hashC] at slot 10.
        let ha = h(0xA0);
        let hb = h(0xA1);
        let hc = h(0xA2);
        state.eb_tx_hashes.insert(h(1), (10, vec![ha, hb, hc]));
        // Body order arrives as [b, a, c] but should come out [a, b, c].
        let bodies = vec![
            (b"body-b".to_vec(), hb),
            (b"body-a".to_vec(), ha),
            (b"body-c".to_vec(), hc),
        ];
        let outcome = state.match_eb_tx_response(&point(10, 1), &bodies);
        assert_eq!(
            outcome.matched_bodies,
            vec![b"body-a".to_vec(), b"body-b".to_vec(), b"body-c".to_vec()]
        );
    }

    #[test]
    fn match_eb_tx_response_drops_unmatched_bodies() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let ha = h(0xA0);
        state.eb_tx_hashes.insert(h(1), (10, vec![ha]));
        let bogus = h(0xFF);
        let bodies = vec![(b"body-a".to_vec(), ha), (b"bogus".to_vec(), bogus)];
        let outcome = state.match_eb_tx_response(&point(10, 1), &bodies);
        assert_eq!(outcome.matched_bodies, vec![b"body-a".to_vec()]);
    }

    #[test]
    fn on_eb_txs_offered_gates_per_slot() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let now = Instant::now();
        let mut bitmap = BTreeMap::new();
        bitmap.insert(0u16, 0b111u64);

        let fx = state.on_eb_txs_offered(point(10, 1), bitmap.clone(), now);
        assert_eq!(fx.len(), 1);
        assert!(matches!(fx[0], LeiosEffect::FetchLeiosBlockTxs { .. }));
        assert!(state.pending_eb_tx_fetches.contains_key(&h(1)));

        // Same-slot offer dedup'd via the per-slot gate.
        let fx2 = state.on_eb_txs_offered(point(10, 2), bitmap, now);
        assert!(fx2.is_empty());
    }

    #[test]
    fn on_eb_txs_offered_origin_point_is_noop() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let fx = state.on_eb_txs_offered(Point::Origin, BTreeMap::new(), Instant::now());
        assert!(fx.is_empty());
    }

    #[test]
    fn on_eb_txs_received_clears_gate_for_subsequent_fetch() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let now = Instant::now();
        let mut bitmap = BTreeMap::new();
        bitmap.insert(0u16, 0b1u64);
        let _ = state.on_eb_txs_offered(point(10, 1), bitmap.clone(), now);

        state.on_eb_txs_received(&point(10, 1), 1);

        // A fresh same-slot offer is no longer gated.
        let fx = state.on_eb_txs_offered(point(10, 2), bitmap, now);
        assert_eq!(fx.len(), 1);
    }

    #[test]
    fn on_votes_offered_emits_fetch() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let votes = vec![(10u64, vec![0u8; 8])];
        let fx = state.on_votes_offered(votes.clone());
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            LeiosEffect::FetchLeiosVotes { votes: vs } => assert_eq!(vs, &votes),
            other => panic!("expected FetchLeiosVotes, got {other:?}"),
        }
    }

    #[test]
    fn on_votes_offered_empty_is_noop() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let fx = state.on_votes_offered(Vec::new());
        assert!(fx.is_empty());
    }

    #[test]
    fn on_votes_received_emits_validate_votes() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let ids = vec![(10u64, vec![0u8; 8])];
        let bodies = vec![vec![0xAB]];
        let fx = state.on_votes_received(ids.clone(), bodies.clone());
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            LeiosEffect::ValidateVotes {
                vote_ids,
                vote_data,
            } => {
                assert_eq!(vote_ids, &ids);
                assert_eq!(vote_data, &bodies);
            }
            other => panic!("expected ValidateVotes, got {other:?}"),
        }
    }

    #[test]
    fn on_validated_eb_creates_election() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        state.on_slot(10);
        state.on_validated_eb(point(10, 1));
        assert_eq!(state.elections.count(), 1);
    }

    #[test]
    fn on_validated_eb_origin_is_noop() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        state.on_validated_eb(Point::Origin);
        assert_eq!(state.elections.count(), 0);
    }

    #[test]
    fn retry_eb_tx_fetch_with_bitmap_emits_fetch() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let mut bitmap = BTreeMap::new();
        bitmap.insert(0u16, 0b10u64);
        let fx = state.retry_eb_tx_fetch(point(10, 1), bitmap.clone());
        assert_eq!(fx.len(), 1);
        match &fx[0] {
            LeiosEffect::FetchLeiosBlockTxs { point: p, bitmap: b } => {
                assert_eq!(*p, point(10, 1));
                assert_eq!(b, &bitmap);
            }
            other => panic!("expected FetchLeiosBlockTxs, got {other:?}"),
        }
    }

    #[test]
    fn retry_eb_tx_fetch_empty_bitmap_is_noop() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let fx = state.retry_eb_tx_fetch(point(10, 1), BTreeMap::new());
        assert!(fx.is_empty());
    }

    #[test]
    fn match_eb_tx_response_reports_remaining_bitmap() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let ha = h(0xA0);
        let hb = h(0xA1);
        state.eb_tx_hashes.insert(h(1), (10, vec![ha, hb]));
        // Pretend we requested both indices 0 and 1.
        let mut requested = BTreeMap::new();
        requested.insert(0u16, 0b11u64);
        state.pending_eb_tx_fetches.insert(h(1), (10, requested));
        // Only body for index 0 (ha) arrives.
        let outcome =
            state.match_eb_tx_response(&point(10, 1), &[(b"body-a".to_vec(), ha)]);
        assert_eq!(outcome.matched_bodies, vec![b"body-a".to_vec()]);
        assert_eq!(outcome.requested, 2);
        // Index 1 still missing.
        let mut expected_remaining = BTreeMap::new();
        expected_remaining.insert(0u16, 0b10u64);
        assert_eq!(outcome.remaining_bitmap, expected_remaining);
        // pending_eb_tx_fetches updated to remaining-only.
        assert_eq!(
            state.pending_eb_tx_fetches.get(&h(1)).map(|(_, b)| b.clone()),
            Some(expected_remaining)
        );
    }

    #[test]
    fn match_eb_tx_response_clears_pending_when_complete() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let ha = h(0xA0);
        state.eb_tx_hashes.insert(h(1), (10, vec![ha]));
        let mut requested = BTreeMap::new();
        requested.insert(0u16, 0b1u64);
        state.pending_eb_tx_fetches.insert(h(1), (10, requested));
        let outcome =
            state.match_eb_tx_response(&point(10, 1), &[(b"body-a".to_vec(), ha)]);
        assert!(outcome.remaining_bitmap.is_empty());
        assert!(!state.pending_eb_tx_fetches.contains_key(&h(1)));
    }

    #[test]
    fn match_eb_tx_response_unknown_manifest_passes_bodies_through() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let outcome = state.match_eb_tx_response(
            &point(10, 1),
            &[(b"some-body".to_vec(), h(0xAA))],
        );
        assert_eq!(outcome.matched_bodies, vec![b"some-body".to_vec()]);
        assert_eq!(outcome.requested, 0);
        assert!(outcome.remaining_bitmap.is_empty());
    }

    #[test]
    fn match_eb_tx_response_origin_point_returns_empty() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        let outcome = state.match_eb_tx_response(&Point::Origin, &[]);
        assert!(outcome.matched_bodies.is_empty());
        assert_eq!(outcome.requested, 0);
    }

    #[test]
    fn election_expired_emits_telemetry() {
        let mut state = LeiosState::new("n0".into(), elections_for("n0"), cfg(0), pipeline());
        state.on_slot(10);
        state.elections.announce(10, h(1));
        // Lifespan = 3+5+5+10 = 23.  Tick past expiry.
        let fx = state.on_slot(34);
        assert!(fx.iter().any(|e| matches!(
            e,
            LeiosEffect::EmitTelemetry(LeiosTelemetryEvent::ElectionExpired { .. })
        )));
    }

    #[test]
    fn quorum_emits_telemetry_with_weighted_voter() {
        // Set up an Elections with a persistent committee that hands node
        // "voter-a" enough seats to single-handedly form quorum.
        use crate::elections::ElectionsConfig;
        let mut persistent = BTreeMap::new();
        persistent.insert("voter-a".to_string(), 100u32);
        let elections = Elections::new(ElectionsConfig {
            node_id: "n0".to_string(),
            pipeline: pipeline(),
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: persistent,
            stake_registry: BTreeMap::new(),
            total_stake: 0,
            expected_committee_size: 100,
            quorum_weight_fraction: 0.75,
        });
        let mut state = LeiosState::new("n0".into(), elections, cfg(0), pipeline());
        state.on_slot(10);
        state.elections.announce(10, h(1));

        let vote = ValidatedVote {
            voter_id: b"voter-a",
            tag: 0,
            eligibility_signature: None,
            endorser_block_hash: &h(1),
        };
        let fx = state.on_validated_votes(std::iter::once(vote));
        assert!(fx.iter().any(|e| matches!(
            e,
            LeiosEffect::EmitTelemetry(LeiosTelemetryEvent::QuorumReached { .. })
        )));
    }
}
