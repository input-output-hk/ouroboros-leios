//! EB election state machine.
//!
//! Sans-IO. Owns the per-EB election state. The caller (typically a
//! node's leios layer) feeds slot ticks and incoming votes; the machine
//! emits `SlotEffect`s describing what the I/O layer should do — cast a
//! vote, expire caches.
//!
//! All iteration is over `BTreeMap`s, so given a deterministic input
//! ordering at the I/O boundary, this module produces deterministic
//! state mutations and a deterministic effect sequence — needed by
//! consumers that replay runs from a seed.

use std::collections::BTreeMap;

use tracing::info;

use crate::aggregation::{self, hex_prefix, QuorumFormed};
use crate::config::CommitteeSelection;
use crate::pipeline::{EbElection, PipelineConfig, PipelinePhase};
use crate::committee;

/// What the caller should do as a result of a slot tick.
///
/// Effects are returned in deterministic order: all `EligibleToVote`
/// first (sorted by `eb_hash`), then all `Expired` (also sorted).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlotEffect {
    /// The local node is in the Voting window for this EB and has not
    /// yet voted. Caller should compute its vote, send it to the network,
    /// then call `mark_voted(eb_hash)` to suppress further re-emission.
    /// `eb_seen_slot` is the slot at which this node first learned of the
    /// EB, carried so the caller can apply the CIP-0164 `LateEB` predicate
    /// without an extra accessor.
    EligibleToVote {
        eb_hash: [u8; 32],
        eb_slot: u64,
        eb_seen_slot: u64,
    },
    /// Election expired (past `dedup_window` slots after CertEligible).
    /// Caller may want to clean associated transient state — for
    /// example, EB tx manifests and in-flight tx-fetch entries keyed
    /// by this hash.
    Expired {
        eb_hash: [u8; 32],
        eb_slot: u64,
        had_quorum: bool,
        voted_weight: u64,
        voters: usize,
    },
}

/// Returned by [`ElectionsConfig::validate`] for invariant violations
/// callers want to surface at startup rather than at quorum-check time.
#[derive(Debug, PartialEq)]
pub enum ElectionsConfigError {
    /// CIP-164 PR #1196 requires the committee to cover strictly more
    /// stake than quorum demands.  At `top_centile_of_stake ≤
    /// quorum_weight_fraction`, even unanimous participation by the
    /// committee cannot satisfy the quorum and certification is
    /// unreachable.
    StakeCentileQuorumUnreachable { sigma_c: f64, tau: f64 },
}

impl std::fmt::Display for ElectionsConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StakeCentileQuorumUnreachable { sigma_c, tau } => write!(
                f,
                "stake-centile committee must cover more stake than the quorum fraction \
                 (σ_c={sigma_c} ≤ τ={tau})"
            ),
        }
    }
}

impl std::error::Error for ElectionsConfigError {}

/// Configuration for an `Elections` instance.
pub struct ElectionsConfig {
    pub node_id: String,
    pub pipeline: PipelineConfig,
    pub committee_selection: CommitteeSelection,
    /// Per-pool persistent committee allocation, identical on every node
    /// (computed via `committee::build_committee` at startup).
    pub persistent_committee: BTreeMap<String, u32>,
    /// Network-wide stake registry, used to re-run the NPV lottery for
    /// incoming non-persistent votes.
    pub stake_registry: BTreeMap<String, u64>,
    pub total_stake: u64,
    /// Quorum denominator in the same units the aggregator sums
    /// per-voter weights — seats for `WfaLs`, node count for
    /// `EveryoneVotes`, total active stake for `StakeCentile`.
    /// Compute via [`committee::expected_total_weight`].
    pub expected_total_weight: u64,
    /// Fraction of expected total weight required for quorum
    /// (e.g. 0.75 = 75%).
    pub quorum_weight_fraction: f64,
}

impl ElectionsConfig {
    /// Reject configurations that are guaranteed to fail at
    /// quorum-check time.  Production callers (the sim adapter,
    /// real-node bootstrap) invoke this before [`Elections::new`];
    /// test fixtures may construct `Elections` directly when the
    /// scenario only exercises code below the quorum step.
    pub fn validate(&self) -> Result<(), ElectionsConfigError> {
        if let CommitteeSelection::StakeCentile {
            top_centile_of_stake,
        } = self.committee_selection
        {
            if top_centile_of_stake <= self.quorum_weight_fraction {
                return Err(ElectionsConfigError::StakeCentileQuorumUnreachable {
                    sigma_c: top_centile_of_stake,
                    tau: self.quorum_weight_fraction,
                });
            }
        }
        Ok(())
    }
}

pub struct Elections {
    cfg: ElectionsConfig,
    current_slot: u64,
    elections: BTreeMap<[u8; 32], EbElection>,
}

impl Elections {
    pub fn new(cfg: ElectionsConfig) -> Self {
        Self {
            cfg,
            current_slot: 0,
            elections: BTreeMap::new(),
        }
    }

    pub fn current_slot(&self) -> u64 {
        self.current_slot
    }

    pub fn count(&self) -> usize {
        self.elections.len()
    }

    /// Mark an election as locally-body-validated.  If an election
    /// already exists for `eb_hash` (e.g., as a vote-placeholder
    /// created by `record_vote`), flips `body_validated_locally` to
    /// true and preserves accumulated votes.  Otherwise creates a
    /// fresh election with the flag set.  Returns `true` iff a new
    /// election was inserted; `false` if a placeholder was upgraded or
    /// the EB is already past its pipeline lifetime relative to
    /// `current_slot`.
    pub fn announce(&mut self, eb_slot: u64, eb_hash: [u8; 32]) -> bool {
        if let Some(existing) = self.elections.get_mut(&eb_hash) {
            existing.body_validated_locally = true;
            return false;
        }
        let elapsed = self.current_slot.saturating_sub(eb_slot);
        let phase = self.cfg.pipeline.phase_for_elapsed(elapsed);
        info!(
            node_id = %self.cfg.node_id,
            eb_slot,
            eb_hash = %hex_prefix(&eb_hash),
            ?phase,
            "eb election created"
        );
        self.elections.insert(
            eb_hash,
            EbElection {
                announced_slot: eb_slot,
                phase,
                seen_slot: self.current_slot,
                voted: false,
                voter_weights: BTreeMap::new(),
                quorum_reached: false,
                body_validated_locally: true,
            },
        );
        true
    }

    /// Advance the slot counter, update phases, and emit effects.
    ///
    /// Effect ordering: every `EligibleToVote` (sorted by eb_hash) first,
    /// then every `Expired` (sorted). Callers iterate in order; this is
    /// the contract deterministic-replay consumers rely on.
    pub fn on_slot(&mut self, slot: u64) -> Vec<SlotEffect> {
        self.current_slot = slot;
        let pipeline = self.cfg.pipeline;
        let mut effects: Vec<SlotEffect> = Vec::new();

        // Pass 1: collect EligibleToVote in BTreeMap order.
        for (hash, election) in &self.elections {
            let elapsed = slot.saturating_sub(election.announced_slot);
            if pipeline.phase_for_elapsed(elapsed) == PipelinePhase::Voting && !election.voted
            {
                effects.push(SlotEffect::EligibleToVote {
                    eb_hash: *hash,
                    eb_slot: election.announced_slot,
                    eb_seen_slot: election.seen_slot,
                });
            }
        }

        // Pass 2: refresh phase on every election.  No time-based
        // expiry: under the strict parent-only cert rule, an EB stays
        // CertEligible for as long as it's the chain tip's
        // announcement.  Lifetime is governed exclusively by the
        // chain-progress prune in [`crate::leios::LeiosState::on_slot`]
        // (via [`Self::prune_below_slot`]), not by elapsed slots.
        for election in self.elections.values_mut() {
            election.phase = pipeline
                .phase_for_elapsed(slot.saturating_sub(election.announced_slot));
        }
        effects
    }

    /// Caller invokes after a vote message for `eb_hash` was successfully
    /// emitted to the network, to suppress further `EligibleToVote`
    /// effects for this election.
    pub fn mark_voted(&mut self, eb_hash: &[u8; 32]) {
        if let Some(e) = self.elections.get_mut(eb_hash) {
            e.voted = true;
        }
    }

    /// Record a vote received for an EB. The caller decoded the vote
    /// body and computed the weight (typically via `weight_for`).
    /// Returns `Some(QuorumFormed)` exactly once per election.  If
    /// the election doesn't exist yet, a vote-placeholder is created
    /// at `eb_slot` (see [`aggregation::record_vote`] for the
    /// CIP-0164 rationale).
    pub fn record_vote(
        &mut self,
        eb_hash: &[u8; 32],
        eb_slot: u64,
        voter_key: Vec<u8>,
        weight: u64,
    ) -> Option<QuorumFormed> {
        aggregation::record_vote(
            &mut self.elections,
            eb_hash,
            eb_slot,
            voter_key,
            weight,
            self.cfg.quorum_weight_fraction,
            self.cfg.expected_total_weight,
            self.current_slot,
            self.cfg.pipeline,
            &self.cfg.node_id,
        )
    }

    /// Derive the weight to attribute to a decoded vote body, in the
    /// units `expected_total_weight` is denominated in for this
    /// committee mode.
    ///
    /// - `tag == 0` (PV) under `WfaLs`/`EveryoneVotes`: the voter's
    ///   persistent-committee seat count (`0` if not seated).
    /// - `tag == 0` (PV) under `StakeCentile` (CIP-164 PR #1196):
    ///   the voter's stake from the registry, but only if it is on
    ///   the deterministic committee (otherwise `0`).  The quorum
    ///   denominator is total active stake, so each member contributes
    ///   its own stake.
    /// - `tag == 1` (NPV) under `WfaLs`: re-runs the NPV lottery from
    ///   the embedded eligibility signature and the voter's stake.  If
    ///   the voter *also* holds a persistent seat, returns `0` —
    ///   CIP-0164 partitions persistent (indices `[1, n₁]`) and
    ///   non-persistent candidate (`[i*, |P|]`) pools disjointly, so a
    ///   verified NPV signature from a persistent-seated voter is
    ///   spec-violating and must not contribute weight.
    /// - NPV tag under non-`WfaLs` modes (no NPV phase), or any other
    ///   tag, or NPV without a signature: `0`.
    pub fn weight_for(&self, voter_id: &str, tag: u8, npv_signature: Option<&[u8]>) -> u64 {
        match (tag, npv_signature, &self.cfg.committee_selection) {
            (0, _, CommitteeSelection::StakeCentile { .. }) => {
                if self.cfg.persistent_committee.contains_key(voter_id) {
                    self.cfg
                        .stake_registry
                        .get(voter_id)
                        .copied()
                        .unwrap_or(0)
                } else {
                    0
                }
            }
            (0, _, _) => self
                .cfg
                .persistent_committee
                .get(voter_id)
                .copied()
                .map(u64::from)
                .unwrap_or(0),
            (1, Some(sig), CommitteeSelection::WfaLs { .. }) => {
                if self.cfg.persistent_committee.contains_key(voter_id) {
                    return 0;
                }
                let stake = self
                    .cfg
                    .stake_registry
                    .get(voter_id)
                    .copied()
                    .unwrap_or(0);
                committee::count_npv_wins(
                    sig,
                    stake,
                    self.cfg.total_stake,
                    self.cfg.committee_selection.non_persistent_voters(),
                ) as u64
            }
            _ => 0,
        }
    }

    /// Resolve a compact voter index to its registered node id.
    ///
    /// The index is a pool's position in the network stake registry
    /// (sorted by node id — `BTreeMap` key order), identical on every
    /// node that shares the same registry.  Returns `None` for an index
    /// outside the local registry (e.g. a foreign voter from an external
    /// relay we hold no stake entry for — its votes gossip but carry no
    /// resolvable weight).
    pub fn voter_id_at(&self, index: u16) -> Option<&str> {
        self.cfg
            .stake_registry
            .keys()
            .nth(index as usize)
            .map(String::as_str)
    }

    /// The compact voter index for a registered node id, if present.
    pub fn voter_index(&self, node_id: &str) -> Option<u16> {
        self.cfg
            .stake_registry
            .keys()
            .position(|k| k == node_id)
            .and_then(|p| u16::try_from(p).ok())
    }

    pub fn phase(&self, eb_hash: &[u8; 32]) -> Option<PipelinePhase> {
        self.elections.get(eb_hash).map(|e| e.phase)
    }

    /// Mutable access to a live election. Adapters use this to fix up
    /// per-EB state the announce path couldn't capture (e.g., a more
    /// precise `seen_slot` from the network layer's per-message timing).
    pub fn election_mut(&mut self, eb_hash: &[u8; 32]) -> Option<&mut EbElection> {
        self.elections.get_mut(eb_hash)
    }

    pub fn voted(&self, eb_hash: &[u8; 32]) -> bool {
        self.elections
            .get(eb_hash)
            .map(|e| e.voted)
            .unwrap_or(false)
    }

    /// True iff the EB body has been locally validated (the
    /// producer-side EB-safety gate's "I have the closure" predicate).
    /// A vote-placeholder election exists when only votes have been
    /// observed; this query returns false for that case so the gate
    /// fires when the producer holds a cert for an EB whose body has
    /// not been validated locally.
    pub fn is_announced(&self, eb_hash: &[u8; 32]) -> bool {
        self.elections
            .get(eb_hash)
            .map(|e| e.body_validated_locally)
            .unwrap_or(false)
    }

    pub fn quorum(&self, eb_hash: &[u8; 32]) -> bool {
        self.elections
            .get(eb_hash)
            .map(|e| e.quorum_reached)
            .unwrap_or(false)
    }

    pub fn voter_count(&self, eb_hash: &[u8; 32]) -> usize {
        self.elections
            .get(eb_hash)
            .map(|e| e.voter_weights.len())
            .unwrap_or(0)
    }

    /// Drop every election with `announced_slot < min_slot`.  Used by
    /// the chain-progress prune in [`crate::leios::LeiosState::on_slot`]:
    /// under the strict parent-only cert rule, an EB whose announcing
    /// RB is no longer the chain tip is permanently dead, and its
    /// election state is dead weight.
    pub fn prune_below_slot(&mut self, min_slot: u64) {
        self.elections
            .retain(|_, e| e.announced_slot >= min_slot);
    }

    /// Slot of the EB at `eb_hash` if it is both at quorum and
    /// CertEligible — the only state in which a producer can attach a
    /// cert for it.  Linear Leios requires the cert to target the EB
    /// announced by the parent RB specifically (see
    /// [`crate::chain_tree::ChainTree::announced_eb_hash_by`]); the
    /// producer threads the parent RB's announced EB hash through this
    /// method to decide whether to set the `certified_eb` header bit.
    pub fn eb_certifiable_slot(&self, eb_hash: &[u8; 32]) -> Option<u64> {
        let e = self.elections.get(eb_hash)?;
        if e.quorum_reached && e.phase == PipelinePhase::CertEligible {
            Some(e.announced_slot)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_pipeline() -> PipelineConfig {
        PipelineConfig {
            delta_hdr: 1,
            vote_window: 5,
            diffuse_window: 5,
            dedup_window: 10,
        }
    }

    fn test_elections() -> Elections {
        Elections::new(ElectionsConfig {
            node_id: "test".to_string(),
            pipeline: test_pipeline(),
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 0,
            expected_total_weight: 100,
            quorum_weight_fraction: 0.75,
        })
    }

    fn h(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    #[test]
    fn voter_index_round_trips_in_registry_order() {
        let mut registry = BTreeMap::new();
        // Insertion order differs from sorted order on purpose.
        registry.insert("pool-c".to_string(), 10u64);
        registry.insert("pool-a".to_string(), 30u64);
        registry.insert("pool-b".to_string(), 20u64);
        let e = Elections::new(ElectionsConfig {
            node_id: "pool-a".to_string(),
            pipeline: test_pipeline(),
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: BTreeMap::new(),
            stake_registry: registry,
            total_stake: 60,
            expected_total_weight: 3,
            quorum_weight_fraction: 0.75,
        });
        // BTreeMap key order: pool-a=0, pool-b=1, pool-c=2.
        assert_eq!(e.voter_index("pool-a"), Some(0));
        assert_eq!(e.voter_index("pool-b"), Some(1));
        assert_eq!(e.voter_index("pool-c"), Some(2));
        assert_eq!(e.voter_id_at(0), Some("pool-a"));
        assert_eq!(e.voter_id_at(2), Some("pool-c"));
        // Out-of-range / unregistered.
        assert_eq!(e.voter_id_at(3), None);
        assert_eq!(e.voter_index("pool-z"), None);
    }

    #[test]
    fn announce_creates_election() {
        let mut e = test_elections();
        e.on_slot(10);
        assert!(e.announce(10, h(1)));
        assert_eq!(e.count(), 1);
        assert_eq!(e.phase(&h(1)), Some(PipelinePhase::EquivocationCheck));
    }

    #[test]
    fn duplicate_announce_returns_false() {
        let mut e = test_elections();
        e.on_slot(10);
        assert!(e.announce(10, h(1)));
        assert!(!e.announce(10, h(1)));
        assert_eq!(e.count(), 1);
    }

    #[test]
    fn on_slot_emits_eligible_to_vote_in_voting_phase() {
        let mut e = test_elections();
        e.on_slot(10);
        e.announce(10, h(1));
        // EquivocationCheck is [0, 3): nothing.
        let fx = e.on_slot(11);
        assert!(fx.is_empty());
        // Voting starts at elapsed=3.
        let fx = e.on_slot(13);
        assert_eq!(
            fx,
            vec![SlotEffect::EligibleToVote {
                eb_hash: h(1),
                eb_slot: 10,
                eb_seen_slot: 10,
            }]
        );
    }

    #[test]
    fn mark_voted_suppresses_repeat_eligible_to_vote() {
        let mut e = test_elections();
        e.on_slot(10);
        e.announce(10, h(1));
        let fx = e.on_slot(13);
        assert_eq!(fx.len(), 1);
        e.mark_voted(&h(1));
        let fx = e.on_slot(14);
        assert!(fx.is_empty());
    }

    #[test]
    fn prune_below_slot_drops_old_elections() {
        // Chain-progress prune: drop elections at slot < min_keep.
        let mut e = test_elections();
        e.on_slot(10);
        e.announce(10, h(1));
        e.announce(15, h(2));
        e.announce(20, h(3));
        assert_eq!(e.count(), 3);
        e.prune_below_slot(15);
        assert_eq!(e.count(), 2);
        assert!(e.phase(&h(1)).is_none());
        assert!(e.phase(&h(2)).is_some());
        assert!(e.phase(&h(3)).is_some());
    }

    #[test]
    fn effects_are_in_btreemap_order() {
        let mut e = test_elections();
        e.on_slot(10);
        // Announce out of order; effects should still come out sorted.
        e.announce(10, h(3));
        e.announce(10, h(1));
        e.announce(10, h(2));
        let fx = e.on_slot(13);
        assert_eq!(fx.len(), 3);
        let hashes: Vec<[u8; 32]> = fx
            .into_iter()
            .map(|f| match f {
                SlotEffect::EligibleToVote { eb_hash, .. } => eb_hash,
                _ => panic!("unexpected effect"),
            })
            .collect();
        assert_eq!(hashes, vec![h(1), h(2), h(3)]);
    }

    #[test]
    fn record_vote_fires_quorum_then_advances_to_certifiable() {
        let mut e = test_elections();
        e.on_slot(10);
        e.announce(10, h(1));
        // 75% × 100 = 75. Two voters of weight 40 each cross 75.
        assert!(e.record_vote(&h(1), 10, b"a".to_vec(), 40).is_none());
        assert!(e.record_vote(&h(1), 10, b"b".to_vec(), 40).is_some());
        assert!(e.quorum(&h(1)));
        // After Voting+Diffusing windows, phase should be CertEligible.
        e.on_slot(23);
        assert_eq!(e.phase(&h(1)), Some(PipelinePhase::CertEligible));
        assert_eq!(e.eb_certifiable_slot(&h(1)), Some(10));
        // Different hash → no cert.
        assert_eq!(e.eb_certifiable_slot(&h(2)), None);
    }

    #[test]
    fn weight_for_pv_looks_up_committee() {
        let mut cfg = ElectionsConfig {
            node_id: "test".to_string(),
            pipeline: test_pipeline(),
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 0,
            expected_total_weight: 100,
            quorum_weight_fraction: 0.75,
        };
        cfg.persistent_committee.insert("pool-a".to_string(), 5);
        let e = Elections::new(cfg);
        assert_eq!(e.weight_for("pool-a", 0, None), 5);
        assert_eq!(e.weight_for("unknown", 0, None), 0);
    }

    #[test]
    fn weight_for_npv_zero_when_not_wfa_ls() {
        // EveryoneVotes has non_persistent_voters() == 0, so any NPV
        // body produces zero weight regardless of stake.
        let mut cfg = ElectionsConfig {
            node_id: "test".to_string(),
            pipeline: test_pipeline(),
            committee_selection: CommitteeSelection::EveryoneVotes,
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 1000,
            expected_total_weight: 100,
            quorum_weight_fraction: 0.75,
        };
        cfg.stake_registry.insert("pool-a".to_string(), 500);
        let e = Elections::new(cfg);
        let sig = committee::npv_eligibility_signature(b"pool-a", &h(0xAB), 1);
        assert_eq!(e.weight_for("pool-a", 1, Some(&sig)), 0);
    }

    /// CIP-164 PR #1196 invariant: a stake-centile committee that
    /// covers less stake than the quorum demands cannot produce a
    /// certificate even with unanimous participation.  Reject at
    /// startup rather than at quorum-check time.
    #[test]
    fn validate_rejects_stake_centile_when_sigma_c_le_tau() {
        let cfg = ElectionsConfig {
            node_id: "test".to_string(),
            pipeline: test_pipeline(),
            committee_selection: CommitteeSelection::StakeCentile {
                top_centile_of_stake: 0.75,
            },
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 1_000_000,
            expected_total_weight: 1_000_000,
            quorum_weight_fraction: 0.80,
        };
        assert_eq!(
            cfg.validate(),
            Err(ElectionsConfigError::StakeCentileQuorumUnreachable {
                sigma_c: 0.75,
                tau: 0.80,
            })
        );
    }

    /// Equality (σ_c == τ) is also rejected — at the boundary the
    /// committee can only just meet quorum if every member votes, and
    /// CIP-164 PR #1196 requires strict inequality.
    #[test]
    fn validate_rejects_stake_centile_at_boundary() {
        let cfg = ElectionsConfig {
            node_id: "test".to_string(),
            pipeline: test_pipeline(),
            committee_selection: CommitteeSelection::StakeCentile {
                top_centile_of_stake: 0.75,
            },
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 1_000_000,
            expected_total_weight: 1_000_000,
            quorum_weight_fraction: 0.75,
        };
        assert!(cfg.validate().is_err());
    }

    /// σ_c > τ passes — and the check is StakeCentile-only.
    #[test]
    fn validate_accepts_stake_centile_when_sigma_c_gt_tau() {
        let cfg = ElectionsConfig {
            node_id: "test".to_string(),
            pipeline: test_pipeline(),
            committee_selection: CommitteeSelection::StakeCentile {
                top_centile_of_stake: 0.95,
            },
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 1_000_000,
            expected_total_weight: 1_000_000,
            quorum_weight_fraction: 0.75,
        };
        assert!(cfg.validate().is_ok());
    }

    #[test]
    fn validate_ignores_wfa_ls_quorum_relationship() {
        // WfaLs doesn't carry a σ_c notion; the invariant doesn't apply.
        let cfg = ElectionsConfig {
            node_id: "test".to_string(),
            pipeline: test_pipeline(),
            committee_selection: CommitteeSelection::WfaLs {
                persistent_voters: 480,
                non_persistent_voters: 120,
            },
            persistent_committee: BTreeMap::new(),
            stake_registry: BTreeMap::new(),
            total_stake: 1_000_000,
            expected_total_weight: 600,
            quorum_weight_fraction: 0.99,
        };
        assert!(cfg.validate().is_ok());
    }
}
