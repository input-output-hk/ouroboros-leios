//! Sim-rs adapter for the shared con-rs consensus crate.
//!
//! This module is the W2.2 work item from
//! `sim-rs/merge-con-rs-plan.md`: replace `linear_leios.rs` with a thin
//! wrapper that drives `con_rs::leios::LeiosState`,
//! `con_rs::praos::PraosState`, and `con_rs::mempool::MempoolState`
//! directly. The handlers fill in incrementally — today only the TX
//! propagation path is wired, so selecting `variant: con-rs` exercises
//! `MempoolState` end-to-end but emits no RBs, EBs, or votes yet.
//!
//! Wire format (`Message`, `CpuTask`, `TimedEvent`) is reused from
//! `linear_leios` so cross-variant comparisons (`linear` vs `con-rs`)
//! and the byte-equivalent event-stream determinism check in W2.5 line
//! up directly.
//!
//! Adversary hooks are intentionally absent — they re-enter as a
//! follow-on wrapper layer once the protocol-level equivalence in W2.6
//! is verified.
//!
//! # YAML config knobs the adapter reads
//!
//! The translation lives in [`derive_pipeline`],
//! [`derive_committee_selection`], and [`derive_quorum_fraction`].
//! Anything not in this table either:
//! - has no con-rs analog (sim-only knobs), or
//! - hasn't been wired yet (TODOs called out in the helpers).
//!
//! | YAML key                                | con-rs destination                                 |
//! |-----------------------------------------|----------------------------------------------------|
//! | `leios-header-diffusion-time-ms`        | `PipelineConfig.delta_hdr` (in slots, ceil)        |
//! | `linear-vote-stage-length-slots`        | `PipelineConfig.vote_window` (CIP-0164 L_vote)     |
//! | `linear-diffuse-stage-length-slots`     | `PipelineConfig.diffuse_window` (CIP-0164 L_diff)  |
//! | `linear-tx-max-age-slots`               | `PipelineConfig.dedup_window` (residual)           |
//! | `committee-selection-algorithm`         | `CommitteeSelection` variant                       |
//! | `persistent-vote-generation-probability`<br>`+ non-persistent-vote-generation-probability` | `WfaLs.persistent_voters` (combined — already dimensioned as expected total committee weight per EB) |
//! | `vote-threshold`                        | `ElectionsConfig.quorum_weight_fraction`           |
//! | `vote-bundle-size-bytes-constant`<br>`+ {persistent,non-persistent}-vote-bundle-size-bytes-per-eb` | `VotingConfig.{persistent,non_persistent}_vote_bytes` (via `Sizes::vote_bundle`) |
//! | `leios-mempool-size-bytes`              | `MempoolState::new(capacity)`                      |
//! | `rb-body-max-size-bytes`                | `BodyPath::decide(_, rb_body_max_bytes)`           |
//! | `rb-generation-probability` (= `block-generation-probability`) | `rb_win_threshold(rate, stake)` |
//! | _(per-node) `stake`_                    | `StakeEntry.stake` + `VotingConfig.stake`          |
//! | _(per-node) `name`_                     | `Elections.node_id`, `StakeEntry.node_id`, voter key |
//!
//! Hardcoded defaults (no YAML source yet):
//!
//! | con-rs field                  | Value | Rationale                                         |
//! |-------------------------------|-------|---------------------------------------------------|
//! | `WfaLs.non_persistent_voters` | `0`   | sim collapses PV/NPV into one probability         |
//! | `StakeCentile.top_centile_of_stake` | `0.95` | sim's `committee-stake-fraction-threshold` isn't propagated to `SimConfiguration` |
//! | `PraosState` `k`              | `2160` | sim doesn't model security parameter           |
//! | Fetch policies (RB/EB/votes)  | `LowestRttFirst` with `UniformRtt(0)` (con-rs `LeiosState::new` default) — sim drives fetches via its own `Message` enum |

use std::{collections::BTreeMap, sync::Arc};

use rand_chacha::ChaChaRng;
use tokio::sync::mpsc;

use con_rs::{
    config::{CommitteeSelection, StakeEntry},
    elections::{Elections, ElectionsConfig},
    leios::{
        ChainTipContext, LeiosEffect, LeiosState, LeiosTelemetryEvent, NoVoteReason, VotingConfig,
    },
    lottery as con_lottery,
    mempool::{EbKey, MempoolEffect, MempoolState, PendingTx, TxId, TxRejectReason},
    pipeline::PipelineConfig,
    praos::PraosState,
    production::BodyPath,
    wfa,
};

use crate::{
    clock::{Clock, Timestamp},
    config::{NodeConfiguration, NodeId, RelayStrategy, SimConfiguration},
    events::EventTracker,
    model::{
        BlockId, Endorsement, EndorserBlockId, LinearEndorserBlock, LinearRankingBlock,
        LinearRankingBlockHeader, NoVoteReason as SimNoVoteReason, Transaction, TransactionId,
        TransactionLostReason, VoteBundle, VoteBundleId,
    },
    rng::{DrawSite, Rng},
    sim::{NodeImpl, linear_leios::CpuTask, linear_leios::Message, linear_leios::TimedEvent},
};

/// Stake registry derived from the sim config. Every node builds an
/// identical copy at startup so the persistent-committee allocation
/// and the NPV lottery agree across the network.
fn build_stake_registry(sim_config: &SimConfiguration) -> Vec<StakeEntry> {
    sim_config
        .nodes
        .iter()
        .map(|n| StakeEntry {
            node_id: n.name.clone(),
            stake: n.stake,
        })
        .collect()
}

/// Derive con-rs's [`PipelineConfig`] from the sim config.
///
/// | con-rs field   | sim source                                                  |
/// |----------------|-------------------------------------------------------------|
/// | `delta_hdr`    | ceil(`leios-header-diffusion-time-ms` / 1000)               |
/// | `vote_window`  | `linear-vote-stage-length-slots` (CIP-0164 L_vote)          |
/// | `diffuse_window` | `linear-diffuse-stage-length-slots` (CIP-0164 L_diff)     |
/// | `dedup_window` | `linear-tx-max-age-slots` minus the others (with a floor)   |
fn derive_pipeline(sim_config: &SimConfiguration) -> PipelineConfig {
    let delta_hdr = sim_config
        .header_diffusion_time
        .as_secs_f64()
        .ceil() as u64;
    let vote_window = sim_config.linear_vote_stage_length;
    let diffuse_window = sim_config.linear_diffuse_stage_length;
    // Dedup window is "how long after CertEligible the cert can still be
    // included in an RB".  Sim's nearest analog is the residual past
    // `3*δ_hdr + L_vote + L_diff` in `linear-tx-max-age-slots`.  A
    // generous floor keeps short-config runs from rejecting valid certs.
    let pipeline_window = 3 * delta_hdr + vote_window + diffuse_window;
    let dedup_window = sim_config
        .linear_tx_max_age_slots
        .map(|m| m.saturating_sub(pipeline_window).max(10))
        .unwrap_or(100);
    PipelineConfig {
        delta_hdr,
        vote_window,
        diffuse_window,
        dedup_window,
    }
}

/// Derive con-rs's [`CommitteeSelection`] from sim's
/// [`CommitteeSelectionAlgorithm`].
///
/// | con-rs variant                | sim algorithm                                     |
/// |-------------------------------|---------------------------------------------------|
/// | `WfaLs { persistent_voters }` | `wfa-ls` — sim collapses PV/NPV into a single     |
/// |                               | probability, so the entire expected committee     |
/// |                               | becomes persistent_voters and NPV is disabled.    |
/// | `EveryoneVotes`               | `everyone`                                        |
/// | `StakeCentile`                | `top-stake-fraction` (uses sim's default 0.95)    |
///
/// **Dimension note:** sim's `*-vote-generation-probability` knobs
/// (despite the name) are the *expected total committee weight per
/// EB* — each voter runs `probability` VRF trials whose individual
/// success rate is stake-weighted, so the across-voters sum already
/// totals `probability`.  con-rs's `persistent_voters` is the
/// seat-count distributed across pools, also dimensioned as "total
/// weight per EB".  The two map directly without scaling by node
/// count.
fn derive_committee_selection(sim_config: &SimConfiguration) -> CommitteeSelection {
    use crate::config::CommitteeSelectionAlgorithm as A;
    match sim_config.committee_selection {
        A::WfaLs => {
            // Sim collapses PV / NPV into a single combined
            // probability.  Push the whole expected committee weight
            // into the deterministic persistent allocation; NPV stays
            // at 0 so we don't double-count.
            let persistent_voters = (sim_config.vote_probability as u32).max(1);
            CommitteeSelection::WfaLs {
                persistent_voters,
                non_persistent_voters: 0,
            }
        }
        A::Everyone => CommitteeSelection::EveryoneVotes,
        // Sim's `committee_stake_fraction_threshold` isn't propagated
        // through to `SimConfiguration` — use the spec default 0.95
        // until/unless that wire-up lands.
        A::TopStakeFraction => CommitteeSelection::StakeCentile {
            top_centile_of_stake: 0.95,
        },
    }
}

/// Quorum fraction = `vote_threshold / expected_committee_size`.  Sim
/// stores quorum as an absolute vote count; con-rs wants the same
/// boundary as a fraction of expected total weight.  Falls back to
/// 0.75 (CIP-0164 default) when the divisor is zero.
fn derive_quorum_fraction(sim_config: &SimConfiguration, expected: u32) -> f64 {
    if expected == 0 {
        return 0.75;
    }
    sim_config.vote_threshold as f64 / expected as f64
}

/// Canonical mapping from sim's `TransactionId` to con-rs's opaque
/// `TxId`.  Returns a 32-byte vec so the same value can serve as the
/// `[u8; 32]` hash slots use in EB manifests and in the
/// `MissingTX` voting predicate's `tx_known` callback — see
/// [`tx_id_hash`].
fn tx_id_for(id: TransactionId) -> TxId {
    tx_id_hash(id).to_vec()
}

/// 32-byte form of [`tx_id_for`], for callers that need the hash
/// representation directly (EB manifest entries, `tx_known`).  Sim
/// doesn't model real wire-byte Blake2b hashing — we encode the
/// underlying `u64` deterministically into the first 8 bytes.
fn tx_id_hash(id: TransactionId) -> [u8; 32] {
    // `TransactionId`'s inner value is exposed via Display.  Parsing
    // the string back to u64 keeps us decoupled from the inner field
    // visibility (currently private to `model.rs`).
    let n: u64 = id
        .to_string()
        .parse()
        .expect("TransactionId Display is the inner u64");
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&n.to_le_bytes());
    out
}

pub struct ConRs {
    id: NodeId,
    #[allow(dead_code)] // used once handle_new_slot drives the production lottery
    sim_config: Arc<SimConfiguration>,
    tracker: EventTracker,
    #[allow(dead_code)] // used once handle_new_slot starts driving the lottery
    clock: Clock,
    consumers: Vec<NodeId>,
    current_slot: u64,
    /// Local pool's stake.  Cached from the sim config because the
    /// production lottery runs once per slot.
    config_stake: u64,
    /// Network-wide stake, the lottery denominator.
    total_stake: u64,

    leios: LeiosState,
    #[allow(dead_code)] // wired up once Praos message handlers land
    praos: PraosState,
    mempool: MempoolState,

    /// Lookup from con-rs `TxId` back to the sim's `Arc<Transaction>`.
    /// Sim emits `Message::Tx(Arc<Transaction>)` and the lottery / EB
    /// production paths consume `Arc<Transaction>`; con-rs's mempool
    /// only knows opaque byte ids and bodies. The side-table bridges
    /// the two.
    tx_arcs: BTreeMap<TxId, Arc<Transaction>>,

    /// Per-`TxId` tracking of the peer that first delivered each tx, so
    /// `Tx → TransactionValidated` retains the originator for telemetry
    /// across the async validation hop.
    pending_from: BTreeMap<TxId, NodeId>,

    /// TxIds the local node has already seen offers for, used to
    /// dedupe `AnnounceTx` storms before they reach the mempool's
    /// `pending_validation` map.
    announced_or_known: std::collections::BTreeSet<TxId>,

    /// Per-`TxId` slot at which we first observed the tx (announce,
    /// receive, or local generation).  Used by `prune_chain_state`
    /// to age out `tx_arcs` / `announced_or_known` so they don't
    /// grow forever — mirrors linear_leios's `prune_old_txs`.
    tx_seen_slot: BTreeMap<TxId, u64>,

    /// RB state machine, indexed by `BlockId`.  Self-produced blocks
    /// enter at [`RbState::Received`]; peer announcements walk
    /// `HeaderPending → Pending → Requested → Received` as the
    /// `AnnounceRBHeader → RequestRBHeader → RBHeader → … → RB`
    /// handshake completes.
    rbs: BTreeMap<BlockId, RbState>,
    /// EB state machine, indexed by `EndorserBlockId`.  Self-produced
    /// EBs enter at [`EbState::Received`]; peer-announced EBs walk
    /// `Pending → Requested → Received` as the
    /// `AnnounceEB → RequestEB → EB` handshake completes.
    ebs: BTreeMap<EndorserBlockId, EbState>,
    /// Peers that announced each EB, in arrival order.  Used today to
    /// keep the fan-out symmetric (don't echo `AnnounceEB` back to a
    /// peer who already told us).  Will graduate to a full fetch
    /// candidate set when the multi-peer fetch policy lands.
    eb_announcers: BTreeMap<EndorserBlockId, Vec<NodeId>>,

    /// Reverse lookup from con-rs's 32-byte EB hash back to sim's
    /// `EndorserBlockId`.  Populated whenever an EB enters
    /// [`LeiosState`] via `record_eb_in_leios`.
    eb_hash_to_id: BTreeMap<[u8; 32], EndorserBlockId>,

    /// Vote bundle state machine.  Self-emitted bundles land in
    /// `Received` immediately; peer-announced bundles walk
    /// `Pending → Requested → Received`.
    vote_bundles: BTreeMap<VoteBundleId, VoteState>,

    /// NodeId → pool name lookup, cached so the vote-aggregation path
    /// (which keys by con-rs's `voter_key: Vec<u8>` over the pool name)
    /// doesn't pay a `sim_config.nodes` linear scan per vote.
    node_names: BTreeMap<NodeId, String>,

    /// Sim-side mirror of con-rs's aggregator, keyed by EB so the
    /// endorsement assembly path can answer "who voted, with what
    /// weight, for the certified EB?" without scanning private
    /// `Elections` state.  Populated by `record_bundle_into_elections`
    /// alongside `Elections::record_vote`.
    votes_by_eb: BTreeMap<EndorserBlockId, BTreeMap<NodeId, usize>>,

    /// Latest RB header this node has seen (received or produced).
    /// Stands in for the proper Praos chain selection until
    /// `PraosState` is wired — picks "highest slot" as the parent,
    /// no fork-choice, no slot-battle resolution.  Slot ties take
    /// the producer with the lower `NodeId.to_inner()`.
    latest_rb_id: Option<BlockId>,

    /// Dedup set for `LeiosEffect::NoVote` telemetry.  con-rs's
    /// election lifecycle re-fires `NoVote` once per voting-window
    /// slot for transient reasons (WrongEB / MissingTX / LateRBHeader)
    /// until the predicate succeeds or the EB ages out.  At 750
    /// nodes × O(10) in-flight EBs that's thousands of duplicate
    /// telemetry events per slot; we collapse them to once per
    /// `(eb_hash, reason)` here.
    noted_no_vote: std::collections::BTreeSet<([u8; 32], SimNoVoteReason)>,

    /// EBs we've observed on-chain via an RB's `endorsement` but
    /// haven't yet validated the body for locally.  When the body
    /// validation completes, we drain its txs from this node's
    /// mempool / tx-tracking maps so the next RB / EB won't include
    /// already-certified txs.  Mirrors linear_leios's
    /// `incomplete_onchain_ebs`.
    incomplete_onchain_ebs: std::collections::BTreeSet<EndorserBlockId>,
}

enum VoteState {
    Requested,
    Received { votes: Arc<VoteBundle> },
}

/// State of an EB known to this node.
enum EbState {
    /// Announced by a peer but no `RequestEB` sent yet.
    Pending,
    /// `RequestEB` sent, awaiting the `EB` response.
    Requested,
    /// Body received (or locally produced).  Servable on `RequestEB`.
    Received {
        eb: Arc<LinearEndorserBlock>,
        #[allow(dead_code)] // surfaces via stats once endorsement timing wires in
        seen: Timestamp,
        #[allow(dead_code)] // gates EB-as-candidate decisions once voting lands
        validated: bool,
    },
}

/// State of an RB known to this node.  Linear progression with one
/// quirk: locally produced blocks skip the early states and land
/// directly in [`RbState::Received`].
enum RbState {
    /// Header request sent to a peer, waiting for the `RBHeader`
    /// response.
    HeaderPending,
    /// Header received and validated; no body yet.
    Pending {
        header: LinearRankingBlockHeader,
        header_seen: Timestamp,
    },
    /// Body request sent to a peer, waiting for the `RB` response.
    Requested {
        header: LinearRankingBlockHeader,
        header_seen: Timestamp,
    },
    /// Body received (or locally produced).  Servable on `RequestRB`.
    Received {
        rb: Arc<LinearRankingBlock>,
        header_seen: Timestamp,
    },
}

impl RbState {
    fn header(&self) -> Option<&LinearRankingBlockHeader> {
        match self {
            Self::HeaderPending => None,
            Self::Pending { header, .. } | Self::Requested { header, .. } => Some(header),
            Self::Received { rb, .. } => Some(&rb.header),
        }
    }
    fn header_seen(&self) -> Option<Timestamp> {
        match self {
            Self::HeaderPending => None,
            Self::Pending { header_seen, .. }
            | Self::Requested { header_seen, .. }
            | Self::Received { header_seen, .. } => Some(*header_seen),
        }
    }
}

type EventResult = super::EventResult<ConRs>;

impl NodeImpl for ConRs {
    type Message = Message;
    type Task = CpuTask;
    type TimedEvent = TimedEvent;
    type CustomEvent = ();

    fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        tracker: EventTracker,
        _rng: ChaChaRng,
        clock: Clock,
    ) -> Self {
        // Same stateless-RNG model as linear_leios: per-node randomness
        // is derived on demand by `Rng::new(sim_config.seed)` with a
        // `(node, slot, site)` context.

        let stake_registry = build_stake_registry(&sim_config);
        let committee_selection = derive_committee_selection(&sim_config);
        let persistent_committee =
            wfa::build_committee(&committee_selection, &stake_registry, sim_config.seed);
        let expected_committee_size =
            wfa::expected_committee_size(&committee_selection, &persistent_committee);
        let total_stake: u64 = stake_registry.iter().map(|e| e.stake).sum();

        let pipeline = derive_pipeline(&sim_config);
        let quorum_weight_fraction = derive_quorum_fraction(&sim_config, expected_committee_size);
        let elections = Elections::new(ElectionsConfig {
            node_id: config.name.clone(),
            pipeline,
            committee_selection: committee_selection.clone(),
            persistent_committee: persistent_committee.clone(),
            stake_registry: stake_registry
                .iter()
                .map(|e| (e.node_id.clone(), e.stake))
                .collect(),
            total_stake,
            expected_committee_size,
            quorum_weight_fraction,
        });

        let persistent_seats = persistent_committee.get(&config.name).copied().unwrap_or(0);
        // Sim collapses PV / NPV byte budgets into a single
        // `vote_bundle_size_bytes_constant + vote_per_eb * n_ebs` curve
        // via `vote_weighted_average`.  Since per-class breakdowns
        // aren't preserved on `SimConfiguration`, pass the full
        // single-EB cost on both legs — the adapter currently emits
        // exactly one bundle per EB.
        let vote_bytes_per_bundle = sim_config.sizes.vote_bundle(1);
        let voting_config = VotingConfig {
            committee_selection,
            stake: config.stake,
            total_stake,
            persistent_vote_bytes: vote_bytes_per_bundle as usize,
            non_persistent_vote_bytes: vote_bytes_per_bundle as usize,
            persistent_seats,
        };

        let leios = LeiosState::new(config.name.clone(), elections, voting_config, pipeline);
        // Cardano-mainnet security parameter; sim doesn't model a
        // distinct `k`, and 2160 sets `PraosState`'s chain-tree
        // pruning depth comfortably beyond any sim run length.
        let praos = PraosState::new(config.name.clone(), 2160);
        let mempool = MempoolState::new(sim_config.mempool_size_bytes as usize);
        let node_names = sim_config_nodes_to_names(&sim_config);

        Self {
            id: config.id,
            sim_config,
            tracker,
            clock,
            consumers: config.consumers.clone(),
            current_slot: 0,
            config_stake: config.stake,
            total_stake,
            leios,
            praos,
            mempool,
            tx_arcs: BTreeMap::new(),
            pending_from: BTreeMap::new(),
            announced_or_known: std::collections::BTreeSet::new(),
            tx_seen_slot: BTreeMap::new(),
            rbs: BTreeMap::new(),
            ebs: BTreeMap::new(),
            eb_announcers: BTreeMap::new(),
            eb_hash_to_id: BTreeMap::new(),
            vote_bundles: BTreeMap::new(),
            node_names,
            votes_by_eb: BTreeMap::new(),
            latest_rb_id: None,
            noted_no_vote: std::collections::BTreeSet::new(),
            incomplete_onchain_ebs: std::collections::BTreeSet::new(),
        }
    }

    fn custom_event_source(&mut self) -> Option<mpsc::UnboundedReceiver<Self::CustomEvent>> {
        None
    }

    fn handle_new_slot(&mut self, slot: u64) -> EventResult {
        self.current_slot = slot;
        let mut out = EventResult::default();
        // Periodic adapter-side pruning. Without it the chain-state
        // side-tables grow unboundedly — RBs, EBs, vote bundles,
        // eb_announcers, eb_hash_to_id, votes_by_eb, noted_no_vote
        // each carry one entry per (slot, producer/voter) seen.  At
        // 750 nodes × 1500 slots that's millions of entries and a
        // ~6× slowdown vs linear_leios.  Prune everything older than
        // 5× the pipeline window; cert assembly and `LeiosState`
        // both age out well before that.
        if slot.is_multiple_of(100) {
            self.prune_chain_state(slot);
        }
        if slot.is_multiple_of(60) && self.id.to_inner() == 0 {
            self.log_memory_stats(slot);
        }
        // Drive Leios election lifecycle.  `tx_known` is `|_| true`
        // until the EB-manifest path's `MissingTX` predicate is
        // hooked up to a real callback (sim's tx_arcs).
        let leios_fx = self.leios.on_slot(slot, &|_| true);
        self.apply_leios_effects(&mut out, leios_fx);
        // Praos RB lottery — shared formula with net-rs, sim-rs keeps
        // its own VRF draw form (`Rng::draw_range`).
        let success_rate = self.sim_config.block_generation_probability;
        let target =
            con_lottery::rb_win_threshold(success_rate, self.config_stake) as u64;
        let total_stake = self.total_stake;
        let rng = Rng::new(self.sim_config.seed);
        let draw = rng.draw_range(self.id, slot, DrawSite::RbLottery, total_stake);
        if draw < target {
            self.try_produce_rb(slot, draw, &mut out);
        }
        out
    }

    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult {
        self.tracker.track_transaction_generated(&tx, self.id);
        let id = tx_id_for(tx.id);
        self.tx_arcs.insert(id.clone(), tx.clone());
        self.announced_or_known.insert(id.clone());
        self.tx_seen_slot.insert(id.clone(), self.current_slot);

        let mut out = EventResult::default();
        // Locally-generated txs skip the validate-then-admit dance:
        // the sim's tx generator is the source of truth, and we mirror
        // linear_leios's `generate_tx → propagate_tx → mempool` shape.
        // CpuTask scheduling for validation happens for *peer-sent*
        // txs only, in `handle_message::Tx`.
        let fx = self.mempool.admit_validated(id, vec![], tx.bytes as u32);
        self.apply_mempool_effects(&mut out, fx);
        // Announce to every consumer. linear_leios announces only to
        // consumers (downstream peers); we mirror that here.
        for peer in &self.consumers {
            out.send_to(*peer, Message::AnnounceTx(tx.id));
        }
        out
    }

    fn handle_message(&mut self, from: NodeId, msg: Self::Message) -> EventResult {
        let mut out = EventResult::default();
        match msg {
            Message::AnnounceTx(id) => {
                let key = tx_id_for(id);
                if self.announced_or_known.insert(key.clone()) {
                    self.tx_seen_slot.entry(key).or_insert(self.current_slot);
                    out.send_to(from, Message::RequestTx(id));
                }
            }
            Message::RequestTx(id) => {
                let key = tx_id_for(id);
                if let Some(tx) = self.tx_arcs.get(&key) {
                    self.tracker.track_transaction_sent(tx, self.id, from);
                    out.send_to(from, Message::Tx(tx.clone()));
                }
            }
            Message::Tx(tx) => {
                self.tracker
                    .track_transaction_received(tx.id, from, self.id);
                let key = tx_id_for(tx.id);
                self.tx_arcs.insert(key.clone(), tx.clone());
                self.pending_from.insert(key.clone(), from);
                self.tx_seen_slot.entry(key).or_insert(self.current_slot);
                out.schedule_cpu_task(CpuTask::TransactionValidated(from, tx));
            }
            Message::AnnounceRBHeader(id) => self.receive_announce_rb_header(&mut out, from, id),
            Message::RequestRBHeader(id) => self.receive_request_rb_header(&mut out, from, id),
            Message::RBHeader(header, has_body, has_eb) => {
                out.schedule_cpu_task(CpuTask::RBHeaderValidated(from, header, has_body, has_eb));
            }
            Message::AnnounceRB(id) => self.receive_announce_rb(&mut out, from, id),
            Message::RequestRB(id) => self.receive_request_rb(&mut out, from, id),
            Message::RB(rb) => {
                self.tracker.track_linear_rb_received(&rb, from, self.id);
                out.schedule_cpu_task(CpuTask::RBBlockValidated(rb));
            }
            Message::AnnounceEB(id) => self.receive_announce_eb(&mut out, from, id),
            Message::RequestEB(id) => self.receive_request_eb(&mut out, from, id),
            Message::EB(eb) => {
                self.tracker.track_eb_received(eb.id(), from, self.id);
                out.schedule_cpu_task(CpuTask::EBHeaderValidated(from, eb));
            }
            Message::AnnounceVotes(id) => self.receive_announce_votes(&mut out, from, id),
            Message::RequestVotes(id) => self.receive_request_votes(&mut out, from, id),
            Message::Votes(bundle) => {
                self.tracker.track_votes_received(&bundle, from, self.id);
                out.schedule_cpu_task(CpuTask::VTBundleValidated(from, bundle));
            }
        }
        out
    }

    fn handle_cpu_task(&mut self, task: Self::Task) -> EventResult {
        let mut out = EventResult::default();
        match task {
            CpuTask::TransactionValidated(from, tx) => {
                let key = tx_id_for(tx.id);
                self.pending_from.remove(&key);
                let fx = self.mempool.admit_validated(key, vec![], tx.bytes as u32);
                let admitted = !fx
                    .iter()
                    .any(|e| matches!(e, MempoolEffect::TxRejected { .. }));
                self.apply_mempool_effects(&mut out, fx);
                if admitted {
                    for peer in &self.consumers {
                        if *peer == from {
                            continue;
                        }
                        out.send_to(*peer, Message::AnnounceTx(tx.id));
                    }
                }
            }
            CpuTask::RBBlockGenerated(rb, eb) => self.finish_generating_rb(&mut out, rb, eb),
            CpuTask::RBHeaderValidated(from, header, has_body, has_eb) => {
                self.finish_validating_rb_header(&mut out, from, header, has_body, has_eb);
            }
            CpuTask::RBBlockValidated(rb) => self.finish_validating_rb(&mut out, rb),
            CpuTask::EBHeaderValidated(from, eb) => {
                self.finish_validating_eb_header(&mut out, from, eb);
            }
            CpuTask::EBBlockValidated(eb, seen) => self.finish_validating_eb(&mut out, eb, seen),
            CpuTask::VTBundleGenerated(bundle, eb) => {
                self.finish_generating_votes(&mut out, bundle, eb);
            }
            CpuTask::VTBundleValidated(from, bundle) => {
                self.finish_validating_votes(&mut out, from, bundle);
            }
        }
        out
    }

    fn handle_timed_event(&mut self, _event: Self::TimedEvent) -> EventResult {
        EventResult::default()
    }
}

impl ConRs {
    /// Lottery win for slot `slot` (winning draw `vrf`): pick the body
    /// path via [`BodyPath::decide`] and schedule
    /// `CpuTask::RBBlockGenerated`.  The `Eb` path also commits the
    /// drain via [`MempoolState::produce_eb`] under a hash derived from
    /// the EB id — a sim convenience that stands in for real Blake2b
    /// hashing of wire bytes.
    fn try_produce_rb(&mut self, slot: u64, vrf: u64, out: &mut EventResult) {
        let block_id = BlockId {
            slot,
            producer: self.id,
        };
        self.tracker.track_praos_block_lottery_won(block_id);

        // Build the endorsement (if any) before picking the body, so we
        // can drain the endorsed EB's txs from this node's mempool
        // before they get re-included in the new EB body.  Matches
        // linear_leios's `remove_eb_txs_from_mempool` call in its
        // RB-build closure.
        let endorsement = self.try_build_endorsement();
        if let Some(endorsement) = endorsement.as_ref() {
            let eb_arc = match self.ebs.get(&endorsement.eb) {
                Some(EbState::Received { eb, validated: true, .. }) => Some(eb.clone()),
                _ => None,
            };
            if let Some(eb) = eb_arc {
                self.drain_endorsed_eb(&eb);
            } else {
                self.incomplete_onchain_ebs.insert(endorsement.eb);
            }
        }

        let max_rb_body = self.sim_config.max_block_size as usize;
        let body = BodyPath::decide(&mut self.mempool, max_rb_body);
        let (rb_txs, eb_pair) = match body {
            BodyPath::Inline(pending) => (self.collect_arcs(pending), None),
            BodyPath::Eb { manifest } => {
                // Commit the drain — `produce_eb` moves the pending
                // txs into `eb_pinned` under the given EbKey.  We
                // synthesise a deterministic hash from the producer +
                // slot since sim doesn't model Blake2b on wire bytes.
                let eb_id = EndorserBlockId {
                    slot,
                    pipeline: 0,
                    producer: self.id,
                };
                let eb_hash = synthesize_eb_hash(eb_id);
                let (_committed, mempool_fx) = self.mempool.produce_eb(EbKey {
                    slot,
                    hash: eb_hash,
                });
                self.apply_mempool_effects(out, mempool_fx);
                // Pull the body Arcs from `tx_arcs` in manifest order.
                let txs: Vec<Arc<Transaction>> = manifest
                    .iter()
                    .filter_map(|id| self.tx_arcs.get(id).cloned())
                    .collect();
                let bytes = self.sim_config.sizes.linear_eb(&txs);
                let eb = LinearEndorserBlock {
                    slot,
                    producer: self.id,
                    bytes,
                    txs: txs.clone(),
                };
                (Vec::new(), Some((eb, txs)))
            }
        };

        let rb = LinearRankingBlock {
            header: LinearRankingBlockHeader {
                id: block_id,
                vrf,
                parent: self.pick_parent(),
                bytes: self.sim_config.sizes.block_header,
                eb_announcement: eb_pair.as_ref().map(|(eb, _)| eb.id()),
            },
            transactions: rb_txs,
            endorsement,
        };

        out.schedule_cpu_task(CpuTask::RBBlockGenerated(rb, eb_pair));
    }

    /// `RBBlockGenerated` completion: persist the produced RB/EB in
    /// the side-tables and announce the header to consumers.  Locally
    /// produced blocks bypass the receive-side state walk and land
    /// directly in [`RbState::Received`].
    fn finish_generating_rb(
        &mut self,
        out: &mut EventResult,
        rb: LinearRankingBlock,
        eb: Option<(LinearEndorserBlock, Vec<Arc<Transaction>>)>,
    ) {
        self.tracker.track_linear_rb_generated(&rb);
        let rb_id = rb.header.id;
        let header_seen = self.clock.now();
        let header_for_ctx = rb.header.clone();
        let rb = Arc::new(rb);
        if self.note_rb_observed(rb_id) {
            self.update_chain_tip_ctx(&header_for_ctx);
        }
        self.rbs.insert(
            rb_id,
            RbState::Received {
                rb,
                header_seen,
            },
        );
        for peer in &self.consumers {
            out.send_to(*peer, Message::AnnounceRBHeader(rb_id));
        }
        if let Some((eb, _withheld)) = eb {
            self.tracker.track_linear_eb_generated(&eb);
            let eb_id = eb.id();
            let seen = self.clock.now();
            let eb = Arc::new(eb);
            // Locally produced: feed the manifest into LeiosState so
            // the election is announced and the per-EB voting
            // lifecycle runs at the next slot tick.
            self.record_eb_in_leios(eb_id, &eb);
            self.ebs.insert(
                eb_id,
                EbState::Received {
                    eb,
                    seen,
                    validated: true,
                },
            );
            for peer in &self.consumers {
                out.send_to(*peer, Message::AnnounceEB(eb_id));
            }
        }
    }

    fn receive_announce_rb_header(
        &mut self,
        out: &mut EventResult,
        from: NodeId,
        id: BlockId,
    ) {
        let should_request = match self.rbs.get(&id) {
            None => true,
            Some(RbState::HeaderPending) => {
                self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
            }
            _ => false,
        };
        if should_request {
            self.rbs.insert(id, RbState::HeaderPending);
            out.send_to(from, Message::RequestRBHeader(id));
        }
    }

    fn receive_request_rb_header(
        &mut self,
        out: &mut EventResult,
        from: NodeId,
        id: BlockId,
    ) {
        let Some(state) = self.rbs.get(&id) else {
            return;
        };
        let Some(header) = state.header().cloned() else {
            return;
        };
        let have_body = matches!(state, RbState::Received { .. });
        // `have_eb` is the signal that drives the receiver's
        // proactive RequestEB on header arrival.  It must be true
        // only when the body is locally servable — `Pending` /
        // `Requested` slots advertise an EB we can't yet hand out,
        // so the requester would stall in `Requested` waiting on a
        // RequestEB this side silently drops.
        let have_eb = header
            .eb_announcement
            .is_some_and(|eb_id| matches!(self.ebs.get(&eb_id), Some(EbState::Received { .. })));
        out.send_to(from, Message::RBHeader(header, have_body, have_eb));
    }

    /// `RBHeaderValidated` completion: place the header in
    /// [`RbState::Pending`], announce to other consumers, and request
    /// the body from `from` when it's already on-hand.  Slot-battle
    /// resolution is intentionally omitted in this slice — the next
    /// PraosState slice gets that for free.
    fn finish_validating_rb_header(
        &mut self,
        out: &mut EventResult,
        from: NodeId,
        header: LinearRankingBlockHeader,
        has_body: bool,
        _has_eb: bool,
    ) {
        let id = header.id;
        let header_seen = self.clock.now();
        if self.note_rb_observed(id) {
            self.update_chain_tip_ctx(&header);
        }
        self.rbs.insert(
            id,
            RbState::Pending {
                header: header.clone(),
                header_seen,
            },
        );
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            out.send_to(*peer, Message::AnnounceRBHeader(id));
        }
        if has_body {
            self.rbs.insert(
                id,
                RbState::Requested {
                    header,
                    header_seen,
                },
            );
            out.send_to(from, Message::RequestRB(id));
        }
    }

    fn receive_announce_rb(&mut self, out: &mut EventResult, from: NodeId, id: BlockId) {
        let (header, header_seen) = match self.rbs.get(&id) {
            Some(RbState::Pending { header, header_seen }) => {
                (header.clone(), *header_seen)
            }
            Some(RbState::Requested { header, header_seen })
                if self.sim_config.relay_strategy == RelayStrategy::RequestFromAll =>
            {
                (header.clone(), *header_seen)
            }
            _ => return,
        };
        self.rbs.insert(
            id,
            RbState::Requested {
                header,
                header_seen,
            },
        );
        out.send_to(from, Message::RequestRB(id));
    }

    fn receive_request_rb(&mut self, out: &mut EventResult, from: NodeId, id: BlockId) {
        if let Some(RbState::Received { rb, .. }) = self.rbs.get(&id) {
            self.tracker.track_linear_rb_sent(rb, self.id, from);
            out.send_to(from, Message::RB(rb.clone()));
        }
    }

    fn receive_announce_eb(
        &mut self,
        out: &mut EventResult,
        from: NodeId,
        id: EndorserBlockId,
    ) {
        self.eb_announcers.entry(id).or_default().push(from);
        let should_request = match self.ebs.get(&id) {
            None => true,
            Some(EbState::Pending) => true,
            Some(EbState::Requested) => {
                self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
            }
            Some(EbState::Received { .. }) => false,
        };
        if should_request {
            self.ebs.insert(id, EbState::Requested);
            out.send_to(from, Message::RequestEB(id));
        } else if !self.ebs.contains_key(&id) {
            self.ebs.insert(id, EbState::Pending);
        }
    }

    fn receive_request_eb(
        &mut self,
        out: &mut EventResult,
        from: NodeId,
        id: EndorserBlockId,
    ) {
        if let Some(EbState::Received { eb, .. }) = self.ebs.get(&id) {
            self.tracker.track_linear_eb_sent(eb, self.id, from);
            out.send_to(from, Message::EB(eb.clone()));
        }
    }

    fn finish_validating_eb_header(
        &mut self,
        out: &mut EventResult,
        from: NodeId,
        eb: Arc<LinearEndorserBlock>,
    ) {
        let eb_id = eb.id();
        if matches!(self.ebs.get(&eb_id), Some(EbState::Received { .. })) {
            return;
        }
        let seen = self.clock.now();
        self.ebs.insert(
            eb_id,
            EbState::Received {
                eb: eb.clone(),
                seen,
                validated: false,
            },
        );
        // Propagate immediately under the default `EbReceived`
        // criterion — the `TxsReceived` / `FullyValid` policy knobs
        // wire up alongside the EB-tx fetch slice.
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            out.send_to(*peer, Message::AnnounceEB(eb_id));
        }
        out.schedule_cpu_task(CpuTask::EBBlockValidated(eb, seen));
    }

    fn finish_validating_eb(
        &mut self,
        out: &mut EventResult,
        eb: Arc<LinearEndorserBlock>,
        seen: Timestamp,
    ) {
        let eb_id = eb.id();
        let entry = EbState::Received {
            eb: eb.clone(),
            seen,
            validated: true,
        };
        self.ebs.insert(eb_id, entry);
        // Feed LeiosState so the election is created and the voting
        // lifecycle starts at the next slot tick.  Idempotent — a
        // duplicate `announce` is silently absorbed.
        self.record_eb_in_leios(eb_id, &eb);
        // If this EB was already endorsed on-chain (we saw the
        // endorsement in an RB before its body validated locally),
        // drain its txs now.  See `finish_validating_rb`.
        if self.incomplete_onchain_ebs.remove(&eb_id) {
            self.drain_endorsed_eb(&eb);
        }
        // Drain any leios effects emitted by validation.  Today these
        // are `RecordLeiosEbManifest` + `ValidateEb` (we already
        // validated, so the latter is a no-op) — both are absorbed
        // by `apply_leios_effects`.
        let _ = out;
    }

    fn receive_announce_votes(
        &mut self,
        out: &mut EventResult,
        from: NodeId,
        id: VoteBundleId,
    ) {
        let should_request = match self.vote_bundles.get(&id) {
            None => true,
            Some(VoteState::Requested) => {
                self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
            }
            Some(VoteState::Received { .. }) => false,
        };
        if should_request {
            self.vote_bundles.insert(id, VoteState::Requested);
            out.send_to(from, Message::RequestVotes(id));
        }
    }

    fn receive_request_votes(
        &mut self,
        out: &mut EventResult,
        from: NodeId,
        id: VoteBundleId,
    ) {
        if let Some(VoteState::Received { votes }) = self.vote_bundles.get(&id) {
            self.tracker.track_votes_sent(votes, self.id, from);
            out.send_to(from, Message::Votes(votes.clone()));
        }
    }

    fn finish_generating_votes(
        &mut self,
        out: &mut EventResult,
        bundle: VoteBundle,
        _eb: Arc<LinearEndorserBlock>,
    ) {
        self.tracker.track_votes_generated(&bundle);
        let bundle = Arc::new(bundle);
        let id = bundle.id;
        self.vote_bundles
            .insert(id, VoteState::Received { votes: bundle.clone() });
        // Self-attribution: feed our own vote into the aggregator
        // immediately so quorum can form even when this node sees no
        // other voters.
        self.record_bundle_into_elections(&bundle);
        for peer in &self.consumers {
            out.send_to(*peer, Message::AnnounceVotes(id));
        }
    }

    fn finish_validating_votes(
        &mut self,
        out: &mut EventResult,
        from: NodeId,
        bundle: Arc<VoteBundle>,
    ) {
        let id = bundle.id;
        if matches!(self.vote_bundles.get(&id), Some(VoteState::Received { .. })) {
            return;
        }
        self.vote_bundles
            .insert(id, VoteState::Received { votes: bundle.clone() });
        self.record_bundle_into_elections(&bundle);
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            out.send_to(*peer, Message::AnnounceVotes(id));
        }
    }

    /// Record every (eb, weight) entry in `bundle` into the elections
    /// aggregator using the bundle's producer as the voter key.
    /// Idempotent — `record_vote` dedupes per `(eb_hash, voter_key)`.
    /// Also mirrors the entry into `votes_by_eb` so endorsement
    /// assembly can list voters without scanning private state.
    fn record_bundle_into_elections(&mut self, bundle: &VoteBundle) {
        let Some(voter_name) = self.node_names.get(&bundle.id.producer).cloned() else {
            return;
        };
        for (eb_id, count) in &bundle.ebs {
            let eb_hash = synthesize_eb_hash(*eb_id);
            self.leios
                .elections
                .record_vote(&eb_hash, voter_name.clone().into_bytes(), *count as u32);
            self.votes_by_eb
                .entry(*eb_id)
                .or_default()
                .insert(bundle.id.producer, *count);
        }
    }

    /// Pick the parent BlockId for a newly produced RB.  Stand-in for
    /// proper Praos chain selection — picks the highest-slot RB the
    /// adapter has seen, breaking ties on producer.
    fn pick_parent(&self) -> Option<BlockId> {
        self.latest_rb_id
    }

    /// If the local Elections aggregator has a certified EB whose slot
    /// is old enough that we can endorse it now, build a sim
    /// [`Endorsement`] for it.  Returns `None` if no cert is ready or
    /// the matching `EndorserBlockId` isn't known locally.
    fn try_build_endorsement(&self) -> Option<Endorsement> {
        let cert_slot = self.leios.certified_eb_slot()?;
        // Look up the EB at that slot whose hash carries a quorum.
        // Pretty much always one, but iterate just in case multiple
        // EBs were announced for the same slot.
        let eb_id = self
            .eb_hash_to_id
            .iter()
            .find(|(hash, eb_id)| {
                eb_id.slot == cert_slot && self.leios.elections.quorum(*hash)
            })
            .map(|(_, eb_id)| *eb_id)?;
        let voters = self.votes_by_eb.get(&eb_id)?.clone();
        let size_bytes = self.sim_config.sizes.cert(voters.len());
        Some(Endorsement {
            eb: eb_id,
            size_bytes,
            votes: voters,
        })
    }

    /// Refresh `latest_rb_id` when a higher-slot RB is observed.
    /// Producer break by `NodeId.to_inner()` mirrors the
    /// chain-selection tiebreaker the sequential engine uses on the
    /// linear adapter.  Returns `true` when this RB becomes the new
    /// chain tip, so the caller can propagate the chain-tip context
    /// to LeiosState.
    fn note_rb_observed(&mut self, id: BlockId) -> bool {
        let take_new = match self.latest_rb_id {
            None => true,
            Some(cur) => {
                id.slot > cur.slot
                    || (id.slot == cur.slot
                        && id.producer.to_inner() < cur.producer.to_inner())
            }
        };
        if take_new {
            self.latest_rb_id = Some(id);
        }
        take_new
    }

    /// Drop chain-state and tx-state entries older than their
    /// relevant window.  All consumers — cert assembly, `LeiosState`,
    /// vote serving, peer tx-fetch — only need state within the
    /// active window, so the adapter-side mirrors can age out
    /// aggressively without losing signal.
    fn prune_chain_state(&mut self, current_slot: u64) {
        let pipeline = self.leios.pipeline;
        let chain_window = 3 * pipeline.delta_hdr
            + pipeline.vote_window
            + pipeline.diffuse_window
            + pipeline.dedup_window;
        let chain_cutoff =
            current_slot.saturating_sub(chain_window.saturating_mul(5).max(50));
        self.rbs.retain(|id, _| id.slot >= chain_cutoff);
        self.ebs.retain(|id, _| id.slot >= chain_cutoff);
        self.eb_announcers.retain(|id, _| id.slot >= chain_cutoff);
        self.vote_bundles.retain(|id, _| id.slot >= chain_cutoff);
        self.votes_by_eb.retain(|id, _| id.slot >= chain_cutoff);
        // `eb_hash_to_id` is keyed by hash; drop entries whose
        // corresponding EndorserBlockId is below the cutoff.
        self.eb_hash_to_id
            .retain(|_, id| id.slot >= chain_cutoff);
        // `noted_no_vote` is keyed by `(hash, reason)`; drop entries
        // whose hash no longer maps to a live EB.
        let live_hashes: std::collections::BTreeSet<[u8; 32]> =
            self.eb_hash_to_id.keys().copied().collect();
        self.noted_no_vote
            .retain(|(hash, _)| live_hashes.contains(hash));

        // TX state ages out on its own (faster) clock.  Mirror
        // linear_leios's `prune_old_txs`: keep anything still in the
        // mempool (it might still be included in a future EB), age
        // out the rest by `linear-tx-max-age-slots` (default 23).
        let tx_max_age = self
            .sim_config
            .linear_tx_max_age_slots
            .unwrap_or(100);
        let tx_cutoff = current_slot.saturating_sub(tx_max_age);
        let mempool_ids: std::collections::BTreeSet<TxId> =
            self.mempool.current_tx_ids().into_iter().collect();
        self.tx_seen_slot.retain(|id, seen| {
            *seen >= tx_cutoff || mempool_ids.contains(id)
        });
        let live_txs: std::collections::BTreeSet<TxId> =
            self.tx_seen_slot.keys().cloned().collect();
        self.tx_arcs.retain(|id, _| live_txs.contains(id));
        self.announced_or_known
            .retain(|id| live_txs.contains(id));
        self.pending_from.retain(|id, _| live_txs.contains(id));
    }

    /// Per-component state-size dump, mirroring linear_leios's
    /// `log_memory_stats`.  Node 0 emits this every 60 slots so the
    /// memory curve can be eyeballed alongside the EventMonitor's
    /// global stats.  Byte estimates are rough but consistent across
    /// runs — usable for spotting growth, not for absolute accounting.
    fn log_memory_stats(&self, slot: u64) {
        let num_nodes = self.sim_config.nodes.len();

        let rss_mb = std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| {
                s.lines()
                    .find(|l| l.starts_with("VmRSS:"))
                    .and_then(|l| l.split_whitespace().nth(1))
                    .and_then(|v| v.parse::<u64>().ok())
            })
            .map(|kb| kb as f64 / 1024.0)
            .unwrap_or(0.0);

        // -- Adapter-side side-tables -----------------------------------
        let tx_arcs = self.tx_arcs.len();
        let announced = self.announced_or_known.len();
        let tx_seen = self.tx_seen_slot.len();
        let pending_from = self.pending_from.len();
        let rbs = self.rbs.len();
        let ebs = self.ebs.len();
        let ebs_tx_refs: usize = self
            .ebs
            .values()
            .filter_map(|s| match s {
                EbState::Received { eb, .. } => Some(eb.txs.len()),
                _ => None,
            })
            .sum();
        let eb_announcers_count = self.eb_announcers.len();
        let eb_announcers_peers: usize = self
            .eb_announcers
            .values()
            .map(|v| v.len())
            .sum();
        let eb_hash_to_id = self.eb_hash_to_id.len();
        let vote_bundles = self.vote_bundles.len();
        let votes_by_eb_count = self.votes_by_eb.len();
        let votes_by_eb_voters: usize =
            self.votes_by_eb.values().map(|m| m.len()).sum();
        let noted_no_vote = self.noted_no_vote.len();

        // -- LeiosState owned state -------------------------------------
        let eb_tx_hashes_count = self.leios.eb_tx_hashes.len();
        let eb_tx_hashes_refs: usize = self
            .leios
            .eb_tx_hashes
            .values()
            .map(|(_, v)| v.len())
            .sum();
        let pending_eb_tx_fetches = self.leios.pending_eb_tx_fetches.len();
        let leios_in_flight = self.leios.in_flight.len();
        let elections_count = self.leios.elections.count();

        // -- MempoolState ----------------------------------------------
        let mempool_txs = self.mempool.txs.len();
        let mempool_bytes = self.mempool.total_bytes;
        let mempool_peer_advertised = self.mempool.peer_advertised.len();
        let mempool_peer_advertised_total: usize = self
            .mempool
            .peer_advertised
            .values()
            .map(|s| s.len())
            .sum();
        let mempool_pending_validation = self.mempool.pending_validation.len();
        let mempool_eb_manifests = self.mempool.eb_manifests.len();
        let mempool_eb_manifests_refs: usize = self
            .mempool
            .eb_manifests
            .values()
            .map(|v| v.len())
            .sum();
        let mempool_eb_pinned = self.mempool.eb_pinned.len();

        // -- Rough byte estimates ---------------------------------------
        let tx_arcs_bytes = tx_arcs * 96; // BTreeMap entry + Arc<Transaction>
        let announced_bytes = announced * 64;
        let tx_seen_bytes = tx_seen * 56;
        let pending_from_bytes = pending_from * 48;
        let rbs_bytes = rbs * 96;
        let ebs_bytes = ebs * 96 + ebs_tx_refs * 8;
        let eb_announcers_bytes = eb_announcers_count * 64 + eb_announcers_peers * 8;
        let eb_hash_bytes = eb_hash_to_id * 64;
        let vote_bundles_bytes = vote_bundles * 96;
        let votes_by_eb_bytes = votes_by_eb_count * 64 + votes_by_eb_voters * 32;
        let noted_no_vote_bytes = noted_no_vote * 48;
        let eb_tx_hashes_bytes = eb_tx_hashes_count * 64 + eb_tx_hashes_refs * 32;
        let mempool_overhead_bytes = mempool_peer_advertised_total * 32
            + mempool_eb_manifests_refs * 32;

        let node_total = tx_arcs_bytes
            + announced_bytes
            + tx_seen_bytes
            + pending_from_bytes
            + rbs_bytes
            + ebs_bytes
            + eb_announcers_bytes
            + eb_hash_bytes
            + vote_bundles_bytes
            + votes_by_eb_bytes
            + noted_no_vote_bytes
            + eb_tx_hashes_bytes
            + mempool_overhead_bytes;
        let all_nodes_mb = (node_total * num_nodes) as f64 / (1024.0 * 1024.0);

        tracing::info!(
            "ConRs memory stats at slot {} (node 0, x{} nodes):\n\
             \x20 tx_arcs:              {:>8} entries  ~ {:>6.1} MB\n\
             \x20 announced_or_known:   {:>8} entries  ~ {:>6.1} MB\n\
             \x20 tx_seen_slot:         {:>8} entries  ~ {:>6.1} MB\n\
             \x20 pending_from:         {:>8} entries  ~ {:>6.1} MB\n\
             \x20 rbs:                  {:>8} entries  ~ {:>6.1} MB\n\
             \x20 ebs:                  {:>8} entries  ~ {:>6.1} MB  (tx_refs: {})\n\
             \x20 eb_announcers:        {:>8} entries  ~ {:>6.1} MB  (peers: {})\n\
             \x20 eb_hash_to_id:        {:>8} entries  ~ {:>6.1} MB\n\
             \x20 vote_bundles:         {:>8} entries  ~ {:>6.1} MB\n\
             \x20 votes_by_eb:          {:>8} entries  ~ {:>6.1} MB  (voters: {})\n\
             \x20 noted_no_vote:        {:>8} entries  ~ {:>6.1} MB\n\
             \x20 leios.eb_tx_hashes:   {:>8} entries  ~ {:>6.1} MB  (refs: {})\n\
             \x20 leios.pending_eb_tx_fetches: {:>3} entries\n\
             \x20 leios.in_flight:      {:>8} entries\n\
             \x20 leios.elections:      {:>8} entries\n\
             \x20 mempool.txs:          {:>8} entries  ~ {:>6.1} MB\n\
             \x20 mempool.peer_advertised: {:>5} peers  ({} total ids)\n\
             \x20 mempool.pending_validation: {:>4} entries\n\
             \x20 mempool.eb_manifests: {:>8} entries  (refs: {})\n\
             \x20 mempool.eb_pinned:    {:>8} entries\n\
             \x20 ---\n\
             \x20 Estimated total: ~ {:.1} MB  (x {} = ~ {:.1} MB)\n\
             \x20 Process RSS: {:.0} MB",
            slot,
            num_nodes,
            tx_arcs, tx_arcs_bytes as f64 / 1e6,
            announced, announced_bytes as f64 / 1e6,
            tx_seen, tx_seen_bytes as f64 / 1e6,
            pending_from, pending_from_bytes as f64 / 1e6,
            rbs, rbs_bytes as f64 / 1e6,
            ebs, ebs_bytes as f64 / 1e6, ebs_tx_refs,
            eb_announcers_count, eb_announcers_bytes as f64 / 1e6, eb_announcers_peers,
            eb_hash_to_id, eb_hash_bytes as f64 / 1e6,
            vote_bundles, vote_bundles_bytes as f64 / 1e6,
            votes_by_eb_count, votes_by_eb_bytes as f64 / 1e6, votes_by_eb_voters,
            noted_no_vote, noted_no_vote_bytes as f64 / 1e6,
            eb_tx_hashes_count, eb_tx_hashes_bytes as f64 / 1e6, eb_tx_hashes_refs,
            pending_eb_tx_fetches,
            leios_in_flight,
            elections_count,
            mempool_txs, mempool_bytes as f64 / 1e6,
            mempool_peer_advertised, mempool_peer_advertised_total,
            mempool_pending_validation,
            mempool_eb_manifests, mempool_eb_manifests_refs,
            mempool_eb_pinned,
            node_total as f64 / 1e6, num_nodes, all_nodes_mb,
            rss_mb,
        );
    }

    /// Push the chain tip's `(rb_header_arrival_slot, eb_announcement)`
    /// pair into LeiosState so the `LateRBHeader` / `WrongEB` voting
    /// predicates run with up-to-date inputs.  Called whenever the
    /// adopted chain tip changes — see `note_rb_observed`.
    fn update_chain_tip_ctx(&mut self, header: &LinearRankingBlockHeader) {
        let ctx = ChainTipContext {
            rb_header_arrival_slot: Some(self.current_slot),
            eb_announcement: header.eb_announcement.map(synthesize_eb_hash),
        };
        self.leios.set_chain_tip_context(ctx);
    }

    /// Wire an EB (locally produced or peer-received) into
    /// [`LeiosState`]: register the tx-hash manifest and announce the
    /// election immediately (sim validates synchronously in the
    /// CpuTask, so we skip the separate `ValidateEb` effect path).
    fn record_eb_in_leios(&mut self, eb_id: EndorserBlockId, eb: &LinearEndorserBlock) {
        let eb_hash = synthesize_eb_hash(eb_id);
        self.eb_hash_to_id.insert(eb_hash, eb_id);
        let point = con_rs::types::Point::Specific {
            slot: eb_id.slot,
            hash: eb_hash,
        };
        let manifest: Vec<[u8; 32]> = eb.txs.iter().map(|tx| tx_id_hash(tx.id)).collect();
        let fx = self.leios.on_eb_received(point.clone(), Some(manifest));
        // Drop the effects — `RecordLeiosEbManifest` doesn't need
        // forwarding (the local mempool already pinned the bodies on
        // `produce_eb`), and `ValidateEb` is a no-op for sim's
        // synchronous validation model.
        let _ = fx;
        self.leios.on_validated_eb(point);
    }

    fn finish_validating_rb(&mut self, _out: &mut EventResult, rb: Arc<LinearRankingBlock>) {
        let id = rb.header.id;
        let header_seen = self
            .rbs
            .get(&id)
            .and_then(|s| s.header_seen())
            .unwrap_or(self.clock.now());
        self.note_rb_observed(id);
        self.rbs.insert(
            id,
            RbState::Received {
                rb: rb.clone(),
                header_seen,
            },
        );
        // Drop tx_arcs entries that are now on-chain so the mempool
        // accounting doesn't carry phantom references.  `MempoolState`
        // handles its own pruning on `on_block_applied` once
        // PraosState wires the apply effect; until then we just clear
        // our side-table so EB / RB serving doesn't double-count.
        let ids_on_chain: Vec<TxId> = rb
            .transactions
            .iter()
            .map(|tx| tx_id_for(tx.id))
            .collect();
        self.mempool.on_block_applied(&ids_on_chain);
        for id in &ids_on_chain {
            self.tx_arcs.remove(id);
            self.announced_or_known.remove(id);
        }
        // The RB also carries an endorsement when it certifies an EB.
        // The endorsed EB's txs are now on-chain (via the EB closure),
        // so drain them from the local mempool / tx-tracking maps so
        // the next RB / EB this node produces won't double-include
        // them.  Mirrors linear_leios's drain on RB-with-endorsement.
        // If the EB body hasn't validated locally yet, defer in
        // `incomplete_onchain_ebs` and drain on `finish_validating_eb`.
        if let Some(endorsement) = rb.endorsement.as_ref() {
            let eb_id = endorsement.eb;
            let eb_arc = match self.ebs.get(&eb_id) {
                Some(EbState::Received { eb, validated: true, .. }) => Some(eb.clone()),
                _ => None,
            };
            if let Some(eb) = eb_arc {
                self.drain_endorsed_eb(&eb);
            } else {
                self.incomplete_onchain_ebs.insert(eb_id);
            }
        }
    }

    /// Remove the EB's txs from this node's mempool free pool and
    /// the adapter-side tx-tracking maps.  Idempotent: tx-ids that
    /// aren't currently held are silently skipped.
    fn drain_endorsed_eb(&mut self, eb: &LinearEndorserBlock) {
        let tx_ids: Vec<TxId> = eb.txs.iter().map(|tx| tx_id_for(tx.id)).collect();
        self.mempool.on_block_applied(&tx_ids);
        for id in &tx_ids {
            self.tx_arcs.remove(id);
            self.announced_or_known.remove(id);
            self.tx_seen_slot.remove(id);
            self.pending_from.remove(id);
        }
    }

    /// Look up the sim `Arc<Transaction>` for each pending tx in the
    /// drained set.  Drops anything we lost track of (shouldn't happen
    /// in practice — every tx that enters the mempool has a matching
    /// `tx_arcs` entry — but is defensive against future eviction
    /// drift).
    fn collect_arcs(&self, pending: Vec<PendingTx>) -> Vec<Arc<Transaction>> {
        pending
            .into_iter()
            .filter_map(|tx| self.tx_arcs.get(&tx.tx_id).cloned())
            .collect()
    }

    /// Forward Leios-side effects to sim's `EventResult` and tracker.
    /// Fetch / validate effects stay no-op: sim drives RB/EB/vote
    /// flows directly via the `Message` enum (see the handlers above)
    /// and validation timing through `CpuTask`, so the con-rs
    /// abstractions for those channels don't need translation here.
    fn apply_leios_effects(&mut self, out: &mut EventResult, effects: Vec<LeiosEffect>) {
        for fx in effects {
            match fx {
                LeiosEffect::EmitVote {
                    eb_slot,
                    eb_hash,
                    emit_pv,
                    npv_signature,
                } => {
                    self.emit_vote(out, eb_slot, eb_hash, emit_pv, npv_signature);
                }
                LeiosEffect::NoVote {
                    eb_slot,
                    eb_hash,
                    reason,
                } => {
                    let sim_reason = match reason {
                        NoVoteReason::LateEB => SimNoVoteReason::LateEB,
                        NoVoteReason::LateRBHeader => SimNoVoteReason::LateRBHeader,
                        NoVoteReason::WrongEB => SimNoVoteReason::WrongEB,
                        NoVoteReason::MissingTX => SimNoVoteReason::MissingTX,
                    };
                    // con-rs re-fires NoVote per slot per EB on
                    // transient reasons until the election expires.
                    // Collapse the duplicate telemetry stream here.
                    if !self.noted_no_vote.insert((eb_hash, sim_reason.clone())) {
                        continue;
                    }
                    if let Some(&eb_id) = self.eb_hash_to_id.get(&eb_hash) {
                        self.tracker
                            .track_no_vote(eb_slot, 0, self.id, eb_id, sim_reason);
                    }
                }
                LeiosEffect::EmitTelemetry(LeiosTelemetryEvent::QuorumReached { .. })
                | LeiosEffect::EmitTelemetry(LeiosTelemetryEvent::ElectionExpired { .. }) => {
                    // No 1:1 sim telemetry; sim's stat aggregator
                    // derives equivalent signals from `votes_by_eb`
                    // counts on the receive path.
                }
                // Fetch effects stay no-op: sim drives RB/EB/vote
                // fetches directly through its `Message` enum, so
                // con-rs's fetch-policy abstraction isn't on the
                // path.  Validation effects similarly: sim's
                // `CpuTask` already models the validation hop.
                LeiosEffect::FetchLeiosBlock { .. }
                | LeiosEffect::FetchLeiosBlockTxs { .. }
                | LeiosEffect::FetchLeiosVotes { .. }
                | LeiosEffect::RecordLeiosEbManifest { .. }
                | LeiosEffect::ValidateEb { .. }
                | LeiosEffect::ValidateVotes { .. } => {}
            }
        }
    }

    /// Build a sim `VoteBundle` for this EB carrying the weight con-rs
    /// computed (PV seats + NPV wins) and schedule it through
    /// `CpuTask::VTBundleGenerated` so the validation timing matches
    /// `linear_leios`.
    fn emit_vote(
        &self,
        out: &mut EventResult,
        eb_slot: u64,
        eb_hash: [u8; 32],
        emit_pv: bool,
        npv_signature: Option<Vec<u8>>,
    ) {
        let Some(&eb_id) = self.eb_hash_to_id.get(&eb_hash) else {
            return;
        };
        let Some(EbState::Received { eb, .. }) = self.ebs.get(&eb_id) else {
            return;
        };
        let pv_weight = if emit_pv {
            self.leios.voting_config.persistent_seats
        } else {
            0
        };
        let npv_weight = match npv_signature {
            Some(sig) => con_rs::wfa::count_npv_wins(
                &sig,
                self.leios.voting_config.stake,
                self.leios.voting_config.total_stake,
                self.leios
                    .voting_config
                    .committee_selection
                    .non_persistent_voters(),
            ),
            None => 0,
        };
        let weight = (pv_weight + npv_weight) as usize;
        if weight == 0 {
            return;
        }
        let id = VoteBundleId {
            slot: eb_slot,
            pipeline: 0,
            producer: self.id,
        };
        self.tracker.track_vote_lottery_won(id);
        let mut ebs = BTreeMap::new();
        ebs.insert(eb_id, weight);
        let bundle = VoteBundle {
            id,
            bytes: self.sim_config.sizes.vote_bundle(1),
            ebs,
        };
        out.schedule_cpu_task(CpuTask::VTBundleGenerated(bundle, eb.clone()));
    }

    /// Forward mempool-side effects to sim's tracker. Today only the
    /// `TxRejected` family lands here — `ValidateTx` is bypassed since
    /// sim handles validation timing through `CpuTask` directly. When
    /// the RB / EB paths land, eviction-driven `EbClosurePruned`
    /// effects will follow the same channel.
    fn apply_mempool_effects(&self, _out: &mut EventResult, effects: Vec<MempoolEffect>) {
        for fx in effects {
            match fx {
                MempoolEffect::ValidateTx { .. } => {
                    // Bypassed: sim's CpuTask handles validation timing.
                }
                MempoolEffect::TxRejected { tx_id, reason } => {
                    let Some(orig_id) = self
                        .tx_arcs
                        .get(&tx_id)
                        .map(|tx| tx.id)
                        .or_else(|| sim_id_from_bytes(&tx_id))
                    else {
                        continue;
                    };
                    let sim_reason = match reason {
                        TxRejectReason::QueueFull => {
                            Some(TransactionLostReason::PeerBacklogFull)
                        }
                        TxRejectReason::EbClosurePruned => {
                            Some(TransactionLostReason::EBExpired)
                        }
                        // `AlreadyKnown` is dedup, not loss — skip. A
                        // `ValidationFailed` outcome doesn't surface in
                        // sim today; the wrapper that introduced it
                        // (con-rs) would only emit it if we called
                        // `on_tx_validation_failed`, which we never do.
                        TxRejectReason::AlreadyKnown
                        | TxRejectReason::ValidationFailed(_) => None,
                    };
                    if let Some(reason) = sim_reason {
                        self.tracker.track_transaction_lost(orig_id, reason);
                    }
                }
            }
        }
    }
}

/// Recover a `TransactionId` from its 32-byte con-rs encoding.
/// Inverse of [`tx_id_for`].  Used in the rejection telemetry path
/// when the body arc has already been evicted from `tx_arcs`.
fn sim_id_from_bytes(bytes: &[u8]) -> Option<TransactionId> {
    if bytes.len() < 8 {
        return None;
    }
    let arr: [u8; 8] = bytes[..8].try_into().ok()?;
    Some(TransactionId::new(u64::from_le_bytes(arr)))
}

/// Build the NodeId → pool-name lookup once at startup.  con-rs's
/// vote aggregator keys voters by their pool name (the same string
/// that appears in [`StakeEntry::node_id`] and the persistent
/// committee map), so the adapter needs to translate sim's
/// integer-typed `NodeId` on the receive path.
fn sim_config_nodes_to_names(sim_config: &SimConfiguration) -> BTreeMap<NodeId, String> {
    sim_config
        .nodes
        .iter()
        .map(|n| (n.id, n.name.clone()))
        .collect()
}

/// Deterministic 32-byte EB hash derived from the EB id.  Sim doesn't
/// model wire-byte Blake2b, so we stand in with a fixed encoding that
/// is unique per `(slot, pipeline, producer)`.
fn synthesize_eb_hash(id: EndorserBlockId) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..8].copy_from_slice(&id.slot.to_le_bytes());
    out[8..16].copy_from_slice(&id.pipeline.to_le_bytes());
    out[16..24].copy_from_slice(&(id.producer.to_inner() as u64).to_le_bytes());
    out
}
