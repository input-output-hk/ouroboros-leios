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

use std::{collections::BTreeMap, sync::Arc};

use rand_chacha::ChaChaRng;
use tokio::sync::mpsc;

use con_rs::{
    config::{CommitteeSelection, StakeEntry},
    elections::{Elections, ElectionsConfig},
    leios::{LeiosState, VotingConfig},
    mempool::{MempoolEffect, MempoolState, TxId, TxRejectReason},
    pipeline::PipelineConfig,
    praos::PraosState,
    wfa,
};

use crate::{
    clock::Clock,
    config::{NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::{Transaction, TransactionId, TransactionLostReason},
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

/// Placeholder pipeline / voting / quorum knobs. W2.3 replaces this
/// with values read from the YAML config (vote window, delta_hdr,
/// quorum fraction, vote-body byte budgets).
fn placeholder_pipeline() -> PipelineConfig {
    PipelineConfig {
        delta_hdr: 1,
        vote_window: 5,
        diffuse_window: 5,
        dedup_window: 10,
    }
}

/// Canonical mapping from sim's `TransactionId` to con-rs's opaque
/// `TxId`. Stable across runs; reversible via the `tx_arcs` side-table
/// the adapter maintains.
fn tx_id_for(id: TransactionId) -> TxId {
    id.to_string().into_bytes()
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

    #[allow(dead_code)] // wired up once the slot tick drives elections
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
        let committee_selection = CommitteeSelection::default();
        let persistent_committee =
            wfa::build_committee(&committee_selection, &stake_registry, sim_config.seed);
        let expected_committee_size =
            wfa::expected_committee_size(&committee_selection, &persistent_committee);
        let total_stake: u64 = stake_registry.iter().map(|e| e.stake).sum();

        let pipeline = placeholder_pipeline();
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
            quorum_weight_fraction: 0.75,
        });

        let persistent_seats = persistent_committee.get(&config.name).copied().unwrap_or(0);
        let voting_config = VotingConfig {
            committee_selection,
            stake: config.stake,
            total_stake,
            // Vote-body byte budgets are set by W2.3 from the YAML;
            // zero here is harmless because the voting path isn't wired
            // yet.
            persistent_vote_bytes: 0,
            non_persistent_vote_bytes: 0,
            persistent_seats,
        };

        let leios = LeiosState::new(config.name.clone(), elections, voting_config, pipeline);
        // Praos security parameter `k`: 2160 is the Cardano-mainnet
        // value; W2.3 will read it from the sim config.
        let praos = PraosState::new(config.name.clone(), 2160);
        let mempool = MempoolState::new(sim_config.mempool_size_bytes as usize);

        Self {
            id: config.id,
            sim_config,
            tracker,
            clock,
            consumers: config.consumers.clone(),
            current_slot: 0,
            leios,
            praos,
            mempool,
            tx_arcs: BTreeMap::new(),
            pending_from: BTreeMap::new(),
            announced_or_known: std::collections::BTreeSet::new(),
        }
    }

    fn custom_event_source(&mut self) -> Option<mpsc::UnboundedReceiver<Self::CustomEvent>> {
        None
    }

    fn handle_new_slot(&mut self, slot: u64) -> EventResult {
        self.current_slot = slot;
        EventResult::default()
    }

    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult {
        self.tracker.track_transaction_generated(&tx, self.id);
        let id = tx_id_for(tx.id);
        self.tx_arcs.insert(id.clone(), tx.clone());
        self.announced_or_known.insert(id.clone());

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
                if self.announced_or_known.insert(key) {
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
                self.pending_from.insert(key, from);
                out.schedule_cpu_task(CpuTask::TransactionValidated(from, tx));
            }
            // Other variants are still no-ops while RB / EB / vote
            // handlers come up in subsequent commits.
            Message::AnnounceRBHeader(_)
            | Message::RequestRBHeader(_)
            | Message::RBHeader(_, _, _)
            | Message::AnnounceRB(_)
            | Message::RequestRB(_)
            | Message::RB(_)
            | Message::AnnounceEB(_)
            | Message::RequestEB(_)
            | Message::EB(_)
            | Message::AnnounceVotes(_)
            | Message::RequestVotes(_)
            | Message::Votes(_) => {}
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
            // Other CpuTask variants stay inert until the RB / EB /
            // vote paths land.
            CpuTask::RBBlockGenerated(_, _)
            | CpuTask::RBHeaderValidated(_, _, _, _)
            | CpuTask::RBBlockValidated(_)
            | CpuTask::EBHeaderValidated(_, _)
            | CpuTask::EBBlockValidated(_, _)
            | CpuTask::VTBundleGenerated(_, _)
            | CpuTask::VTBundleValidated(_, _) => {}
        }
        out
    }

    fn handle_timed_event(&mut self, _event: Self::TimedEvent) -> EventResult {
        EventResult::default()
    }
}

impl ConRs {
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

/// Recover a `TransactionId` from its con-rs byte encoding. Inverse of
/// `tx_id_for`. Used in the rejection telemetry path when the body
/// arc has already been evicted from `tx_arcs`.
fn sim_id_from_bytes(bytes: &[u8]) -> Option<TransactionId> {
    let s = std::str::from_utf8(bytes).ok()?;
    s.parse::<u64>().ok().map(TransactionId::new)
}
