//! Sim-rs adapter for the shared con-rs consensus crate.
//!
//! This module is the W2.2 work item from
//! `sim-rs/merge-con-rs-plan.md`: replace `linear_leios.rs` with a thin
//! wrapper that drives `con_rs::leios::LeiosState`,
//! `con_rs::praos::PraosState`, and `con_rs::mempool::MempoolState`
//! directly. Today only the scaffold is in place — every handler is a
//! TODO that returns an empty `EventResult`. Selecting `variant:
//! con-rs` from a config file is therefore safe but inert: the node
//! will validate setup but emit no traffic. Subsequent commits fill in
//! the effect-by-effect translation table from the plan.
//!
//! Wire format (`Message`, `CpuTask`, `TimedEvent`) is reused from
//! `linear_leios` so cross-variant comparisons (`linear` vs `con-rs`)
//! and the byte-equivalent event-stream determinism check in W2.5 line
//! up directly.
//!
//! Adversary hooks are intentionally absent — they re-enter as a
//! follow-on wrapper layer once the protocol-level equivalence in W2.6
//! is verified.

use std::sync::Arc;

use rand_chacha::ChaChaRng;
use tokio::sync::mpsc;

use con_rs::{
    config::{CommitteeSelection, StakeEntry},
    elections::{Elections, ElectionsConfig},
    leios::{LeiosState, VotingConfig},
    mempool::MempoolState,
    pipeline::PipelineConfig,
    praos::PraosState,
    wfa,
};

use crate::{
    clock::Clock,
    config::{NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::Transaction,
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

pub struct ConRs {
    #[allow(dead_code)] // wired up incrementally in subsequent commits
    id: NodeId,
    #[allow(dead_code)]
    sim_config: Arc<SimConfiguration>,
    #[allow(dead_code)]
    tracker: EventTracker,
    #[allow(dead_code)]
    clock: Clock,

    #[allow(dead_code)]
    leios: LeiosState,
    #[allow(dead_code)]
    praos: PraosState,
    #[allow(dead_code)]
    mempool: MempoolState,
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
            // zero here is harmless because the no-op handlers below
            // never emit a vote.
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
            leios,
            praos,
            mempool,
        }
    }

    fn custom_event_source(&mut self) -> Option<mpsc::UnboundedReceiver<Self::CustomEvent>> {
        None
    }

    fn handle_new_slot(&mut self, _slot: u64) -> EventResult {
        EventResult::default()
    }

    fn handle_new_tx(&mut self, _tx: Arc<Transaction>) -> EventResult {
        EventResult::default()
    }

    fn handle_message(&mut self, _from: NodeId, _msg: Self::Message) -> EventResult {
        EventResult::default()
    }

    fn handle_cpu_task(&mut self, _task: Self::Task) -> EventResult {
        EventResult::default()
    }

    fn handle_timed_event(&mut self, _event: Self::TimedEvent) -> EventResult {
        EventResult::default()
    }
}
