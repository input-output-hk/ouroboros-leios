//! Consensus facade.
//!
//! Owns both the Praos (longest-chain RB) and Leios (EB/vote) sub-layers and
//! dispatches incoming network events to whichever cares. Praos is the
//! foundation; Leios sits on top and produces votes when EB elections enter
//! the Voting pipeline phase.

mod leios;
mod praos;

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::{BlockBody, Point, Tip, WrappedHeader};
use tokio::sync::{mpsc, watch};

use crate::chain_tree::ChainTreeEntry;
use crate::config::{CommitteeSelection, DynamicConfig, StakeEntry};
use crate::telemetry::NodeEvent;
use crate::validation::{LedgerOutcome, Validator};

pub use leios::{LeiosConsensus, PipelineConfig};
pub use praos::PraosConsensus;

/// Top-level consensus, composing Praos and Leios sub-layers.
pub struct Consensus {
    praos: PraosConsensus,
    leios: LeiosConsensus,
}

impl Consensus {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        node_id: String,
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
        security_param_k: u64,
        pipeline: PipelineConfig,
        committee_selection: CommitteeSelection,
        stake: u64,
        stake_registry: &[StakeEntry],
        persistent_vote_bytes: usize,
        non_persistent_vote_bytes: usize,
        quorum_weight_fraction: f64,
        committee_seed: u64,
        rng_seed: Option<u64>,
        dyn_config: watch::Receiver<DynamicConfig>,
    ) -> Self {
        let praos = PraosConsensus::new(
            node_id.clone(),
            commands.clone(),
            validator.clone(),
            security_param_k,
        );
        let leios = LeiosConsensus::new(
            node_id,
            commands,
            validator,
            pipeline,
            committee_selection,
            stake,
            stake_registry,
            persistent_vote_bytes,
            non_persistent_vote_bytes,
            quorum_weight_fraction,
            committee_seed,
            rng_seed,
            dyn_config,
        );
        Self { praos, leios }
    }

    /// Notify the Leios layer of a new slot tick.
    pub async fn on_slot(&mut self, slot: u64) {
        self.leios.on_slot(slot).await;
    }

    /// Register a self-produced ranking block with Praos consensus.
    pub async fn register_self_produced(
        &mut self,
        point: &Point,
        header: &WrappedHeader,
        body: &BlockBody,
    ) {
        self.praos.register_self_produced(point, header, body).await
    }

    /// Route a network event to Praos or Leios. Returns true if the event
    /// was consumed (caller should not log it separately).
    pub async fn handle_event(&mut self, event: &NetworkEvent) -> bool {
        match event {
            NetworkEvent::LeiosBlockOffered { .. }
            | NetworkEvent::LeiosBlockTxsOffered { .. }
            | NetworkEvent::LeiosVotesOffered { .. }
            | NetworkEvent::LeiosBlockReceived { .. }
            | NetworkEvent::LeiosVotesReceived { .. }
            | NetworkEvent::LeiosBlockTxsReceived { .. } => self.leios.handle_event(event).await,
            _ => self.praos.handle_event(event).await,
        }
    }

    /// Periodic retry for lagging nodes — evicts stale fetches and
    /// re-runs chain selection even when no network events arrive.
    pub async fn retry_pending(&mut self) {
        self.praos.retry_select_chain().await;
    }

    pub async fn on_validation_outcome(&mut self, outcome: LedgerOutcome) -> bool {
        match outcome {
            LedgerOutcome::EbValidated { point } => {
                self.leios.on_validated_eb(point);
                false
            }
            LedgerOutcome::VotesValidated { vote_data, .. } => {
                self.leios.on_validated_votes(&vote_data);
                false
            }
            other => self.praos.on_validation_outcome(other).await,
        }
    }

    #[allow(dead_code)]
    pub fn local_tip(&self) -> Option<Tip> {
        self.praos.local_tip()
    }

    pub fn chain_tree_snapshot(&self) -> (Vec<ChainTreeEntry>, Option<u64>, Option<String>) {
        self.praos.chain_tree_snapshot()
    }

    pub fn tip_hash(&self) -> Option<[u8; 32]> {
        self.praos.tip_hash()
    }

    pub fn next_block_number(&self) -> u64 {
        self.praos.next_block_number()
    }

    /// Whether any EB has a valid certificate (quorum + pipeline elapsed).
    pub fn has_certified_eb(&self) -> bool {
        self.leios.has_certified_eb()
    }

    /// Slot of the earliest certified EB, if any. Used to populate the
    /// eb_slot field on the `RbCertifiedEb` telemetry event.
    pub fn certified_eb_slot(&self) -> Option<u64> {
        self.leios.certified_eb_slot()
    }

    /// Drain Leios-side telemetry events buffered since the last call.
    pub fn drain_leios_telemetry(&mut self) -> Vec<NodeEvent> {
        self.leios.drain_telemetry()
    }
}
