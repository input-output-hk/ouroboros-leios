//! Consensus facade.
//!
//! Owns both the Praos (longest-chain RB) and Leios (EB/vote) sub-layers and
//! dispatches incoming network events to whichever cares. Praos is the
//! foundation; Leios sits on top and, today, only routes offer/fetch events.
//! Future Leios work (EB ranking, vote aggregation, certificates) lands in
//! `leios.rs` without churning this facade.

mod leios;
mod praos;

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::types::{BlockBody, Point, Tip, WrappedHeader};
use tokio::sync::mpsc;

use crate::chain_tree::ChainTreeEntry;
use crate::validation::{LedgerOutcome, Validator};

pub use leios::LeiosConsensus;
pub use praos::PraosConsensus;

/// Top-level consensus, composing Praos and Leios sub-layers.
pub struct Consensus {
    praos: PraosConsensus,
    leios: LeiosConsensus,
}

impl Consensus {
    pub fn new(
        node_id: String,
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
        security_param_k: u64,
    ) -> Self {
        let praos = PraosConsensus::new(
            node_id.clone(),
            commands.clone(),
            validator.clone(),
            security_param_k,
        );
        let leios = LeiosConsensus::new(node_id, commands, validator);
        Self { praos, leios }
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
            LedgerOutcome::VotesValidated { vote_ids } => {
                self.leios.on_validated_votes(&vote_ids);
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
}
