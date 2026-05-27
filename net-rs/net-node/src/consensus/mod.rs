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

use shared_consensus::chain_tree::ChainTreeEntry;
use shared_consensus::fetch::PeerRttCache;
use shared_consensus::leios::ChainTipContext;
use crate::config::{CommitteeSelection, DynamicConfig, FetchPolicyConfig, StakeEntry};
use crate::telemetry::NodeEvent;
use crate::validation::{LedgerOutcome, Validator};

pub use leios::{EbTxMatchOutcome, LeiosConsensus, PipelineConfig};
pub use praos::PraosConsensus;

/// Top-level consensus, composing Praos and Leios sub-layers.
pub struct Consensus {
    praos: PraosConsensus,
    leios: LeiosConsensus,
    /// Deterministic seed handed to
    /// [`shared_consensus::behaviour::build`] whenever the per-node
    /// behaviour is materialised — at startup and again from each
    /// runtime config swap.  Derived once from `rng_seed` (or the node
    /// identifier) and reused so a behaviour that hashes peer ids for
    /// partitioning always lands on the same buckets across re-runs.
    behaviour_seed: u64,
    /// Shared handle to the per-node behaviour.  All three state
    /// machines (praos, leios, mempool) point at the same `Arc<Mutex>`
    /// so a single behaviour instance observes events from every layer
    /// and so a runtime swap propagates to all of them at once.  The
    /// coordinator holds its own clone for the per-peer outbound
    /// transform path.
    behaviour_handle: shared_consensus::behaviour::BehaviourHandle,
    /// Spec the node materialised at startup.  Kept so a runtime
    /// "reset" can walk the handle back to the original behaviour
    /// (Honest for most nodes, but a node configured as a startup
    /// attacker remains one).
    startup_spec: shared_consensus::behaviour::BehaviourSpec,
}

impl Consensus {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        node_id: String,
        commands: mpsc::Sender<NetworkCommand>,
        validator: Validator,
        mempool: crate::mempool::SharedMempool,
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
        rtt: PeerRttCache,
        fetch_policy: FetchPolicyConfig,
        behaviour_handle: shared_consensus::behaviour::BehaviourHandle,
        startup_spec: shared_consensus::behaviour::BehaviourSpec,
    ) -> Self {
        let mut praos = PraosConsensus::new(
            node_id.clone(),
            commands.clone(),
            validator.clone(),
            security_param_k,
        );
        praos.set_rtt(rtt.clone());
        praos.set_block_policy(fetch_policy.block.into_block_policy());
        let mut leios = LeiosConsensus::new(
            node_id,
            commands,
            validator,
            mempool.clone(),
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
        leios.set_rtt(rtt);
        leios.set_eb_policy(fetch_policy.eb.into_eb_policy());
        leios.set_eb_txs_policy(fetch_policy.eb_txs.into_eb_txs_policy());
        leios.set_vote_policy(fetch_policy.votes.into_vote_policy());
        let behaviour_seed = rng_seed.unwrap_or_else(|| {
            shared_consensus::behaviour::seed_from_node_id(praos.node_id_str())
        });
        // Install the shared behaviour handle on every state machine so
        // a stateful behaviour (equivocation variant store, peer
        // partition map, …) sees events from every layer and the
        // coordinator's outbound transform path observes the same
        // instance.  Runtime swaps replace the trait object inside this
        // handle; clones held elsewhere observe the new behaviour from
        // their next hook call.
        praos.install_behaviour_handle(behaviour_handle.clone());
        leios.install_behaviour_handle(behaviour_handle.clone());
        if let Ok(mut m) = mempool.lock() {
            m.install_behaviour_handle(behaviour_handle.clone());
        }
        Self {
            praos,
            leios,
            behaviour_seed,
            behaviour_handle,
            startup_spec,
        }
    }

    /// Swap the per-node behaviour by replacing the trait object inside
    /// the shared handle.  Every state machine and the coordinator's
    /// outbound transform path observe the new behaviour from their
    /// next hook call.  Called at runtime from the stdin-driven
    /// `DynamicConfigUpdate` path.
    pub fn set_behaviour(
        &mut self,
        spec: &shared_consensus::behaviour::BehaviourSpec,
        _mempool: &crate::mempool::SharedMempool,
    ) {
        tracing::info!(?spec, behaviour_seed = self.behaviour_seed, "swapping per-node behaviour");
        shared_consensus::behaviour::swap_handle(&self.behaviour_handle, spec, self.behaviour_seed);
    }

    /// Walk the per-node behaviour back to the spec materialised at
    /// startup.  Used when net-cluster stops a runtime attack so each
    /// node returns to its original configuration.
    pub fn reset_behaviour(&mut self, _mempool: &crate::mempool::SharedMempool) {
        tracing::info!(
            startup_spec = ?self.startup_spec,
            behaviour_seed = self.behaviour_seed,
            "resetting per-node behaviour to startup spec"
        );
        shared_consensus::behaviour::swap_handle(
            &self.behaviour_handle,
            &self.startup_spec,
            self.behaviour_seed,
        );
    }

    /// Ask the per-node behaviour what to do for this slot's
    /// self-produced RB.  See
    /// [`shared_consensus::behaviour::RbProductionStrategy`].  Default
    /// `HonestBehaviour` always returns `Normal`.
    pub fn rb_production_strategy(
        &mut self,
        slot: u64,
    ) -> shared_consensus::behaviour::RbProductionStrategy {
        // The behaviour lives on `LeiosState` (chosen during the
        // initial scaffolding because the Leios side has the broadest
        // hook surface); the strategy method takes a `&PraosState`
        // alongside.  Borrow split is done by passing `praos.state()`
        // before mutably borrowing the leios layer.
        let praos = self.praos.state();
        self.leios.state_mut().ask_rb_production_strategy(praos, slot)
    }

    /// Notify the Leios layer of a new slot tick.
    pub async fn on_slot(&mut self, slot: u64) {
        // Bump Praos's slot first so subsequent header-arrival paths
        // (TipAdvanced, BlockReceived, register_self_produced) stamp
        // the right slot on `note_header_first_seen`.  Then refresh the
        // chain-tip context Leios uses for the CIP-0164 voting
        // predicates before driving elections forward.
        self.praos.set_current_slot(slot);
        self.refresh_chain_tip_ctx();
        self.leios.on_slot(slot).await;
    }

    fn refresh_chain_tip_ctx(&mut self) {
        let arrival = self.praos.adopted_tip_header_arrival_slot();
        let eb_announcement = self.praos.adopted_tip_announced_eb();
        let equivocating_slots = self.praos.equivocating_rb_slots().clone();
        let tip_rb_slot = self.praos.state().adopted_tip_rb_slot();
        self.leios.set_chain_tip_context(ChainTipContext {
            rb_header_arrival_slot: arrival,
            eb_announcement,
            equivocating_slots,
            tip_rb_slot,
        });
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

    /// Register a self-produced endorser block with Leios consensus —
    /// records the manifest, fires the offer notifications, and marks
    /// the EB validated.  Also stashes the manifest size on the
    /// announcing RB's chain-tree node so the UI snapshot can surface
    /// the count regardless of LeiosState's manifest-cache TTL.
    pub async fn register_self_produced_eb(&mut self, point: Point, eb_data: &[u8]) {
        self.record_announced_eb_tx_count_from_blob(&point, eb_data);
        self.leios.register_self_produced_eb(point, eb_data).await;
    }

    /// Route a network event to Praos or Leios. Returns true if the event
    /// was consumed (caller should not log it separately).
    pub async fn handle_event(&mut self, event: &NetworkEvent) -> bool {
        // Mirror manifest sizes onto the chain-tree node on receive so
        // they survive the LeiosState cache TTL — see
        // `register_self_produced_eb` for the same on the produce path.
        if let NetworkEvent::LeiosBlockReceived { point, block } = event {
            self.record_announced_eb_tx_count_from_blob(point, block);
        }
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

    /// Decode an EB blob to extract its manifest size and stash it on
    /// the chain-tree node that announced this EB hash.  Idempotent;
    /// no-op when the blob doesn't decode (malformed) or no chain-tree
    /// node announces the EB (the announcing RB was pruned or never
    /// adopted).
    fn record_announced_eb_tx_count_from_blob(&mut self, point: &Point, blob: &[u8]) {
        let hash = match point {
            Point::Specific { hash, .. } => *hash,
            Point::Origin => return,
        };
        if let Some((_, tx_hashes)) = crate::production::decode_overflow_eb(blob) {
            self.praos
                .record_announced_eb_tx_count(&hash, tx_hashes.len() as u32);
        }
    }

    /// Verify a `LeiosBlockTxsReceived` response against the cached
    /// EB manifest. Returns the bodies whose hash lies in the manifest,
    /// in manifest-index order, plus how many indices were requested
    /// and which indices remain unfilled.
    pub fn match_eb_tx_response(&mut self, point: &Point, bodies: &[Vec<u8>]) -> EbTxMatchOutcome {
        self.leios.match_eb_tx_response(point, bodies)
    }

    /// Re-issue a `FetchLeiosBlockTxs` for the still-missing indices.
    /// The coordinator's `pick_txs_fetch_peer` excludes already-tried
    /// peers, so the retry will land on a different candidate (or no-op
    /// if all candidates are exhausted).
    pub async fn retry_eb_tx_fetch(
        &mut self,
        point: Point,
        bitmap: std::collections::BTreeMap<u16, u64>,
    ) {
        self.leios.retry_eb_tx_fetch(point, bitmap).await;
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
            LedgerOutcome::Applied { ref point } => {
                // Producer-side EB-safety gate: an RB carrying a cert
                // for the parent's announced EB needs that EB recorded
                // in `LeiosState` until its body validates locally.
                // `BodyPath::decide` reads this for the next own RB.
                if let Some((eb_slot, eb_hash)) =
                    self.praos.parent_announced_eb_for_cert(point)
                {
                    self.leios
                        .state
                        .on_chain_endorsement(eb_slot, eb_hash);
                }
                self.praos.on_validation_outcome(outcome).await
            }
            other => self.praos.on_validation_outcome(other).await,
        }
    }

    #[allow(dead_code)]
    pub fn local_tip(&self) -> Option<Tip> {
        self.praos.local_tip()
    }

    pub fn chain_tree_snapshot(&self) -> (Vec<ChainTreeEntry>, Option<u64>, Option<String>) {
        let leios_state = &self.leios.state;
        self.praos.chain_tree_snapshot(|eb_hash| {
            leios_state
                .eb_tx_hashes
                .get(eb_hash)
                .map(|(_, hashes)| hashes.len() as u32)
        })
    }

    pub fn tip_hash(&self) -> Option<[u8; 32]> {
        self.praos.tip_hash()
    }

    pub fn next_block_number(&self) -> u64 {
        self.praos.next_block_number()
    }

    /// Borrow the underlying `LeiosState`.  Used by `try_produce_block`
    /// to consult the producer-side EB-safety gate
    /// (`BodyPath::decide` reads `has_endorsed_unvalidated_eb`).
    pub fn leios_state(&self) -> &shared_consensus::leios::LeiosState {
        &self.leios.state
    }

    /// Linear-Leios producer rule: an RB may attach a cert only for the
    /// EB its **parent RB** announced, and only once that EB has reached
    /// quorum and entered CertEligible.  Returns the announced slot of
    /// that EB (to populate the `RbCertifiedEb` telemetry event); `None`
    /// means no cert candidate — the producer leaves `certified_eb` off
    /// and the parent's EB is dropped from the chain's perspective.
    pub fn cert_for_parent(&self) -> Option<u64> {
        let eb_hash = self.praos.adopted_tip_announced_eb()?;
        self.leios.eb_certifiable_slot(&eb_hash)
    }

    /// Emit per-subsystem `info!` lines summarising internal state
    /// collection sizes.  Used as a periodic diagnostic to identify
    /// unbounded growth — grep `state sizes` in node logs to read the
    /// time series.
    pub fn log_state_sizes(&self) {
        self.praos.state().log_state_sizes();
        self.leios.state.log_state_sizes();
    }

    /// Drain Leios-side telemetry events buffered since the last call.
    pub fn drain_leios_telemetry(&mut self) -> Vec<NodeEvent> {
        self.leios.drain_telemetry()
    }
}
