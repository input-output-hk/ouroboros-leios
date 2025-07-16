use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, hash_map::Entry},
    sync::Arc,
};

use rand::{Rng as _, seq::SliceRandom as _};
use rand_chacha::ChaChaRng;

use crate::{
    clock::{Clock, Timestamp},
    config::{
        MempoolSamplingStrategy, NodeConfiguration, NodeId, RelayStrategy, SimConfiguration,
        TransactionConfig,
    },
    events::EventTracker,
    model::{
        Block as RankingBlock, BlockId, Endorsement, EndorserBlockId, NoVoteReason,
        StracciatellaEndorserBlock as EndorserBlock, Transaction, TransactionId, VoteBundle,
        VoteBundleId,
    },
    sim::{MiniProtocol, NodeImpl, SimCpuTask, SimMessage, lottery},
};

#[derive(Clone, Debug)]
pub enum Message {
    // TX propagation
    AnnounceTx(TransactionId),
    RequestTx(TransactionId),
    Tx(Arc<Transaction>),

    // RB propagation
    AnnounceRB(BlockId),
    RequestRB(BlockId),
    RB(Arc<RankingBlock>),

    // EB propagation
    AnnounceEB(EndorserBlockId),
    RequestEB(EndorserBlockId),
    EB(Arc<EndorserBlock>),

    // Vote propagation
    AnnounceVotes(VoteBundleId),
    RequestVotes(VoteBundleId),
    Votes(Arc<VoteBundle>),
}

impl SimMessage for Message {
    fn protocol(&self) -> super::MiniProtocol {
        match self {
            Self::AnnounceTx(_) => MiniProtocol::Tx,
            Self::RequestTx(_) => MiniProtocol::Tx,
            Self::Tx(_) => MiniProtocol::Tx,

            Self::AnnounceRB(_) => MiniProtocol::Block,
            Self::RequestRB(_) => MiniProtocol::Block,
            Self::RB(_) => MiniProtocol::Block,

            Self::AnnounceEB(_) => MiniProtocol::EB,
            Self::RequestEB(_) => MiniProtocol::EB,
            Self::EB(_) => MiniProtocol::EB,

            Self::AnnounceVotes(_) => MiniProtocol::Vote,
            Self::RequestVotes(_) => MiniProtocol::Vote,
            Self::Votes(_) => MiniProtocol::Vote,
        }
    }

    fn bytes_size(&self) -> u64 {
        match self {
            Self::AnnounceTx(_) => 8,
            Self::RequestTx(_) => 8,
            Self::Tx(tx) => tx.bytes,

            Self::AnnounceRB(_) => 8,
            Self::RequestRB(_) => 8,
            Self::RB(rb) => rb.bytes(),

            Self::AnnounceEB(_) => 8,
            Self::RequestEB(_) => 8,
            Self::EB(eb) => eb.bytes,

            Self::AnnounceVotes(_) => 8,
            Self::RequestVotes(_) => 8,
            Self::Votes(v) => v.bytes,
        }
    }
}

pub enum CpuTask {
    /// A transaction has been received and validated, and is ready to propagate
    TransactionValidated(NodeId, Arc<Transaction>),
    /// A ranking block has been generated and is ready to propagate
    RBBlockGenerated(RankingBlock),
    /// A ranking block has been received and validated, and is ready to propagate
    RBBlockValidated(NodeId, Arc<RankingBlock>),
    /// An endorser block has been generated and is ready to propagate
    EBBlockGenerated(EndorserBlock),
    /// An endorser block has been received and validated, and is ready to propagate
    EBBlockValidated(NodeId, Arc<EndorserBlock>),
    /// A bundle of votes has been generated and is ready to propagate
    VTBundleGenerated(VoteBundle, Vec<Arc<EndorserBlock>>),
    /// A bundle of votes has been received and validated, and is ready to propagate
    VTBundleValidated(NodeId, Arc<VoteBundle>),
}

impl SimCpuTask for CpuTask {
    fn name(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "ValTX",
            Self::RBBlockGenerated(_) => "GenRB",
            Self::RBBlockValidated(_, _) => "ValRB",
            Self::EBBlockGenerated(_) => "GenEB",
            Self::EBBlockValidated(_, _) => "ValEB",
            Self::VTBundleGenerated(_, _) => "GenVote",
            Self::VTBundleValidated(_, _) => "ValVote",
        }
        .to_string()
    }

    fn extra(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "".to_string(),
            Self::RBBlockGenerated(_) => "".to_string(),
            Self::RBBlockValidated(_, _) => "".to_string(),
            Self::EBBlockGenerated(_) => "".to_string(),
            Self::EBBlockValidated(_, _) => "".to_string(),
            Self::VTBundleGenerated(_, _) => "".to_string(),
            Self::VTBundleValidated(_, _) => "".to_string(),
        }
    }

    fn times(&self, config: &crate::config::CpuTimeConfig) -> Vec<std::time::Duration> {
        match self {
            Self::TransactionValidated(_, _) => vec![config.tx_validation],
            Self::RBBlockGenerated(rb) => {
                let mut time = config.rb_generation;
                if let Some(endorsement) = &rb.endorsement {
                    let nodes = endorsement.votes.len();
                    time += config.cert_generation_constant
                        + (config.cert_generation_per_node * nodes as u32)
                }
                vec![config.rb_generation]
            }
            Self::RBBlockValidated(_, rb) => {
                let mut time = config.rb_body_validation_constant;
                let bytes: u64 = rb.transactions.iter().map(|tx| tx.bytes).sum();
                time += config.rb_validation_per_byte * (bytes as u32);
                if let Some(endorsement) = &rb.endorsement {
                    let nodes = endorsement.votes.len();
                    time += config.cert_validation_constant
                        + (config.cert_validation_per_node * nodes as u32)
                }
                vec![time]
            }
            Self::EBBlockGenerated(_) => vec![config.eb_generation],
            Self::EBBlockValidated(_, eb) => {
                let mut time = config.eb_body_validation_constant;
                let bytes: u64 = eb.txs.iter().map(|tx| tx.bytes).sum();
                time += config.eb_body_validation_per_byte * (bytes as u32);
                vec![time]
            }
            Self::VTBundleGenerated(_, ebs) => ebs
                .iter()
                .map(|eb| {
                    config.vote_generation_constant
                        + (config.vote_generation_per_tx * eb.txs.len() as u32)
                })
                .collect(),
            Self::VTBundleValidated(_, votes) => vec![config.vote_validation; votes.ebs.len()],
        }
    }
}

enum TransactionView {
    Pending,
    Received(Arc<Transaction>),
}

#[derive(Default)]
struct NodePraosState {
    mempool: BTreeMap<TransactionId, Arc<Transaction>>,
    peer_heads: BTreeMap<NodeId, u64>,
    blocks_seen: BTreeSet<BlockId>,
    blocks: BTreeMap<BlockId, Arc<RankingBlock>>,
    block_ids_by_slot: BTreeMap<u64, BlockId>,
}

struct SeenTransaction {
    tx: Arc<Transaction>,
    seen_at: Timestamp,
}

enum EndorserBlockView {
    Pending,
    Received {
        eb: Arc<EndorserBlock>,
        finalized: bool,
    },
}
impl EndorserBlockView {
    fn eb(&self) -> Option<&Arc<EndorserBlock>> {
        match self {
            Self::Pending => None,
            Self::Received { eb, .. } => Some(eb),
        }
    }
}

enum VoteBundleView {
    Requested,
    Received(Arc<VoteBundle>),
}

#[derive(Default)]
struct NodeLeiosState {
    mempool: BTreeMap<TransactionId, SeenTransaction>,
    input_ids_in_flight: HashSet<u64>,
    ebs: HashMap<EndorserBlockId, EndorserBlockView>,
    ebs_by_pipeline: BTreeMap<u64, Vec<EndorserBlockId>>,
    earliest_eb_cert_times_by_pipeline: BTreeMap<u64, Timestamp>,
    votes_to_generate: BTreeMap<u64, usize>,
    votes_by_eb: BTreeMap<EndorserBlockId, BTreeMap<NodeId, usize>>,
    votes: BTreeMap<VoteBundleId, VoteBundleView>,
}

#[derive(Clone, Default)]
struct LedgerState {
    spent_inputs: HashSet<u64>,
    seen_blocks: HashSet<BlockId>,
    seen_ebs: HashSet<EndorserBlockId>,
}

pub struct StracciatellaLeiosNode {
    id: NodeId,
    sim_config: Arc<SimConfiguration>,
    queued: EventResult,
    tracker: EventTracker,
    rng: ChaChaRng,
    clock: Clock,
    stake: u64,
    consumers: Vec<NodeId>,
    txs: HashMap<TransactionId, TransactionView>,
    ledger_states: BTreeMap<BlockId, Arc<LedgerState>>,
    praos: NodePraosState,
    leios: NodeLeiosState,
}

type EventResult = super::EventResult<Message, CpuTask>;

impl NodeImpl for StracciatellaLeiosNode {
    type Message = Message;
    type Task = CpuTask;

    fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: Clock,
    ) -> Self {
        Self {
            id: config.id,
            sim_config,
            queued: EventResult::default(),
            tracker,
            rng,
            clock,
            stake: config.stake,
            consumers: config.consumers.clone(),
            txs: HashMap::new(),
            ledger_states: BTreeMap::new(),
            praos: NodePraosState::default(),
            leios: NodeLeiosState::default(),
        }
    }

    fn handle_new_slot(&mut self, slot: u64) -> EventResult {
        if slot % self.sim_config.stage_length == 0 {
            // A new stage has begun.

            // Decide how many votes to generate in each slot
            self.schedule_endorser_block_votes(slot);

            // Generate any EBs we're allowed to in this slot.
            self.generate_endorser_blocks(slot);

            // Vote for any EBs which satisfy all requirements.
            self.vote_for_endorser_blocks(slot);
        }

        self.try_generate_rb(slot);

        std::mem::take(&mut self.queued)
    }

    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult {
        self.generate_tx(tx);

        std::mem::take(&mut self.queued)
    }

    fn handle_message(&mut self, from: NodeId, msg: Self::Message) -> EventResult {
        match msg {
            Message::AnnounceTx(id) => self.receive_announce_tx(from, id),
            Message::RequestTx(id) => self.receive_request_tx(from, id),
            Message::Tx(tx) => self.receive_tx(from, tx),

            Message::AnnounceRB(id) => self.receive_announce_rb(from, id),
            Message::RequestRB(id) => self.receive_request_rb(from, id),
            Message::RB(rb) => self.receive_rb(from, rb),

            Message::AnnounceEB(id) => self.receive_announce_eb(from, id),
            Message::RequestEB(id) => self.receive_request_eb(from, id),
            Message::EB(eb) => self.receive_eb(from, eb),

            Message::AnnounceVotes(id) => self.receive_announce_votes(from, id),
            Message::RequestVotes(id) => self.receive_request_votes(from, id),
            Message::Votes(votes) => self.receive_votes(from, votes),
        }

        std::mem::take(&mut self.queued)
    }

    fn handle_cpu_task(&mut self, task: Self::Task) -> EventResult {
        match task {
            CpuTask::TransactionValidated(from, tx) => self.propagate_tx(from, tx),
            CpuTask::RBBlockGenerated(rb) => self.finish_generating_rb(rb),
            CpuTask::RBBlockValidated(from, rb) => self.finish_validating_rb(from, rb),
            CpuTask::EBBlockGenerated(eb) => self.finish_generating_eb(eb),
            CpuTask::EBBlockValidated(from, eb) => self.finish_validating_eb(from, eb),
            CpuTask::VTBundleGenerated(votes, _) => self.finish_generating_vote_bundle(votes),
            CpuTask::VTBundleValidated(from, votes) => {
                self.finish_validating_vote_bundle(from, votes)
            }
        }

        std::mem::take(&mut self.queued)
    }
}

// Transaction propagation
impl StracciatellaLeiosNode {
    fn receive_announce_tx(&mut self, from: NodeId, id: TransactionId) {
        if self.txs.get(&id).is_none_or(|t| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(t, TransactionView::Pending)
        }) {
            self.txs.insert(id, TransactionView::Pending);
            self.queued.send_to(from, Message::RequestTx(id));
        }
    }

    fn receive_request_tx(&mut self, from: NodeId, id: TransactionId) {
        if let Some(TransactionView::Received(tx)) = self.txs.get(&id) {
            self.tracker.track_transaction_sent(tx, self.id, from);
            self.queued.send_to(from, Message::Tx(tx.clone()));
        }
    }

    fn receive_tx(&mut self, from: NodeId, tx: Arc<Transaction>) {
        self.tracker
            .track_transaction_received(tx.id, from, self.id);
        self.queued
            .schedule_cpu_task(CpuTask::TransactionValidated(from, tx));
    }

    fn generate_tx(&mut self, tx: Arc<Transaction>) {
        self.tracker.track_transaction_generated(&tx, self.id);
        self.propagate_tx(self.id, tx);
    }

    fn propagate_tx(&mut self, from: NodeId, tx: Arc<Transaction>) {
        let id = tx.id;
        if self
            .txs
            .insert(id, TransactionView::Received(tx.clone()))
            .is_some_and(|tx| matches!(tx, TransactionView::Received(_)))
        {
            return;
        }
        let rb_ref = self.latest_rb().map(|rb| rb.id);
        let ledger_state = self.resolve_ledger_state(rb_ref);
        if ledger_state.spent_inputs.contains(&tx.input_id) {
            // Ignoring a TX which conflicts with something already onchain
            return;
        }
        if self
            .praos
            .mempool
            .values()
            .any(|mempool_tx| mempool_tx.input_id == tx.input_id)
        {
            // Ignoring a TX which conflicts with the current mempool contents.
            return;
        }

        // TODO: should send to producers instead (make configurable)
        self.praos.mempool.insert(tx.id, tx.clone());
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued.send_to(*peer, Message::AnnounceTx(id));
        }

        if self.sim_config.mempool_aggressive_pruning
            && self.leios.input_ids_in_flight.contains(&tx.input_id)
        {
            // Ignoring a TX which conflicts with TXs we've seen in input or endorser blocks.
            // This only affects the Leios mempool; these TXs should still be able to reach the chain through Praos.
            return;
        }

        self.leios.mempool.insert(
            tx.id,
            SeenTransaction {
                seen_at: self.clock.now(),
                tx,
            },
        );
    }
}

// Ranking block propagation
impl StracciatellaLeiosNode {
    fn try_generate_rb(&mut self, slot: u64) {
        // L1 block generation
        let Some(vrf) = self.run_vrf(self.sim_config.block_generation_probability) else {
            return;
        };

        // Let's see if we are minting an RB
        let endorsement = self.choose_endorsed_block_for_rb(slot);
        if let Some(endorsement) = &endorsement {
            // If we are, get all referenced TXs out of the mempool
            self.remove_endorsed_txs_from_mempools(endorsement);
        }

        let mut transactions = vec![];
        if self.sim_config.praos_fallback {
            if let TransactionConfig::Mock(config) = &self.sim_config.transactions {
                // Add one transaction, the right size for the RB payload
                let tx = config.mock_tx(config.rb_size);
                self.tracker.track_transaction_generated(&tx, self.id);
                transactions.push(Arc::new(tx));
            } else {
                self.sample_from_praos_mempool(&mut transactions);
            }
        }

        let parent = self.latest_rb().map(|rb| rb.id);

        let rb = RankingBlock {
            id: BlockId {
                slot,
                producer: self.id,
            },
            vrf,
            parent,
            header_bytes: self.sim_config.sizes.block_header,
            endorsement,
            transactions,
        };
        self.tracker.track_praos_block_lottery_won(rb.id);
        self.queued.schedule_cpu_task(CpuTask::RBBlockGenerated(rb));
    }

    fn finish_generating_rb(&mut self, rb: RankingBlock) {
        self.tracker.track_praos_block_generated(&rb);
        self.publish_rb(Arc::new(rb));
    }

    fn publish_rb(&mut self, rb: Arc<RankingBlock>) {
        self.remove_rb_txs_from_mempools(&rb);
        for peer in &self.consumers {
            if self
                .praos
                .peer_heads
                .get(peer)
                .is_none_or(|&s| s < rb.id.slot)
            {
                self.queued.send_to(*peer, Message::AnnounceRB(rb.id));
                self.praos.peer_heads.insert(*peer, rb.id.slot);
            }
        }
        self.praos.block_ids_by_slot.insert(rb.id.slot, rb.id);
        self.praos.blocks.insert(rb.id, rb);
    }

    fn receive_announce_rb(&mut self, from: NodeId, id: BlockId) {
        if self.praos.blocks_seen.insert(id) {
            self.queued.send_to(from, Message::RequestRB(id));
        }
    }

    fn receive_request_rb(&mut self, from: NodeId, id: BlockId) {
        if let Some(rb) = self.praos.blocks.get(&id) {
            self.tracker.track_praos_block_sent(rb, self.id, from);
            self.queued.send_to(from, Message::RB(rb.clone()));
        }
    }

    fn receive_rb(&mut self, from: NodeId, rb: Arc<RankingBlock>) {
        self.tracker.track_praos_block_received(&rb, from, self.id);
        self.queued
            .schedule_cpu_task(CpuTask::RBBlockValidated(from, rb));
    }

    fn finish_validating_rb(&mut self, from: NodeId, rb: Arc<RankingBlock>) {
        if let Some(old_rb_id) = self.praos.block_ids_by_slot.get(&rb.id.slot) {
            // SLOT BATTLE!!! lower VRF wins
            if let Some(old_rb) = self.praos.blocks.get(old_rb_id) {
                if old_rb.vrf <= rb.vrf {
                    // We like our block better than this new one.
                    return;
                }
                self.praos.blocks.remove(old_rb_id);
            }
        }

        self.praos.block_ids_by_slot.insert(rb.id.slot, rb.id);
        self.praos.blocks.insert(rb.id, rb.clone());

        let head = self.praos.peer_heads.entry(from).or_default();
        if *head < rb.id.slot {
            *head = rb.id.slot
        }
        self.publish_rb(rb);
    }

    fn latest_rb(&self) -> Option<&Arc<RankingBlock>> {
        self.praos.blocks.values().next_back()
    }
}

// EB propagation
impl StracciatellaLeiosNode {
    fn generate_endorser_blocks(&mut self, slot: u64) {
        let pipeline = self.slot_to_pipeline(slot) + 1;

        let shards = self.find_available_shards(slot);
        for next_p in lottery::vrf_probabilities(self.sim_config.eb_generation_probability) {
            if let Some(vrf) = self.run_vrf(next_p) {
                self.tracker.track_eb_lottery_won(EndorserBlockId {
                    slot,
                    pipeline,
                    producer: self.id,
                });
                let shard = shards[vrf as usize % shards.len()];
                let txs = self.select_txs_for_eb(shard, pipeline);
                let ebs = self.select_ebs_for_eb(pipeline);
                let bytes = self.sim_config.sizes.eb(txs.len(), 0, ebs.len());
                let eb = EndorserBlock {
                    slot,
                    pipeline,
                    producer: self.id,
                    shard,
                    bytes,
                    txs,
                    ebs,
                };
                self.queued.schedule_cpu_task(CpuTask::EBBlockGenerated(eb));
                // A node should only generate at most 1 EB per slot
                return;
            }
        }
        if self.sim_config.emit_conformance_events {
            self.tracker.track_no_eb_generated(self.id, slot);
        }
    }

    fn find_available_shards(&self, slot: u64) -> Vec<u64> {
        let period = slot / self.sim_config.ib_shard_period_slots;
        let group = period % self.sim_config.ib_shard_groups;
        let shards_per_group = self.sim_config.ib_shards / self.sim_config.ib_shard_groups;
        (group * shards_per_group..(group + 1) * shards_per_group).collect()
    }

    fn select_txs_for_eb(&mut self, shard: u64, pipeline: u64) -> Vec<Arc<Transaction>> {
        let mut txs = vec![];
        if self.sim_config.eb_include_txs_from_previous_stage {
            if let Some(eb_from_last_pipeline) =
                self.leios.ebs_by_pipeline.get(&pipeline).and_then(|ebs| {
                    ebs.iter()
                        .find_map(|eb_id| match self.leios.ebs.get(eb_id) {
                            Some(EndorserBlockView::Received { eb, .. }) => Some(eb),
                            _ => None,
                        })
                })
            {
                // include TXs from the first EB in the last pipeline
                for tx in &eb_from_last_pipeline.txs {
                    if matches!(self.txs.get(&tx.id), Some(TransactionView::Received(_))) {
                        txs.push(tx.clone());
                    }
                }
            }
        }
        self.sample_from_leios_mempool(&mut txs, shard, pipeline);
        txs
    }

    fn select_ebs_for_eb(&self, pipeline: u64) -> Vec<EndorserBlockId> {
        let Some(referenced_pipelines) = self.pipelines_for_eb_references(pipeline) else {
            return vec![];
        };

        // include one certified EB from each of these pipelines
        let mut ebs = vec![];
        for referenced_pipeline in referenced_pipelines {
            if let Some(eb) = self.choose_endorsed_block_from_pipeline(referenced_pipeline) {
                ebs.push(eb);
            }
        }
        ebs
    }

    fn pipelines_for_eb_references(
        &self,
        pipeline: u64,
    ) -> Option<impl Iterator<Item = u64> + use<'_>> {
        // The newest pipeline to include EBs from is i-1, where i is the current pipeline.
        let Some(newest_included_pipeline) = pipeline.checked_sub(1) else {
            // If this is the first pipeline, just don't recurse.
            return None;
        };

        // the oldest pipeline is i-⌈3η/L⌉, where i is the current pipeline,
        // η is the "quality parameter" (expected block rate), and L is stage length.
        let old_pipelines =
            (3 * self.sim_config.praos_chain_quality).div_ceil(self.sim_config.stage_length);
        let oldest_included_pipeline = pipeline
            .checked_sub(old_pipelines)
            .unwrap_or(newest_included_pipeline);

        Some(oldest_included_pipeline..=newest_included_pipeline)
    }

    fn finish_generating_eb(&mut self, eb: EndorserBlock) {
        let eb = Arc::new(eb);
        self.tracker.track_stracciatella_eb_generated(&eb);

        let id = eb.id();
        self.leios.ebs.insert(
            id,
            EndorserBlockView::Received {
                eb: eb.clone(),
                finalized: false,
            },
        );
        self.leios
            .ebs_by_pipeline
            .entry(id.pipeline)
            .or_default()
            .push(id);
        for peer in &self.consumers {
            self.queued.send_to(*peer, Message::AnnounceEB(id));
        }
    }

    fn receive_announce_eb(&mut self, from: NodeId, id: EndorserBlockId) {
        if self.leios.ebs.get(&id).is_none_or(|eb| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(eb, EndorserBlockView::Pending)
        }) {
            self.leios.ebs.insert(id, EndorserBlockView::Pending);
            self.queued.send_to(from, Message::RequestEB(id));
        }
    }

    fn receive_request_eb(&mut self, from: NodeId, id: EndorserBlockId) {
        if let Some(EndorserBlockView::Received { eb, .. }) = self.leios.ebs.get(&id) {
            self.tracker.track_stracciatella_eb_sent(eb, self.id, from);
            self.queued.send_to(from, Message::EB(eb.clone()));
        }
    }

    fn receive_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) {
        self.tracker.track_eb_received(eb.id(), from, self.id);
        self.queued
            .schedule_cpu_task(CpuTask::EBBlockValidated(from, eb));
    }

    fn finish_validating_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) {
        let id = eb.id();
        let eb_view = match self.leios.ebs.entry(id) {
            Entry::Vacant(e) => e.insert(EndorserBlockView::Received {
                eb,
                finalized: false,
            }),
            Entry::Occupied(mut e) => {
                if matches!(e.get(), EndorserBlockView::Received { .. }) {
                    return;
                }
                e.insert(EndorserBlockView::Received {
                    eb,
                    finalized: false,
                });
                e.into_mut()
            }
        };
        let eb = eb_view.eb().unwrap().clone();
        self.remove_eb_txs_from_mempools(&eb);
        self.leios
            .ebs_by_pipeline
            .entry(id.pipeline)
            .or_default()
            .push(id);
        // We haven't seen this EB before, so propagate it to our neighbors
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued.send_to(*peer, Message::AnnounceEB(id));
        }
    }
}

// vote/endorsement operations
impl StracciatellaLeiosNode {
    fn schedule_endorser_block_votes(&mut self, slot: u64) {
        let vrf_wins = lottery::vrf_probabilities(self.sim_config.vote_probability)
            .filter_map(|f| self.run_vrf(f))
            .count();
        if vrf_wins == 0 {
            return;
        }
        // Each node chooses a slot at random in which to produce all its votes.
        // Randomness spreads out vote generation across the whole network to make traffic less spiky,
        // but each node generates all votes for a pipeline at once to minimize overall traffic.
        let new_slot = slot + self.rng.random_range(0..self.sim_config.vote_slot_length);
        self.tracker.track_vote_lottery_won(VoteBundleId {
            slot: new_slot,
            pipeline: self.slot_to_pipeline(new_slot),
            producer: self.id,
        });
        self.leios.votes_to_generate.insert(new_slot, vrf_wins);
    }

    fn vote_for_endorser_blocks(&mut self, slot: u64) {
        let pipeline = self.slot_to_pipeline(slot);
        if pipeline < 4 {
            // The first pipeline with IBs in it is pipeline 4.
            // Don't try voting before that pipeline, because there's nothing to vote for.
            return;
        }
        if !self.try_vote_for_endorser_blocks(slot) && self.sim_config.emit_conformance_events {
            self.tracker.track_no_vote_generated(self.id, slot);
        }
    }

    fn try_vote_for_endorser_blocks(&mut self, slot: u64) -> bool {
        let Some(vote_count) = self.leios.votes_to_generate.remove(&slot) else {
            return false;
        };
        // When we vote, we vote for EBs which were sent at the start of the prior stage.
        let Some(eb_pipeline) = (slot / self.sim_config.stage_length).checked_sub(1) else {
            return false;
        };
        let Some(eb_ids) = self.leios.ebs_by_pipeline.get(&eb_pipeline) else {
            return false;
        };
        let mut ebs: Vec<_> = eb_ids
            .iter()
            .map(|eb_id| {
                let Some(EndorserBlockView::Received { eb, .. }) = self.leios.ebs.get(eb_id) else {
                    panic!("Tried voting for EB which we haven't received");
                };
                eb.clone()
            })
            .collect();
        ebs.retain(|eb| match self.should_vote_for(eb) {
            Ok(()) => true,
            Err(reason) => {
                self.tracker.track_no_vote(
                    slot,
                    self.slot_to_pipeline(slot),
                    self.id,
                    eb.id(),
                    reason,
                );
                false
            }
        });
        if ebs.is_empty() {
            return false;
        }
        // For every VRF lottery you won, you can vote for every EB
        let votes_allowed = vote_count * eb_ids.len();
        let votes = VoteBundle {
            id: VoteBundleId {
                slot,
                pipeline: self.slot_to_pipeline(slot),
                producer: self.id,
            },
            bytes: self.sim_config.sizes.vote_bundle(ebs.len()),
            ebs: ebs.iter().map(|eb| (eb.id(), votes_allowed)).collect(),
        };
        self.queued
            .schedule_cpu_task(CpuTask::VTBundleGenerated(votes, ebs));
        true
    }

    fn should_vote_for(&self, eb: &EndorserBlock) -> Result<(), NoVoteReason> {
        for tx in &eb.txs {
            if !matches!(self.txs.get(&tx.id), Some(TransactionView::Received(_))) {
                return Err(NoVoteReason::ExtraTX);
            }
        }

        if let Some(expected_eb_pipelines) = self.pipelines_for_eb_references(eb.pipeline) {
            let actual_eb_pipelines: HashSet<u64> = eb.ebs.iter().map(|id| id.pipeline).collect();
            for expected_pipeline in expected_eb_pipelines {
                let saw_certified_eb = self
                    .leios
                    .earliest_eb_cert_times_by_pipeline
                    .get(&expected_pipeline)
                    .is_some_and(|certified_at| {
                        let last_pipeline_slot =
                            (expected_pipeline + 1) * self.sim_config.stage_length - 1;
                        let cutoff = Timestamp::from_secs(last_pipeline_slot)
                            .checked_sub_duration(self.sim_config.header_diffusion_time)
                            .unwrap_or_default();
                        certified_at <= &cutoff
                    });
                if saw_certified_eb && !actual_eb_pipelines.contains(&expected_pipeline) {
                    // We saw at least one certified EB for this pipeline, so we should have included one.
                    return Err(NoVoteReason::MissingEB);
                }
            }
        }

        // If this EB _does_ reference other EBs, make sure we trust them
        for referenced_eb in &eb.ebs {
            let Some(votes) = self.leios.votes_by_eb.get(referenced_eb) else {
                return Err(NoVoteReason::UncertifiedEBReference);
            };
            let vote_count = votes.values().copied().sum::<usize>() as u64;
            if vote_count < self.sim_config.vote_threshold {
                return Err(NoVoteReason::UncertifiedEBReference);
            }
        }
        Ok(())
    }

    fn finish_generating_vote_bundle(&mut self, votes: VoteBundle) {
        self.tracker.track_votes_generated(&votes);
        for (eb, count) in &votes.ebs {
            let eb_votes = self
                .leios
                .votes_by_eb
                .entry(*eb)
                .or_default()
                .entry(votes.id.producer)
                .or_default();
            *eb_votes += count;
            if *eb_votes as u64 > self.sim_config.vote_threshold {
                self.leios
                    .earliest_eb_cert_times_by_pipeline
                    .entry(eb.pipeline)
                    .or_insert(self.clock.now());
            }
        }
        let votes = Arc::new(votes);
        self.leios
            .votes
            .insert(votes.id, VoteBundleView::Received(votes.clone()));
        for peer in &self.consumers {
            self.queued.send_to(*peer, Message::AnnounceVotes(votes.id));
        }
    }

    fn receive_announce_votes(&mut self, from: NodeId, id: VoteBundleId) {
        if self.leios.votes.get(&id).is_none_or(|v| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(v, VoteBundleView::Requested)
        }) {
            self.leios.votes.insert(id, VoteBundleView::Requested);
            self.queued.send_to(from, Message::RequestVotes(id));
        }
    }

    fn receive_request_votes(&mut self, from: NodeId, id: VoteBundleId) {
        if let Some(VoteBundleView::Received(votes)) = self.leios.votes.get(&id) {
            self.tracker.track_votes_sent(votes, self.id, from);
            self.queued.send_to(from, Message::Votes(votes.clone()));
        }
    }

    fn receive_votes(&mut self, from: NodeId, votes: Arc<VoteBundle>) {
        self.tracker.track_votes_received(&votes, from, self.id);
        self.queued
            .schedule_cpu_task(CpuTask::VTBundleValidated(from, votes));
    }

    fn finish_validating_vote_bundle(&mut self, from: NodeId, votes: Arc<VoteBundle>) {
        let id = votes.id;
        if self
            .leios
            .votes
            .insert(id, VoteBundleView::Received(votes.clone()))
            .is_some_and(|v| matches!(v, VoteBundleView::Received(_)))
        {
            return;
        }
        for (eb, count) in votes.ebs.iter() {
            let eb_votes = self
                .leios
                .votes_by_eb
                .entry(*eb)
                .or_default()
                .entry(votes.id.producer)
                .or_default();
            *eb_votes += count;
            if *eb_votes as u64 >= self.sim_config.vote_threshold {
                self.leios
                    .earliest_eb_cert_times_by_pipeline
                    .entry(eb.pipeline)
                    .or_insert(self.clock.now());
            }
        }
        // We haven't seen these votes before, so propagate them to our neighbors
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued.send_to(*peer, Message::AnnounceVotes(id));
        }
    }

    fn choose_endorsed_block_for_rb(&self, slot: u64) -> Option<Endorsement> {
        // an EB is eligible to be included on-chain if it has this many votes
        let vote_threshold = self.sim_config.vote_threshold;
        // and it is not older than this
        let max_eb_age = self.sim_config.max_eb_age;
        // and if it is not in a pipeline already represented in the chain
        // (NB: all EBs produced in a pipeline are produced during the same slot)
        let forbidden_slots: HashSet<u64> = self
            .praos
            .blocks
            .values()
            .filter_map(|rb| rb.endorsement.as_ref())
            .map(|e| e.eb.slot)
            .collect();

        let candidates = self.leios.votes_by_eb.iter().filter_map(|(eb, votes)| {
            let age = slot - eb.slot;
            if age > max_eb_age || forbidden_slots.contains(&eb.slot) {
                return None;
            }
            let vote_count: usize = votes.values().sum();
            if (vote_count as u64) < vote_threshold {
                return None;
            }
            Some((eb, age, vote_count))
        });

        // Choose an EB based on, in order,
        //  - the age of the EB (older EBs take priority in Short Leios, newer in Full)
        //  - the TXs in the EB (more TXs take priority)
        //  - the number of votes (more votes is better)
        let (&block, _, _) = candidates
            .max_by_key(|(eb, age, votes)| (Reverse(*age), self.count_txs_in_eb(eb), *votes))?;

        let votes = self.leios.votes_by_eb.get(&block)?.clone();
        let size_bytes = self.sim_config.sizes.cert(votes.len());

        Some(Endorsement {
            eb: block,
            size_bytes,
            votes,
        })
    }

    fn choose_endorsed_block_from_pipeline(&self, pipeline: u64) -> Option<EndorserBlockId> {
        // an EB is eligible for endorsement if it has this many votes
        let vote_threshold = self.sim_config.vote_threshold;

        // Choose an EB based on, in order,
        //  - the TXs in the EB (more TXs take priority)
        //  - the number of votes (more votes is better)
        let (&block, _) = self
            .leios
            .ebs_by_pipeline
            .get(&pipeline)
            .iter()
            .flat_map(|ids| ids.iter())
            .filter_map(|eb| {
                let votes = self.leios.votes_by_eb.get(eb)?;
                let vote_count: usize = votes.values().sum();
                if (vote_count as u64) < vote_threshold {
                    return None;
                }
                Some((eb, vote_count))
            })
            .max_by_key(|(eb, votes)| (self.count_txs_in_eb(eb), *votes))?;

        Some(block)
    }

    fn count_txs_in_eb(&self, eb_id: &EndorserBlockId) -> Option<usize> {
        match self.leios.ebs.get(eb_id) {
            Some(EndorserBlockView::Received { eb, .. }) => Some(eb.txs.len()),
            _ => None,
        }
    }
}

// Ledger/mempool operations
impl StracciatellaLeiosNode {
    fn sample_from_praos_mempool(&mut self, txs: &mut Vec<Arc<Transaction>>) {
        let mut size = 0;
        let mut candidates: Vec<_> = self.praos.mempool.keys().copied().collect();
        if matches!(
            self.sim_config.mempool_strategy,
            MempoolSamplingStrategy::Random
        ) {
            candidates.shuffle(&mut self.rng);
        } else {
            candidates.reverse();
        }

        // Fill with as many pending transactions as can fit
        while let Some(id) = candidates.pop() {
            let tx = self.praos.mempool.get(&id).unwrap();
            if size + tx.bytes > self.sim_config.max_block_size {
                break;
            }
            size += tx.bytes;
            txs.push(self.praos.mempool.remove(&id).unwrap());
            self.leios.mempool.remove(&id);
        }
    }
    fn sample_from_leios_mempool(
        &mut self,
        txs: &mut Vec<Arc<Transaction>>,
        shard: u64,
        pipeline: u64,
    ) {
        let Some(last_legal_slot) =
            (pipeline * self.sim_config.stage_length).checked_sub(self.sim_config.stage_length)
        else {
            return;
        };
        let max_seen_at = Timestamp::from_secs(last_legal_slot);
        let shard_count = self.sim_config.ib_shards;

        let can_include_tx = |seen: &SeenTransaction| {
            if seen.seen_at >= max_seen_at {
                return false;
            }
            for tx_shard in seen.tx.shard..=seen.tx.shard + seen.tx.overcollateralization_factor {
                let tx_shard = tx_shard % shard_count;
                if tx_shard == shard {
                    return true;
                }
            }
            false
        };

        let mut size = 0;
        let mut candidates: Vec<_> = self.leios.mempool.keys().copied().collect();
        if matches!(
            self.sim_config.mempool_strategy,
            MempoolSamplingStrategy::Random
        ) {
            candidates.shuffle(&mut self.rng);
        } else {
            candidates.reverse();
        }

        // Fill with as many pending transactions as can fit
        while let Some(id) = candidates.pop() {
            let seen = self.leios.mempool.get(&id).unwrap();
            if !can_include_tx(seen) {
                continue;
            }
            if size + seen.tx.bytes > self.sim_config.max_eb_size {
                break;
            }
            size += seen.tx.bytes;
            txs.push(self.leios.mempool.remove(&id).unwrap().tx);
        }
    }

    fn remove_rb_txs_from_mempools(&mut self, rb: &RankingBlock) {
        let mut txs = rb.transactions.clone();
        if let Some(endorsement) = &rb.endorsement {
            if let Some(EndorserBlockView::Received { eb, .. }) =
                self.leios.ebs.get(&endorsement.eb)
            {
                txs.extend(eb.txs.iter().cloned());
            }
        }
        self.remove_txs_from_mempools(&txs);
    }

    fn remove_endorsed_txs_from_mempools(&mut self, endorsement: &Endorsement) {
        let mut eb_queue = vec![endorsement.eb];
        let mut txs_to_remove = vec![];
        while let Some(eb_id) = eb_queue.pop() {
            let Some(eb) = self.leios.ebs.get(&eb_id) else {
                continue;
            };
            let EndorserBlockView::Received {
                eb,
                finalized: false,
            } = eb
            else {
                // TXs from finalized EBs have already been removed from the mempool
                continue;
            };
            txs_to_remove.extend_from_slice(&eb.txs);
            for eb_id in &eb.ebs {
                eb_queue.push(*eb_id);
            }
            self.leios.ebs.insert(
                eb_id,
                EndorserBlockView::Received {
                    eb: eb.clone(),
                    finalized: true,
                },
            );
        }
        self.remove_txs_from_mempools(&txs_to_remove);
    }

    fn remove_eb_txs_from_mempools(&mut self, eb: &EndorserBlock) {
        for tx in &eb.txs {
            // Do not include transactions from this EB in any EBs we produce ourselves.
            self.leios.mempool.remove(&tx.id);
        }
        if self.sim_config.mempool_aggressive_pruning {
            // If we're using aggressive pruning, remove transactions from the mempool if they conflict with transactions in this EB
            self.leios
                .input_ids_in_flight
                .extend(eb.txs.iter().map(|tx| tx.input_id));
            self.leios
                .mempool
                .retain(|_, seen| !self.leios.input_ids_in_flight.contains(&seen.tx.input_id));
        }
    }

    fn remove_txs_from_mempools(&mut self, txs: &[Arc<Transaction>]) {
        let inputs = txs.iter().map(|tx| tx.input_id).collect::<HashSet<_>>();
        self.praos
            .mempool
            .retain(|_, tx| !inputs.contains(&tx.input_id));
        self.leios
            .mempool
            .retain(|_, seen| !inputs.contains(&seen.tx.input_id));
    }

    fn resolve_ledger_state(&mut self, rb_ref: Option<BlockId>) -> Arc<LedgerState> {
        let Some(block_id) = rb_ref else {
            return Arc::new(LedgerState::default());
        };
        if let Some(state) = self.ledger_states.get(&block_id) {
            return state.clone();
        };

        let mut state = self
            .ledger_states
            .last_key_value()
            .map(|(_, v)| v.as_ref().clone())
            .unwrap_or_default();

        let mut block_queue = vec![block_id];
        while let Some(block_id) = block_queue.pop() {
            if !state.seen_blocks.insert(block_id) {
                continue;
            }
            let Some(rb) = self.praos.blocks.get(&block_id) else {
                continue;
            };
            if let Some(parent) = rb.parent {
                block_queue.push(parent);
            }
            for tx in &rb.transactions {
                state.spent_inputs.insert(tx.input_id);
            }

            let mut eb_queue = vec![];
            if let Some(endorsement) = &rb.endorsement {
                eb_queue.push(endorsement.eb);
            }
            while let Some(eb_id) = eb_queue.pop() {
                if !state.seen_ebs.insert(eb_id) {
                    continue;
                }
                let Some(EndorserBlockView::Received { eb, .. }) = self.leios.ebs.get(&eb_id)
                else {
                    continue;
                };
                for tx in &eb.txs {
                    state.spent_inputs.insert(tx.input_id);
                }
                for eb_id in &eb.ebs {
                    eb_queue.push(*eb_id);
                }
            }
        }

        let state = Arc::new(state);
        self.ledger_states.insert(block_id, state.clone());
        state
    }
}

// Common utilities
impl StracciatellaLeiosNode {
    // Simulates the output of a VRF using this node's stake (if any).
    fn run_vrf(&mut self, success_rate: f64) -> Option<u64> {
        let target_vrf_stake = lottery::compute_target_vrf_stake(
            self.stake,
            self.sim_config.total_stake,
            success_rate,
        );
        let result = self.rng.random_range(0..self.sim_config.total_stake);
        if result < target_vrf_stake {
            Some(result)
        } else {
            None
        }
    }

    fn slot_to_pipeline(&self, slot: u64) -> u64 {
        slot / self.sim_config.stage_length
    }
}
