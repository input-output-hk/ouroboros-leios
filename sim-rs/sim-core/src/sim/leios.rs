use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    hash::Hash,
    sync::Arc,
    time::Duration,
};

use anyhow::Result;
use priority_queue::PriorityQueue;
use rand::{Rng as _, seq::SliceRandom as _};
use rand_chacha::ChaChaRng;
use tracing::info;

use crate::{
    clock::{Clock, Timestamp},
    config::{
        DiffusionStrategy, LeiosVariant, MempoolSamplingStrategy, NodeBehaviours,
        NodeConfiguration, NodeId, RelayStrategy, SimConfiguration, TransactionConfig,
    },
    events::EventTracker,
    model::{
        Block, BlockId, Endorsement, EndorserBlock, EndorserBlockId, InputBlock, InputBlockHeader,
        InputBlockId, NoVoteReason, Transaction, TransactionId, VoteBundle, VoteBundleId,
    },
    sim::{MiniProtocol, NodeImpl, SimCpuTask, SimMessage, lottery},
};

enum TransactionView {
    Pending,
    Received(Arc<Transaction>),
}

#[derive(Clone, Debug)]
pub enum SimulationMessage {
    // tx "propagation"
    AnnounceTx(TransactionId),
    RequestTx(TransactionId),
    Tx(Arc<Transaction>),
    // praos block propagation
    RollForward(BlockId),
    RequestBlock(BlockId),
    Block(Arc<Block>),
    // IB header propagation
    AnnounceIBHeader(InputBlockId),
    RequestIBHeader(InputBlockId),
    IBHeader(InputBlockHeader, bool /* has_body */),
    // IB transmission
    AnnounceIB(InputBlockId),
    RequestIB(InputBlockId),
    IB(Arc<InputBlock>),
    // EB propagation
    AnnounceEB(EndorserBlockId),
    RequestEB(EndorserBlockId),
    EB(Arc<EndorserBlock>),
    // Get out the vote
    AnnounceVotes(VoteBundleId),
    RequestVotes(VoteBundleId),
    Votes(Arc<VoteBundle>),
}

impl SimMessage for SimulationMessage {
    fn protocol(&self) -> MiniProtocol {
        match self {
            Self::AnnounceTx(_) => MiniProtocol::Tx,
            Self::RequestTx(_) => MiniProtocol::Tx,
            Self::Tx(_) => MiniProtocol::Tx,

            Self::RollForward(_) => MiniProtocol::Block,
            Self::RequestBlock(_) => MiniProtocol::Block,
            Self::Block(_) => MiniProtocol::Block,

            Self::AnnounceIBHeader(_) => MiniProtocol::IB,
            Self::RequestIBHeader(_) => MiniProtocol::IB,
            Self::IBHeader(_, _) => MiniProtocol::IB,

            Self::AnnounceIB(_) => MiniProtocol::IB,
            Self::RequestIB(_) => MiniProtocol::IB,
            Self::IB(_) => MiniProtocol::IB,

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

            Self::RollForward(_) => 8,
            Self::RequestBlock(_) => 8,
            Self::Block(block) => block.bytes(),

            Self::AnnounceIBHeader(_) => 8,
            Self::RequestIBHeader(_) => 8,
            Self::IBHeader(header, _) => header.bytes,

            Self::AnnounceIB(_) => 8,
            Self::RequestIB(_) => 8,
            Self::IB(ib) => ib.bytes(),

            Self::AnnounceEB(_) => 8,
            Self::RequestEB(_) => 8,
            Self::EB(eb) => eb.bytes,

            Self::AnnounceVotes(_) => 8,
            Self::RequestVotes(_) => 8,
            Self::Votes(v) => v.bytes,
        }
    }
}

pub enum Task {
    /// A transaction has been received and validated, and is ready to propagate
    TransactionValidated(NodeId, Arc<Transaction>),
    /// A Praos block has been generated and is ready to propagate
    RBBlockGenerated(Block),
    /// A Praos block has been received and validated, and is ready to propagate
    RBBlockValidated(NodeId, Arc<Block>),
    /// An input block has been generated and is ready to propagate
    IBBlockGenerated(InputBlock),
    /// An IB header has been received and validated, and is ready to propagate
    IBHeaderValidated(NodeId, InputBlockHeader, bool),
    /// An input block has been received and validated, and is ready to propagate
    IBBlockValidated(NodeId, Arc<InputBlock>),
    /// An endorser block has been generated and is ready to propagate
    EBBlockGenerated(EndorserBlock),
    /// An endorser block has been received and validated, and is ready to propagate
    EBBlockValidated(NodeId, Arc<EndorserBlock>),
    /// A bundle of votes has been generated and is ready to propagate
    VTBundleGenerated(VoteBundle, Vec<Arc<EndorserBlock>>),
    /// A bundle of votes has been received and validated, and is ready to propagate
    VTBundleValidated(NodeId, Arc<VoteBundle>),
}

impl SimCpuTask for Task {
    fn name(&self) -> String {
        match self {
            Self::TransactionValidated(_, _) => "ValTX",
            Self::RBBlockGenerated(_) => "GenRB",
            Self::RBBlockValidated(_, _) => "ValRB",
            Self::IBBlockGenerated(_) => "GenIB",
            Self::IBHeaderValidated(_, _, _) => "ValIH",
            Self::IBBlockValidated(_, _) => "ValIB",
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
            Self::IBBlockGenerated(id) => id.header.id.to_string(),
            Self::IBHeaderValidated(_, id, _) => id.id.to_string(),
            Self::IBBlockValidated(_, id) => id.header.id.to_string(),
            Self::EBBlockGenerated(_) => "".to_string(),
            Self::EBBlockValidated(_, _) => "".to_string(),
            Self::VTBundleGenerated(_, _) => "".to_string(),
            Self::VTBundleValidated(_, _) => "".to_string(),
        }
    }

    fn times(&self, config: &crate::config::CpuTimeConfig) -> Vec<Duration> {
        match self {
            Self::TransactionValidated(_, _) => vec![config.tx_validation],
            Self::RBBlockGenerated(block) => {
                let mut time = config.rb_generation;
                if let Some(endorsement) = &block.endorsement {
                    let nodes = endorsement.votes.len();
                    time += config.cert_generation_constant
                        + (config.cert_generation_per_node * nodes as u32)
                }
                vec![time]
            }
            Self::RBBlockValidated(_, rb) => {
                let mut time = config.rb_head_validation + config.rb_body_validation_constant;
                let bytes: u64 = rb.transactions.iter().map(|tx| tx.bytes).sum();
                time += config.rb_validation_per_byte * (bytes as u32);
                if let Some(endorsement) = &rb.endorsement {
                    let nodes = endorsement.votes.len();
                    time += config.cert_validation_constant
                        + (config.cert_validation_per_node * nodes as u32)
                }
                vec![time]
            }
            Self::IBBlockGenerated(_) => vec![config.ib_generation],
            Self::IBHeaderValidated(_, _, _) => vec![config.ib_head_validation],
            Self::IBBlockValidated(_, ib) => {
                let total_tx_bytes: u64 = ib.transactions.iter().map(|tx| tx.bytes).sum();
                vec![
                    config.ib_body_validation_constant
                        + (config.ib_body_validation_per_byte * total_tx_bytes as u32),
                ]
            }
            Self::EBBlockGenerated(_) => vec![config.eb_generation],
            Self::EBBlockValidated(_, _) => vec![config.eb_validation],
            Self::VTBundleGenerated(_, ebs) => ebs
                .iter()
                .map(|eb| {
                    config.vote_generation_constant
                        + (config.vote_generation_per_ib * eb.ibs.len() as u32)
                })
                .collect(),
            Self::VTBundleValidated(_, votes) => {
                std::iter::repeat_n(config.vote_validation, votes.ebs.len()).collect()
            }
        }
    }
}

#[derive(Clone, Default)]
struct LedgerState {
    spent_inputs: HashSet<u64>,
    seen_blocks: HashSet<BlockId>,
    seen_ebs: HashSet<EndorserBlockId>,
}

pub struct LeiosNode {
    id: NodeId,
    name: String,
    trace: bool,
    sim_config: Arc<SimConfiguration>,
    queued: EventResult,
    tracker: EventTracker,
    rng: ChaChaRng,
    clock: Clock,
    stake: u64,
    consumers: Vec<NodeId>,
    behaviours: NodeBehaviours,
    txs: HashMap<TransactionId, TransactionView>,
    ledger_states: BTreeMap<BlockId, Arc<LedgerState>>,
    praos: NodePraosState,
    leios: NodeLeiosState,
}

#[derive(Default)]
struct NodePraosState {
    mempool: BTreeMap<TransactionId, Arc<Transaction>>,
    peer_heads: BTreeMap<NodeId, u64>,
    blocks_seen: BTreeSet<BlockId>,
    blocks: BTreeMap<BlockId, Arc<Block>>,
    block_ids_by_slot: BTreeMap<u64, BlockId>,
}

#[derive(Default)]
struct NodeLeiosState {
    mempool: BTreeMap<TransactionId, Arc<Transaction>>,
    input_ids_in_flight: HashSet<u64>,
    ibs_to_generate: BTreeMap<u64, Vec<u64>>,
    ibs: BTreeMap<InputBlockId, InputBlockState>,
    ib_requests: BTreeMap<NodeId, PeerInputBlockRequests>,
    ibs_by_vrf: BTreeMap<u64, Vec<InputBlockId>>,
    ibs_by_pipeline: BTreeMap<u64, Vec<InputBlockId>>,
    ebs: BTreeMap<EndorserBlockId, EndorserBlockState>,
    ebs_by_pipeline: BTreeMap<u64, Vec<EndorserBlockId>>,
    earliest_eb_cert_times_by_pipeline: BTreeMap<u64, Timestamp>,
    votes_to_generate: BTreeMap<u64, usize>,
    votes_by_eb: BTreeMap<EndorserBlockId, BTreeMap<NodeId, usize>>,
    votes: BTreeMap<VoteBundleId, VoteBundleState>,
}

enum InputBlockState {
    HeaderPending,
    Pending {
        header: InputBlockHeader,
        header_seen: Timestamp,
    },
    Requested {
        header: InputBlockHeader,
        header_seen: Timestamp,
    },
    Received {
        ib: Arc<InputBlock>,
        header_seen: Timestamp,
    },
}
impl InputBlockState {
    fn header(&self) -> Option<&InputBlockHeader> {
        match self {
            Self::HeaderPending => None,
            Self::Pending { header, .. } => Some(header),
            Self::Requested { header, .. } => Some(header),
            Self::Received { ib, .. } => Some(&ib.header),
        }
    }
    fn header_seen(&self) -> Option<Timestamp> {
        match self {
            Self::HeaderPending => None,
            Self::Pending { header_seen, .. } => Some(*header_seen),
            Self::Requested { header_seen, .. } => Some(*header_seen),
            Self::Received { header_seen, .. } => Some(*header_seen),
        }
    }
}

enum EndorserBlockState {
    Pending,
    Received {
        eb: Arc<EndorserBlock>,
        finalized: bool,
    },
}

enum VoteBundleState {
    Requested,
    Received(Arc<VoteBundle>),
}

struct PeerInputBlockRequests {
    pending: PendingQueue<InputBlockId>,
    active: HashSet<InputBlockId>,
}
enum PendingQueue<T: Hash + Eq> {
    PeerOrder(VecDeque<T>),
    FreshestFirst(PriorityQueue<T, Timestamp>),
    OldestFirst(PriorityQueue<T, Reverse<Timestamp>>),
}
impl<T: Hash + Eq> PendingQueue<T> {
    fn new(strategy: DiffusionStrategy) -> Self {
        match strategy {
            DiffusionStrategy::PeerOrder => Self::PeerOrder(VecDeque::new()),
            DiffusionStrategy::FreshestFirst => Self::FreshestFirst(PriorityQueue::new()),
            DiffusionStrategy::OldestFirst => Self::OldestFirst(PriorityQueue::new()),
        }
    }
    fn push(&mut self, value: T, timestamp: Timestamp) {
        match self {
            Self::PeerOrder(queue) => queue.push_back(value),
            Self::FreshestFirst(queue) => {
                queue.push(value, timestamp);
            }
            Self::OldestFirst(queue) => {
                queue.push(value, Reverse(timestamp));
            }
        }
    }
    fn pop(&mut self) -> Option<T> {
        match self {
            Self::PeerOrder(queue) => queue.pop_back(),
            Self::FreshestFirst(queue) => queue.pop().map(|(value, _)| value),
            Self::OldestFirst(queue) => queue.pop().map(|(value, _)| value),
        }
    }
}

impl PeerInputBlockRequests {
    fn new(config: &SimConfiguration) -> Self {
        Self {
            pending: PendingQueue::new(config.ib_diffusion_strategy),
            active: HashSet::new(),
        }
    }

    fn queue(&mut self, id: InputBlockId, timestamp: Timestamp) {
        self.pending.push(id, timestamp);
    }

    fn next(&mut self) -> Option<InputBlockId> {
        self.pending.pop()
    }
}

type EventResult = super::EventResult<SimulationMessage, Task>;

impl NodeImpl for LeiosNode {
    type Task = Task;
    type Message = SimulationMessage;

    fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: Clock,
    ) -> Self {
        let id = config.id;
        let stake = config.stake;
        let consumers = config.consumers.clone();
        let behaviours = config.behaviours.clone();

        Self {
            id,
            name: config.name.clone(),
            trace: sim_config.trace_nodes.contains(&id),
            sim_config,
            queued: EventResult::default(),
            tracker,
            rng,
            clock,
            stake,
            consumers,
            behaviours,
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

            // Decide how many IBs to generate in each slot.
            self.schedule_input_block_generation(slot);

            // Vote for any EBs which satisfy all requirements.
            self.vote_for_endorser_blocks(slot);
        }

        // Generate any IBs scheduled for this slot.
        self.generate_input_blocks(slot);

        self.try_generate_praos_block(slot);

        std::mem::take(&mut self.queued)
    }

    fn handle_new_tx(&mut self, tx: Arc<Transaction>) -> EventResult {
        self.generate_tx(tx);

        std::mem::take(&mut self.queued)
    }

    fn handle_message(&mut self, from: NodeId, msg: SimulationMessage) -> EventResult {
        match msg {
            // TX propagation
            SimulationMessage::AnnounceTx(id) => {
                self.receive_announce_tx(from, id);
            }
            SimulationMessage::RequestTx(id) => {
                self.receive_request_tx(from, id);
            }
            SimulationMessage::Tx(tx) => {
                self.receive_tx(from, tx);
            }

            // Block propagation
            SimulationMessage::RollForward(id) => {
                self.receive_roll_forward(from, id);
            }
            SimulationMessage::RequestBlock(id) => {
                self.receive_request_block(from, id);
            }
            SimulationMessage::Block(block) => {
                self.receive_block(from, block);
            }

            // IB header propagation
            SimulationMessage::AnnounceIBHeader(id) => {
                self.receive_announce_ib_header(from, id);
            }
            SimulationMessage::RequestIBHeader(id) => {
                self.receive_request_ib_header(from, id);
            }
            SimulationMessage::IBHeader(header, has_body) => {
                self.receive_ib_header(from, header, has_body);
            }

            // IB transmission
            SimulationMessage::AnnounceIB(id) => {
                self.receive_announce_ib(from, id);
            }
            SimulationMessage::RequestIB(id) => {
                self.receive_request_ib(from, id);
            }
            SimulationMessage::IB(ib) => {
                self.receive_ib(from, ib);
            }

            // EB propagation
            SimulationMessage::AnnounceEB(id) => {
                self.receive_announce_eb(from, id);
            }
            SimulationMessage::RequestEB(id) => {
                self.receive_request_eb(from, id);
            }
            SimulationMessage::EB(eb) => {
                self.receive_eb(from, eb);
            }

            // Voting
            SimulationMessage::AnnounceVotes(id) => {
                self.receive_announce_votes(from, id);
            }
            SimulationMessage::RequestVotes(id) => {
                self.receive_request_votes(from, id);
            }
            SimulationMessage::Votes(votes) => {
                self.receive_votes(from, votes);
            }
        }

        std::mem::take(&mut self.queued)
    }

    fn handle_cpu_task(&mut self, task: Task) -> EventResult {
        match task {
            Task::TransactionValidated(from, tx) => self.propagate_tx(from, tx),
            Task::RBBlockGenerated(block) => self.finish_generating_block(block),
            Task::RBBlockValidated(from, block) => self.finish_validating_block(from, block),
            Task::IBBlockGenerated(ib) => self.finish_generating_ib(ib),
            Task::IBHeaderValidated(from, ib, has_body) => {
                self.finish_validating_ib_header(from, ib, has_body)
            }
            Task::IBBlockValidated(from, ib) => self.finish_validating_ib(from, ib),
            Task::EBBlockGenerated(eb) => self.finish_generating_eb(eb),
            Task::EBBlockValidated(from, eb) => self.finish_validating_eb(from, eb),
            Task::VTBundleGenerated(votes, _) => self.finish_generating_vote_bundle(votes),
            Task::VTBundleValidated(from, votes) => self.finish_validating_vote_bundle(from, votes),
        };

        std::mem::take(&mut self.queued)
    }
}

impl LeiosNode {
    fn schedule_input_block_generation(&mut self, slot: u64) {
        let mut slot_vrfs: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
        // IBs are generated at the start of any slot within this stage
        for stage_slot in slot..slot + self.sim_config.stage_length {
            let vrfs: Vec<u64> =
                lottery::vrf_probabilities(self.sim_config.ib_generation_probability)
                    .filter_map(|p| self.run_vrf(p))
                    .collect();
            if !vrfs.is_empty() {
                slot_vrfs.insert(stage_slot, vrfs);
            }
        }
        for (slot, vrfs) in slot_vrfs {
            self.leios.ibs_to_generate.insert(slot, vrfs);
        }
    }

    fn find_available_ib_shards(&self, slot: u64) -> Vec<u64> {
        let period = slot / self.sim_config.ib_shard_period_slots;
        let group = period % self.sim_config.ib_shard_groups;
        let shards_per_group = self.sim_config.ib_shards / self.sim_config.ib_shard_groups;
        (group * shards_per_group..(group + 1) * shards_per_group).collect()
    }

    fn generate_endorser_blocks(&mut self, slot: u64) {
        let pipeline = self.slot_to_pipeline(slot) + 1;
        if pipeline < 4 {
            // The first pipeline with IBs in it is pipeline 4.
            // Don't generate EBs before that pipeline, because they would just be empty.
            return;
        }
        for next_p in lottery::vrf_probabilities(self.sim_config.eb_generation_probability) {
            if self.run_vrf(next_p).is_some() {
                self.tracker.track_eb_lottery_won(EndorserBlockId {
                    slot,
                    pipeline,
                    producer: self.id,
                });
                let ibs = self.select_ibs_for_eb(pipeline);
                let ebs = self.select_ebs_for_eb(pipeline);
                let bytes = self.sim_config.sizes.eb(0, ibs.len(), ebs.len());
                let eb = EndorserBlock {
                    slot,
                    pipeline,
                    producer: self.id,
                    shard: 0,
                    bytes,
                    ibs,
                    ebs,
                };
                self.queued.schedule_cpu_task(Task::EBBlockGenerated(eb));
                // A node should only generate at most 1 EB per slot
                return;
            }
        }
        if self.sim_config.emit_conformance_events {
            self.tracker.track_no_eb_generated(self.id, slot);
        }
    }

    fn schedule_endorser_block_votes(&mut self, slot: u64) {
        let pipeline = self.slot_to_pipeline(slot);
        if pipeline < 4 {
            // The first pipeline with IBs in it is pipeline 4.
            // Don't run the VT lottery before that pipeline, because there's nothing to vote on.
            return;
        }
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
                let Some(EndorserBlockState::Received { eb, .. }) = self.leios.ebs.get(eb_id)
                else {
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
            .schedule_cpu_task(Task::VTBundleGenerated(votes, ebs));
        true
    }

    fn generate_input_blocks(&mut self, slot: u64) {
        let pipeline = self.slot_to_pipeline(slot) + 4;
        let Some(vrfs) = self.leios.ibs_to_generate.remove(&slot) else {
            if self.sim_config.emit_conformance_events {
                self.tracker.track_no_ib_generated(self.id, slot);
            }
            return;
        };
        let shards = self.find_available_ib_shards(slot);
        assert!(!shards.is_empty());
        let mut headers = vec![];
        let mut index = 0;
        for vrf in vrfs {
            let id = InputBlockId {
                slot,
                pipeline,
                producer: self.id,
                index,
            };
            self.leios.ibs_by_vrf.entry(vrf).or_default().push(id);
            self.tracker.track_ib_lottery_won(id);
            index += 1;
            headers.push(InputBlockHeader {
                id,
                vrf,
                shard: shards[vrf as usize % shards.len()],
                timestamp: self.clock.now(),
                bytes: self.sim_config.sizes.ib_header,
            });
            if self.behaviours.ib_equivocation {
                let equivocated_id = InputBlockId {
                    slot,
                    pipeline,
                    producer: self.id,
                    index,
                };
                self.leios
                    .ibs_by_vrf
                    .entry(vrf)
                    .or_default()
                    .push(equivocated_id);
                index += 1;
                headers.push(InputBlockHeader {
                    id: equivocated_id,
                    vrf,
                    shard: shards[vrf as usize % shards.len()],
                    timestamp: self.clock.now(),
                    bytes: self.sim_config.sizes.ib_header,
                });
            }
        }
        for header in headers {
            self.tracker.track_ib_lottery_won(header.id);
            let rb_ref = self.latest_rb_ref();
            let transactions = self.select_txs_for_ib(header.shard, rb_ref);
            let ib = InputBlock {
                header,
                tx_payload_bytes: self.sim_config.sizes.ib_payload(&transactions),
                transactions,
                rb_ref,
            };
            self.queued.schedule_cpu_task(Task::IBBlockGenerated(ib));
        }
    }

    fn try_generate_praos_block(&mut self, slot: u64) {
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
                // Add one transaction, the right size for the extra RB payload
                let tx = config.mock_tx(config.rb_size);
                self.tracker.track_transaction_generated(&tx, self.id);
                transactions.push(Arc::new(tx));
            } else {
                let mut size = 0;
                // Fill a block with as many pending transactions as can fit
                while let Some((id, tx)) = self.praos.mempool.first_key_value() {
                    if size + tx.bytes > self.sim_config.max_block_size {
                        break;
                    }
                    size += tx.bytes;
                    let id = *id;
                    transactions.push(self.praos.mempool.remove(&id).unwrap());
                    self.leios.mempool.remove(&id);
                }
            }
        }

        let parent = self.latest_rb_ref();

        let block = Block {
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
        self.tracker.track_praos_block_lottery_won(block.id);
        self.queued.schedule_cpu_task(Task::RBBlockGenerated(block));
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
            .flat_map(|b| b.endorsement.iter())
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
            if !self.all_ibs_seen(eb) {
                return None;
            }
            Some((eb, age, vote_count))
        });

        // Choose an EB based on, in order,
        //  - the age of the EB (older EBs take priority in Short Leios, newer in Full)
        //  - the TXs in the EB (more TXs take priority)
        //  - the number of votes (more votes is better)
        let (&block, _, _) = match self.sim_config.variant {
            LeiosVariant::Short => candidates
                .max_by_key(|(eb, age, votes)| (*age, self.count_txs_in_eb(eb), *votes))?,
            LeiosVariant::Full | LeiosVariant::FullWithTxReferences => candidates
                .max_by_key(|(eb, age, votes)| (Reverse(*age), self.count_txs_in_eb(eb), *votes))?,
            LeiosVariant::FullWithoutIbs
            | LeiosVariant::Linear
            | LeiosVariant::LinearWithTxReferences => {
                unreachable!("wrong implementation")
            }
        };

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
                // Only select the EB if we have seen all IBs which it references
                if !self.all_ibs_seen(eb) {
                    return None;
                }
                Some((eb, vote_count))
            })
            .max_by_key(|(eb, votes)| (self.count_txs_in_eb(eb), *votes))?;

        Some(block)
    }

    fn remove_endorsed_txs_from_mempools(&mut self, endorsement: &Endorsement) {
        let mut eb_queue = vec![endorsement.eb];
        while let Some(eb_id) = eb_queue.pop() {
            let Some(eb) = self.leios.ebs.get(&eb_id) else {
                continue;
            };
            let EndorserBlockState::Received {
                eb,
                finalized: false,
            } = eb
            else {
                // TXs from finalized EBs have already been removed from the mempool
                continue;
            };
            for ib_id in &eb.ibs {
                let Some(InputBlockState::Received { ib, .. }) = self.leios.ibs.get(ib_id) else {
                    continue;
                };
                for tx in &ib.transactions {
                    self.praos.mempool.remove(&tx.id);
                    self.leios.mempool.remove(&tx.id);
                }
            }
            for eb_id in &eb.ebs {
                eb_queue.push(*eb_id);
            }
            self.leios.ebs.insert(
                eb_id,
                EndorserBlockState::Received {
                    eb: eb.clone(),
                    finalized: true,
                },
            );
        }
    }

    fn all_ibs_seen(&self, eb: &EndorserBlockId) -> bool {
        let Some(EndorserBlockState::Received { eb: eb_body, .. }) = self.leios.ebs.get(eb) else {
            return false;
        };
        eb_body.ibs.iter().all(|ib| {
            matches!(
                self.leios.ibs.get(ib),
                Some(InputBlockState::Received { .. })
            )
        })
    }

    fn count_txs_in_eb(&self, eb_id: &EndorserBlockId) -> Option<usize> {
        let Some(EndorserBlockState::Received { eb, .. }) = self.leios.ebs.get(eb_id) else {
            return None;
        };
        let mut tx_set = HashSet::new();
        for ib_id in &eb.ibs {
            let InputBlockState::Received { ib, .. } = self.leios.ibs.get(ib_id)? else {
                return None;
            };
            for tx in &ib.transactions {
                tx_set.insert(tx.id);
            }
        }
        Some(tx_set.len())
    }

    fn finish_generating_block(&mut self, block: Block) {
        self.tracker.track_praos_block_generated(&block);

        self.publish_block(Arc::new(block))
    }

    fn publish_block(&mut self, block: Arc<Block>) {
        // Remove TXs in these blocks from the mempools.
        for tx in &block.transactions {
            self.praos.mempool.remove(&tx.id);
            self.leios.mempool.remove(&tx.id);
        }
        if let Some(endorsement) = &block.endorsement {
            self.remove_endorsed_txs_from_mempools(endorsement);
        }
        for peer in &self.consumers {
            if self
                .praos
                .peer_heads
                .get(peer)
                .is_none_or(|&s| s < block.id.slot)
            {
                self.queued
                    .send_to(*peer, SimulationMessage::RollForward(block.id));
                self.praos.peer_heads.insert(*peer, block.id.slot);
            }
        }
        self.praos.block_ids_by_slot.insert(block.id.slot, block.id);
        self.praos.blocks.insert(block.id, block);
    }

    fn receive_announce_tx(&mut self, from: NodeId, id: TransactionId) {
        if self.txs.get(&id).is_none_or(|t| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(t, TransactionView::Pending)
        }) {
            self.txs.insert(id, TransactionView::Pending);
            self.queued.send_to(from, SimulationMessage::RequestTx(id));
        }
    }

    fn receive_request_tx(&mut self, from: NodeId, id: TransactionId) {
        if let Some(TransactionView::Received(tx)) = self.txs.get(&id) {
            self.tracker.track_transaction_sent(tx, self.id, from);
            self.queued.send_to(from, SimulationMessage::Tx(tx.clone()));
        }
    }

    fn receive_tx(&mut self, from: NodeId, tx: Arc<Transaction>) {
        self.tracker
            .track_transaction_received(tx.id, from, self.id);
        self.queued
            .schedule_cpu_task(Task::TransactionValidated(from, tx));
    }

    fn generate_tx(&mut self, tx: Arc<Transaction>) {
        self.tracker.track_transaction_generated(&tx, self.id);
        self.propagate_tx(self.id, tx)
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
        if self.trace {
            info!("node {} saw tx {id}", self.name);
        }
        let rb_ref = self.latest_rb_ref();
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
        self.praos.mempool.insert(tx.id, tx.clone());
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued
                .send_to(*peer, SimulationMessage::AnnounceTx(id));
        }
        if self.sim_config.mempool_aggressive_pruning
            && self.leios.input_ids_in_flight.contains(&tx.input_id)
        {
            // Ignoring a TX which conflicts with TXs we've seen in input or endorser blocks.
            // This only affects the Leios mempool; these TXs should still be able to reach the chain through Praos.
            return;
        }
        self.leios.mempool.insert(tx.id, tx);
    }

    fn receive_roll_forward(&mut self, from: NodeId, id: BlockId) {
        if self.praos.blocks_seen.insert(id) {
            self.queued
                .send_to(from, SimulationMessage::RequestBlock(id));
        }
    }

    fn receive_request_block(&mut self, from: NodeId, id: BlockId) {
        if let Some(block) = self.praos.blocks.get(&id) {
            self.tracker.track_praos_block_sent(block, self.id, from);
            self.queued
                .send_to(from, SimulationMessage::Block(block.clone()));
        }
    }

    fn receive_block(&mut self, from: NodeId, block: Arc<Block>) {
        self.tracker
            .track_praos_block_received(&block, from, self.id);
        self.queued
            .schedule_cpu_task(Task::RBBlockValidated(from, block));
    }

    fn finish_validating_block(&mut self, from: NodeId, block: Arc<Block>) {
        if let Some(old_block_id) = self.praos.block_ids_by_slot.get(&block.id.slot) {
            // SLOT BATTLE!!! lower VRF wins
            if let Some(old_block) = self.praos.blocks.get(old_block_id) {
                if old_block.vrf <= block.vrf {
                    // We like our block better than this new one.
                    return;
                }
                self.praos.blocks.remove(old_block_id);
            }
        }
        self.praos.block_ids_by_slot.insert(block.id.slot, block.id);
        self.praos.blocks.insert(block.id, block.clone());

        let head = self.praos.peer_heads.entry(from).or_default();
        if *head < block.id.slot {
            *head = block.id.slot
        }
        self.publish_block(block);
    }

    fn receive_announce_ib_header(&mut self, from: NodeId, id: InputBlockId) {
        if self.leios.ibs.get(&id).is_none_or(|ib| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(ib, InputBlockState::HeaderPending)
        }) {
            self.leios.ibs.insert(id, InputBlockState::HeaderPending);
            self.queued
                .send_to(from, SimulationMessage::RequestIBHeader(id));
        }
    }

    fn receive_request_ib_header(&mut self, from: NodeId, id: InputBlockId) {
        if let Some(ib) = self.leios.ibs.get(&id) {
            if let Some(header) = ib.header() {
                let have_body = matches!(ib, InputBlockState::Received { .. });
                self.queued
                    .send_to(from, SimulationMessage::IBHeader(header.clone(), have_body));
            }
        }
    }

    fn receive_ib_header(&mut self, from: NodeId, header: InputBlockHeader, has_body: bool) {
        let id = header.id;
        if self
            .leios
            .ibs
            .get(&id)
            .is_some_and(|ib| ib.header().is_some())
        {
            return;
        }
        let ibs_with_same_vrf = self.leios.ibs_by_vrf.entry(header.vrf).or_default();
        ibs_with_same_vrf.push(id);
        if !self.behaviours.ib_equivocation && ibs_with_same_vrf.len() > 2 {
            // This is an equivocation, and we've already broadcasted a proof of equivocation (PoE).
            // Note that if we've seen EXACTLY two ibs with the same VRF, we still validate/propagate the second,
            // because the second header serves as a PoE to our peers.
            return;
        }
        self.leios.ibs.insert(
            id,
            InputBlockState::Pending {
                header: header.clone(),
                header_seen: self.clock.now(),
            },
        );
        self.queued
            .schedule_cpu_task(Task::IBHeaderValidated(from, header, has_body));
    }

    fn finish_validating_ib_header(
        &mut self,
        from: NodeId,
        header: InputBlockHeader,
        has_body: bool,
    ) {
        let id = header.id;
        // We haven't seen this header before, so propagate it to our neighbors
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued
                .send_to(*peer, SimulationMessage::AnnounceIBHeader(id));
        }
        if !self.ib_equivocation_detected(&header) && has_body {
            // Whoever sent us this IB header has also announced that they have the body.
            // If we still need it, download it from them.
            self.receive_announce_ib(from, id);
        }
    }

    fn receive_announce_ib(&mut self, from: NodeId, id: InputBlockId) {
        let (header, header_seen) = match self.leios.ibs.get(&id) {
            Some(InputBlockState::Pending {
                header,
                header_seen,
            }) => (header, *header_seen),
            Some(InputBlockState::Requested {
                header,
                header_seen,
            }) if self.sim_config.relay_strategy == RelayStrategy::RequestFromAll => {
                (header, *header_seen)
            }
            _ => return,
        };
        if self.ib_equivocation_detected(header) {
            // No reason to download the body of an equivocated IB
            return;
        }

        // Do we have capacity to request this block?
        let reqs = self
            .leios
            .ib_requests
            .entry(from)
            .or_insert(PeerInputBlockRequests::new(&self.sim_config));
        if reqs.active.len() < self.sim_config.max_ib_requests_per_peer {
            // If so, make the request
            self.leios.ibs.insert(
                id,
                InputBlockState::Requested {
                    header: header.clone(),
                    header_seen,
                },
            );
            reqs.active.insert(id);
            self.queued.send_to(from, SimulationMessage::RequestIB(id));
        } else {
            // If not, just track that this peer has this IB when we're ready
            reqs.queue(id, header.timestamp);
        }
    }

    fn receive_request_ib(&mut self, from: NodeId, id: InputBlockId) {
        if let Some(InputBlockState::Received { ib, .. }) = self.leios.ibs.get(&id) {
            self.tracker.track_ib_sent(ib, self.id, from);
            self.queued.send_to(from, SimulationMessage::IB(ib.clone()));
        }
    }

    fn receive_ib(&mut self, from: NodeId, ib: Arc<InputBlock>) {
        self.tracker.track_ib_received(ib.header.id, from, self.id);
        // If we've already received this IB, don't waste CPU time validating it
        if self
            .leios
            .ibs
            .get(&ib.header.id)
            .is_some_and(|ib| matches!(ib, InputBlockState::Received { .. }))
        {
            return;
        }
        // If we know that this is an equivocation, don't waste CPU time validating it either
        if self.ib_equivocation_detected(&ib.header) {
            return;
        }
        self.queued
            .schedule_cpu_task(Task::IBBlockValidated(from, ib));
    }

    fn finish_validating_ib(&mut self, from: NodeId, ib: Arc<InputBlock>) {
        let id = ib.header.id;
        let pipeline = ib.header.id.pipeline;
        for transaction in &ib.transactions {
            // Do not include transactions from this IB in any IBs we produce ourselves.
            self.leios.mempool.remove(&transaction.id);
        }
        if self.sim_config.mempool_aggressive_pruning {
            // If we're using aggressive pruning, remove transactions from the mempool if they conflict with transactions in this IB
            self.leios
                .input_ids_in_flight
                .extend(ib.transactions.iter().map(|tx| tx.input_id));
            self.leios
                .mempool
                .retain(|_, tx| !self.leios.input_ids_in_flight.contains(&tx.input_id));
        }
        let header_seen = self
            .leios
            .ibs
            .get(&id)
            .and_then(|state| state.header_seen())
            .unwrap();
        if self
            .leios
            .ibs
            .insert(id, InputBlockState::Received { ib, header_seen })
            .is_some_and(|ib| matches!(ib, InputBlockState::Received { .. }))
        {
            return;
        }
        self.leios
            .ibs_by_pipeline
            .entry(pipeline)
            .or_default()
            .push(id);

        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.queued
                .send_to(*peer, SimulationMessage::AnnounceIB(id));
        }

        // Mark that this IB is no longer pending
        let reqs = self
            .leios
            .ib_requests
            .entry(from)
            .or_insert(PeerInputBlockRequests::new(&self.sim_config));
        reqs.active.remove(&id);

        // We now have capacity to request one more IB from this peer
        while let Some(id) = reqs.next() {
            let (header, header_seen) = match self.leios.ibs.get(&id) {
                Some(InputBlockState::Pending {
                    header,
                    header_seen,
                }) => (header, *header_seen),
                Some(InputBlockState::Requested {
                    header,
                    header_seen,
                }) if self.sim_config.relay_strategy == RelayStrategy::RequestFromAll => {
                    (header, *header_seen)
                }
                _ => {
                    // We fetched this IB from some other node already
                    continue;
                }
            };

            // NB: below logic is identical to ib_equivocation_detected.
            // We can't call that method because `reqs` has a mutable borrow on our state :(
            if !self.behaviours.ib_equivocation
                && self
                    .leios
                    .ibs_by_vrf
                    .get(&header.vrf)
                    .is_some_and(|ids| ids.len() > 1)
            {
                // Don't bother fetching an equivocated IB
                continue;
            }

            // Make the request
            self.leios.ibs.insert(
                id,
                InputBlockState::Requested {
                    header: header.clone(),
                    header_seen,
                },
            );
            reqs.active.insert(id);
            self.queued.send_to(from, SimulationMessage::RequestIB(id));
            break;
        }
    }

    fn ib_equivocation_detected(&self, header: &InputBlockHeader) -> bool {
        if self.behaviours.ib_equivocation {
            // If we WANT to equivocate IBs, we don't bother detecting equivocations either.
            // This way, relays (which can't equivocate themselves) can still "play along"
            // with a stake pool's equivocation attack.
            return false;
        }
        self.leios
            .ibs_by_vrf
            .get(&header.vrf)
            .is_some_and(|ids| ids.len() > 1)
    }

    fn receive_announce_eb(&mut self, from: NodeId, id: EndorserBlockId) {
        if self.leios.ebs.get(&id).is_none_or(|eb| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(eb, EndorserBlockState::Pending)
        }) {
            self.leios.ebs.insert(id, EndorserBlockState::Pending);
            self.queued.send_to(from, SimulationMessage::RequestEB(id));
        }
    }

    fn receive_request_eb(&mut self, from: NodeId, id: EndorserBlockId) {
        if let Some(EndorserBlockState::Received { eb, .. }) = self.leios.ebs.get(&id) {
            self.tracker.track_eb_sent(eb, self.id, from);
            self.queued.send_to(from, SimulationMessage::EB(eb.clone()));
        }
    }

    fn receive_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) {
        self.tracker.track_eb_received(eb.id(), from, self.id);
        self.queued
            .schedule_cpu_task(Task::EBBlockValidated(from, eb));
    }

    fn finish_validating_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) {
        let id = eb.id();
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
            self.queued
                .send_to(*peer, SimulationMessage::AnnounceEB(id));
        }
    }

    fn receive_announce_votes(&mut self, from: NodeId, id: VoteBundleId) {
        if self.leios.votes.get(&id).is_none_or(|v| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(v, VoteBundleState::Requested)
        }) {
            self.leios.votes.insert(id, VoteBundleState::Requested);
            self.queued
                .send_to(from, SimulationMessage::RequestVotes(id));
        }
    }

    fn receive_request_votes(&mut self, from: NodeId, id: VoteBundleId) {
        if let Some(VoteBundleState::Received(votes)) = self.leios.votes.get(&id) {
            self.tracker.track_votes_sent(votes, self.id, from);
            self.queued
                .send_to(from, SimulationMessage::Votes(votes.clone()));
        }
    }

    fn receive_votes(&mut self, from: NodeId, votes: Arc<VoteBundle>) {
        self.tracker.track_votes_received(&votes, from, self.id);
        self.queued
            .schedule_cpu_task(Task::VTBundleValidated(from, votes));
    }

    fn finish_validating_vote_bundle(&mut self, from: NodeId, votes: Arc<VoteBundle>) {
        let id = votes.id;
        if self
            .leios
            .votes
            .insert(id, VoteBundleState::Received(votes.clone()))
            .is_some_and(|v| matches!(v, VoteBundleState::Received(_)))
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
            self.queued
                .send_to(*peer, SimulationMessage::AnnounceVotes(id));
        }
    }

    fn select_txs_for_ib(&mut self, shard: u64, rb_ref: Option<BlockId>) -> Vec<Arc<Transaction>> {
        if let TransactionConfig::Mock(config) = &self.sim_config.transactions {
            let tx = config.mock_tx(config.ib_size);
            self.tracker.track_transaction_generated(&tx, self.id);
            vec![Arc::new(tx)]
        } else {
            let ledger_state = self.resolve_ledger_state(rb_ref);
            self.select_txs(
                shard,
                |tx| !ledger_state.spent_inputs.contains(&tx.input_id),
                self.sim_config.max_ib_size,
            )
        }
    }

    fn select_txs<C>(
        &mut self,
        container_shard: u64,
        condition: C,
        max_size: u64,
    ) -> Vec<Arc<Transaction>>
    where
        C: Fn(&Transaction) -> bool,
    {
        let ib_shards = self.sim_config.ib_shards;
        let tx_may_use_shard = |tx: &Transaction| {
            for shard in tx.shard..=tx.shard + tx.overcollateralization_factor {
                let shard = shard % ib_shards;
                if shard == container_shard {
                    return true;
                }
            }
            false
        };
        let mut candidate_txs: Vec<_> = self
            .leios
            .mempool
            .values()
            .filter_map(|tx| {
                if tx_may_use_shard(tx) && condition(tx) {
                    Some((tx.id, tx.bytes, tx.input_id))
                } else {
                    None
                }
            })
            .collect();
        if matches!(
            self.sim_config.mempool_strategy,
            MempoolSamplingStrategy::Random
        ) {
            candidate_txs.shuffle(&mut self.rng);
        }
        let mut txs = vec![];
        let mut size = 0;
        let mut spent_inputs = HashSet::new();
        for (id, bytes, input_id) in candidate_txs {
            let remaining_capacity = max_size - size;
            if remaining_capacity < bytes {
                continue;
            }
            if !spent_inputs.insert(input_id) {
                continue;
            }
            let tx = self.leios.mempool.remove(&id).unwrap();
            size += tx.bytes;
            txs.push(tx);
        }
        txs
    }

    fn latest_rb_ref(&self) -> Option<BlockId> {
        self.praos.blocks.last_key_value().map(|(k, _)| *k)
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
            let Some(block) = self.praos.blocks.get(&block_id) else {
                continue;
            };
            if let Some(parent) = block.parent {
                block_queue.push(parent);
            }
            for tx in &block.transactions {
                state.spent_inputs.insert(tx.input_id);
            }

            let mut eb_queue = vec![];
            if let Some(endorsement) = &block.endorsement {
                eb_queue.push(endorsement.eb);
            }
            while let Some(eb_id) = eb_queue.pop() {
                if !state.seen_ebs.insert(eb_id) {
                    continue;
                }
                let Some(EndorserBlockState::Received { eb, .. }) = self.leios.ebs.get(&eb_id)
                else {
                    continue;
                };
                for ib_id in &eb.ibs {
                    let Some(InputBlockState::Received { ib, .. }) = self.leios.ibs.get(ib_id)
                    else {
                        continue;
                    };
                    for tx in &ib.transactions {
                        state.spent_inputs.insert(tx.input_id);
                    }
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

    fn finish_generating_ib(&mut self, mut ib: InputBlock) {
        ib.header.timestamp = self.clock.now();
        let ib = Arc::new(ib);

        self.tracker.track_ib_generated(&ib);

        let id = ib.header.id;
        self.leios
            .ibs_by_pipeline
            .entry(ib.header.id.pipeline)
            .or_default()
            .push(id);
        self.leios.ibs.insert(
            id,
            InputBlockState::Received {
                ib,
                header_seen: self.clock.now(),
            },
        );
        for peer in &self.consumers {
            self.queued
                .send_to(*peer, SimulationMessage::AnnounceIBHeader(id));
        }
    }

    fn select_ibs_for_eb(&self, pipeline: u64) -> Vec<InputBlockId> {
        let mut ibs = vec![];
        for p in self.pipelines_for_ib_references(pipeline) {
            let Some(p_ibs) = self.leios.ibs_by_pipeline.get(&p) else {
                continue;
            };
            ibs.extend(p_ibs.iter().cloned());
        }
        ibs
    }

    fn pipelines_for_ib_references(&self, pipeline: u64) -> impl Iterator<Item = u64> + use<'_> {
        let oldest_pipeline = if self.sim_config.late_ib_inclusion {
            pipeline.saturating_sub(3)
        } else {
            pipeline
        };
        oldest_pipeline..=pipeline
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
        if self.sim_config.variant == LeiosVariant::Short {
            // EBs don't reference other EBs unless we're running Full Leios
            return None;
        }

        // The newest pipeline to include EBs from is i-3, where i is the current pipeline.
        let Some(newest_included_pipeline) = pipeline.checked_sub(3) else {
            // If there haven't been 3 pipelines yet, just don't recurse.
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
        self.tracker.track_eb_generated(&eb);

        let id = eb.id();
        self.leios.ebs.insert(
            id,
            EndorserBlockState::Received {
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
            self.queued
                .send_to(*peer, SimulationMessage::AnnounceEB(id));
        }
    }

    fn should_vote_for(&self, eb: &EndorserBlock) -> Result<(), NoVoteReason> {
        let mut ib_set = HashSet::new();
        let expected_ib_pipelines: HashSet<u64> =
            self.pipelines_for_ib_references(eb.pipeline).collect();

        for ib_id in &eb.ibs {
            let Some(InputBlockState::Received { ib, header_seen }) = self.leios.ibs.get(ib_id)
            else {
                return Err(NoVoteReason::MissingIB);
            };
            let equivocation_header_cutoff = Timestamp::from_secs(ib.header.id.slot)
                + self.sim_config.header_diffusion_time * 4
                + self.sim_config.ib_generation_time;
            let equivocated_ib_ids = self.leios.ibs_by_vrf.get(&ib.header.vrf).unwrap();
            if !self.behaviours.ib_equivocation {
                for equivocated_ib_id in equivocated_ib_ids {
                    if equivocated_ib_id == ib_id {
                        continue;
                    }
                    let equivocated_ib = self.leios.ibs.get(equivocated_ib_id).unwrap();
                    if equivocated_ib
                        .header_seen()
                        .is_some_and(|t| t < equivocation_header_cutoff)
                    {
                        return Err(NoVoteReason::EquivocatedIB);
                    }
                }
            }

            let header_cutoff = Timestamp::from_secs(ib.header.id.slot)
                + self.sim_config.header_diffusion_time * 2
                + self.sim_config.ib_generation_time;
            if *header_seen > header_cutoff {
                return Err(NoVoteReason::LateIBHeader);
            }
            if !expected_ib_pipelines.contains(&ib_id.pipeline) {
                return Err(NoVoteReason::InvalidSlot);
            }
            if matches!(self.sim_config.variant, LeiosVariant::FullWithTxReferences) {
                for tx in &ib.transactions {
                    if !matches!(self.txs.get(&tx.id), Some(TransactionView::Received(_))) {
                        return Err(NoVoteReason::MissingTX);
                    }
                }
            }
            ib_set.insert(*ib_id);
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
            .insert(votes.id, VoteBundleState::Received(votes.clone()));
        for peer in &self.consumers {
            self.queued
                .send_to(*peer, SimulationMessage::AnnounceVotes(votes.id));
        }
    }

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
