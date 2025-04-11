use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque},
    hash::Hash,
    sync::Arc,
    time::Duration,
};

use anyhow::{bail, Result};
use netsim_async::HasBytesSize as _;
use priority_queue::PriorityQueue;
use rand::Rng as _;
use rand_chacha::ChaChaRng;
use tokio::{select, sync::mpsc};
use tracing::{info, trace};

use crate::{
    clock::{ClockBarrier, FutureEvent, Timestamp},
    config::{
        DiffusionStrategy, LeiosVariant, NodeConfiguration, NodeId, RelayStrategy,
        SimConfiguration, TransactionConfig,
    },
    events::EventTracker,
    model::{
        Block, BlockId, CpuTaskId, Endorsement, EndorserBlock, EndorserBlockId, InputBlock,
        InputBlockHeader, InputBlockId, NoVoteReason, Transaction, TransactionId, VoteBundle,
        VoteBundleId,
    },
    network::{NetworkSink, NetworkSource},
};

use super::{
    cpu::{CpuTaskQueue, Subtask},
    MiniProtocol, SimulationMessage,
};

enum TransactionView {
    Pending,
    Received(Arc<Transaction>),
}

struct CpuTask {
    task_type: CpuTaskType,
    start_time: Timestamp,
    cpu_time: Duration,
}

enum CpuTaskType {
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
    VTBundleGenerated(VoteBundle),
    /// A bundle of votes has been received and validated, and is ready to propagate
    VTBundleValidated(NodeId, Arc<VoteBundle>),
}

impl CpuTaskType {
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
            Self::VTBundleGenerated(_) => "GenVote",
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
            Self::VTBundleGenerated(_) => "".to_string(),
            Self::VTBundleValidated(_, _) => "".to_string(),
        }
    }
}

/// Things that can happen next for a node
enum NodeEvent {
    /// A new slot has started.
    NewSlot(u64),
    /// A core has finished running some task, and is free to run another.
    CpuSubtaskCompleted(Subtask),
}

pub struct Node {
    id: NodeId,
    name: String,
    trace: bool,
    sim_config: Arc<SimConfiguration>,
    msg_source: Option<NetworkSource<SimulationMessage>>,
    msg_sink: NetworkSink<MiniProtocol, SimulationMessage>,
    tx_source: Option<mpsc::UnboundedReceiver<Arc<Transaction>>>,
    events: BinaryHeap<FutureEvent<NodeEvent>>,
    tracker: EventTracker,
    rng: ChaChaRng,
    clock: ClockBarrier,
    stake: u64,
    total_stake: u64,
    cpu: CpuTaskQueue<CpuTask>,
    consumers: Vec<NodeId>,
    txs: HashMap<TransactionId, TransactionView>,
    praos: NodePraosState,
    leios: NodeLeiosState,
}

#[derive(Default)]
struct NodePraosState {
    mempool: BTreeMap<TransactionId, Arc<Transaction>>,
    peer_heads: BTreeMap<NodeId, u64>,
    blocks_seen: BTreeSet<u64>,
    blocks: BTreeMap<u64, Arc<Block>>,
}

#[derive(Default)]
struct NodeLeiosState {
    mempool: BTreeMap<TransactionId, Arc<Transaction>>,
    ibs_to_generate: BTreeMap<u64, Vec<InputBlockHeader>>,
    ibs: BTreeMap<InputBlockId, InputBlockState>,
    ib_requests: BTreeMap<NodeId, PeerInputBlockRequests>,
    ibs_by_slot: BTreeMap<u64, Vec<InputBlockId>>,
    ebs: BTreeMap<EndorserBlockId, EndorserBlockState>,
    ebs_by_slot: BTreeMap<u64, Vec<EndorserBlockId>>,
    earliest_eb_cert_times_by_slot: BTreeMap<u64, Timestamp>,
    votes_to_generate: BTreeMap<u64, usize>,
    votes_by_eb: BTreeMap<EndorserBlockId, BTreeMap<NodeId, usize>>,
    votes: BTreeMap<VoteBundleId, VoteBundleState>,
}

enum InputBlockState {
    HeaderPending,
    Pending(InputBlockHeader),
    Requested(InputBlockHeader),
    Received(Arc<InputBlock>),
}
impl InputBlockState {
    fn header(&self) -> Option<&InputBlockHeader> {
        match self {
            Self::HeaderPending => None,
            Self::Pending(header) => Some(header),
            Self::Requested(header) => Some(header),
            Self::Received(ib) => Some(&ib.header),
        }
    }
}

enum EndorserBlockState {
    Pending,
    Received(Arc<EndorserBlock>),
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

impl Node {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        total_stake: u64,
        msg_source: NetworkSource<SimulationMessage>,
        msg_sink: NetworkSink<MiniProtocol, SimulationMessage>,
        tx_source: mpsc::UnboundedReceiver<Arc<Transaction>>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: ClockBarrier,
    ) -> Self {
        let id = config.id;
        let stake = config.stake;
        let cpu = CpuTaskQueue::new(config.cores, config.cpu_multiplier);
        let consumers = config.consumers.clone();
        let mut events = BinaryHeap::new();
        events.push(FutureEvent(clock.now(), NodeEvent::NewSlot(0)));

        Self {
            id,
            name: config.name.clone(),
            trace: sim_config.trace_nodes.contains(&id),
            sim_config,
            msg_source: Some(msg_source),
            msg_sink,
            tx_source: Some(tx_source),
            events,
            tracker,
            rng,
            clock,
            stake,
            total_stake,
            cpu,
            consumers,
            txs: HashMap::new(),
            praos: NodePraosState::default(),
            leios: NodeLeiosState::default(),
        }
    }

    async fn next_event(&mut self) -> NodeEvent {
        self.clock
            .wait_until(self.events.peek().map(|e| e.0).expect("no events"))
            .await;
        self.events.pop().unwrap().1
    }

    fn schedule_cpu_task(&mut self, task_type: CpuTaskType) {
        let cpu_times = self.task_cpu_times(&task_type);
        let task = CpuTask {
            task_type,
            start_time: self.clock.now(),
            cpu_time: cpu_times.iter().sum(),
        };
        let task_type = task.task_type.name();
        let subtask_count = cpu_times.len();
        let (task_id, subtasks) = self.cpu.schedule_task(task, cpu_times);
        self.tracker.track_cpu_task_scheduled(
            CpuTaskId {
                node: self.id,
                index: task_id,
            },
            task_type.clone(),
            subtask_count,
        );
        for subtask in subtasks {
            self.start_cpu_subtask(subtask, task_type.clone());
        }
    }

    fn start_cpu_subtask(&mut self, subtask: Subtask, task_type: String) {
        let task_id = CpuTaskId {
            node: self.id,
            index: subtask.task_id,
        };
        self.tracker.track_cpu_subtask_started(
            task_id,
            task_type,
            subtask.subtask_id,
            subtask.duration,
        );
        let timestamp = self.clock.now() + subtask.duration;
        self.events.push(FutureEvent(
            timestamp,
            NodeEvent::CpuSubtaskCompleted(subtask),
        ))
    }

    fn task_cpu_times(&self, task: &CpuTaskType) -> Vec<Duration> {
        let cpu_times = &self.sim_config.cpu_times;
        match task {
            CpuTaskType::TransactionValidated(_, _) => vec![cpu_times.tx_validation],
            CpuTaskType::RBBlockGenerated(block) => {
                let mut time = cpu_times.rb_generation;
                if let Some(endorsement) = &block.endorsement {
                    let nodes = endorsement.votes.len();
                    time += cpu_times.cert_generation_constant
                        + (cpu_times.cert_generation_per_node * nodes as u32)
                }
                vec![time]
            }
            CpuTaskType::RBBlockValidated(_, rb) => {
                let mut time = cpu_times.rb_validation_constant;
                let bytes: u64 = rb.transactions.iter().map(|tx| tx.bytes).sum();
                time += cpu_times.rb_validation_per_byte * (bytes as u32);
                if let Some(endorsement) = &rb.endorsement {
                    let nodes = endorsement.votes.len();
                    time += cpu_times.cert_validation_constant
                        + (cpu_times.cert_validation_per_node * nodes as u32)
                }
                vec![time]
            }
            CpuTaskType::IBBlockGenerated(_) => vec![cpu_times.ib_generation],
            CpuTaskType::IBHeaderValidated(_, _, _) => vec![cpu_times.ib_head_validation],
            CpuTaskType::IBBlockValidated(_, ib) => vec![
                cpu_times.ib_body_validation_constant
                    + (cpu_times.ib_body_validation_per_byte * ib.bytes() as u32),
            ],
            CpuTaskType::EBBlockGenerated(_) => vec![cpu_times.eb_generation],
            CpuTaskType::EBBlockValidated(_, _) => vec![cpu_times.eb_validation],
            CpuTaskType::VTBundleGenerated(votes) => votes
                .ebs
                .keys()
                .map(|eb_id| {
                    let Some(EndorserBlockState::Received(eb)) = self.leios.ebs.get(eb_id) else {
                        panic!("node tried voting for an unknown EB");
                    };
                    cpu_times.vote_generation_constant
                        + (cpu_times.vote_generation_per_ib * eb.ibs.len() as u32)
                })
                .collect(),
            CpuTaskType::VTBundleValidated(_, votes) => {
                std::iter::repeat(cpu_times.vote_validation)
                    .take(votes.ebs.len())
                    .collect()
            }
        }
    }

    pub async fn run(mut self) -> Result<()> {
        // TODO: split struct Node into the mechanics (which can then be extracted here) and the high-level logic that handles messages
        // (then we could remove these Option shenanigans)
        let mut msg_source = self.msg_source.take().unwrap();
        let mut tx_source = self.tx_source.take().unwrap();

        loop {
            select! {
                maybe_msg = msg_source.recv() => {
                    let Some((from, msg)) = maybe_msg else {
                        // sim has stopped running
                        break;
                    };
                    self.handle_message(from, msg)?;
                    self.clock.finish_task();
                }
                maybe_tx = tx_source.recv() => {
                    let Some(tx) = maybe_tx else {
                        // sim has stopped runinng
                        break;
                    };
                    self.generate_tx(tx)?;
                }
                event = self.next_event() => {
                    match event {
                        NodeEvent::NewSlot(slot) => self.handle_new_slot(slot)?,
                        NodeEvent::CpuSubtaskCompleted(subtask) => {
                            let task_id = CpuTaskId { node: self.id, index: subtask.task_id };
                            let (finished_task, next_subtask) = self.cpu.complete_subtask(subtask);
                            if let Some((subtask, task)) = next_subtask {
                                let task_type = task.task_type.name();
                                self.start_cpu_subtask(subtask, task_type);
                            }
                            let Some(task) = finished_task else {
                                continue;
                            };
                            let wall_time = self.clock.now() - task.start_time;
                            self.tracker.track_cpu_task_finished(task_id, task.task_type.name(), task.cpu_time, wall_time, task.task_type.extra());
                            match task.task_type {
                                CpuTaskType::TransactionValidated(from, tx) => self.propagate_tx(from, tx)?,
                                CpuTaskType::RBBlockGenerated(block) => self.finish_generating_block(block)?,
                                CpuTaskType::RBBlockValidated(from, block) => self.finish_validating_block(from, block)?,
                                CpuTaskType::IBBlockGenerated(ib) => self.finish_generating_ib(ib)?,
                                CpuTaskType::IBHeaderValidated(from, ib, has_body) => self.finish_validating_ib_header(from, ib, has_body)?,
                                CpuTaskType::IBBlockValidated(from, ib) => self.finish_validating_ib(from, ib)?,
                                CpuTaskType::EBBlockGenerated(eb) => self.finish_generating_eb(eb)?,
                                CpuTaskType::EBBlockValidated(from, eb) => self.finish_validating_eb(from, eb)?,
                                CpuTaskType::VTBundleGenerated(votes) => self.finish_generating_vote_bundle(votes)?,
                                CpuTaskType::VTBundleValidated(from, votes) => self.finish_validating_vote_bundle(from, votes)?,
                            }
                        }
                    }
                }
            };
        }
        Ok(())
    }

    fn handle_message(&mut self, from: NodeId, msg: SimulationMessage) -> Result<()> {
        match msg {
            // TX propagation
            SimulationMessage::AnnounceTx(id) => {
                self.receive_announce_tx(from, id)?;
            }
            SimulationMessage::RequestTx(id) => {
                self.receive_request_tx(from, id)?;
            }
            SimulationMessage::Tx(tx) => {
                self.receive_tx(from, tx);
            }

            // Block propagation
            SimulationMessage::RollForward(slot) => {
                self.receive_roll_forward(from, slot)?;
            }
            SimulationMessage::RequestBlock(slot) => {
                self.receive_request_block(from, slot)?;
            }
            SimulationMessage::Block(block) => {
                self.receive_block(from, block);
            }

            // IB header propagation
            SimulationMessage::AnnounceIBHeader(id) => {
                self.receive_announce_ib_header(from, id)?;
            }
            SimulationMessage::RequestIBHeader(id) => {
                self.receive_request_ib_header(from, id)?;
            }
            SimulationMessage::IBHeader(header, has_body) => {
                self.receive_ib_header(from, header, has_body);
            }

            // IB transmission
            SimulationMessage::AnnounceIB(id) => {
                self.receive_announce_ib(from, id)?;
            }
            SimulationMessage::RequestIB(id) => {
                self.receive_request_ib(from, id)?;
            }
            SimulationMessage::IB(ib) => {
                self.receive_ib(from, ib);
            }

            // EB propagation
            SimulationMessage::AnnounceEB(id) => {
                self.receive_announce_eb(from, id)?;
            }
            SimulationMessage::RequestEB(id) => {
                self.receive_request_eb(from, id)?;
            }
            SimulationMessage::EB(eb) => {
                self.receive_eb(from, eb);
            }

            // Voting
            SimulationMessage::AnnounceVotes(id) => {
                self.receive_announce_votes(from, id)?;
            }
            SimulationMessage::RequestVotes(id) => {
                self.receive_request_votes(from, id)?;
            }
            SimulationMessage::Votes(votes) => {
                self.receive_votes(from, votes);
            }
        }
        Ok(())
    }

    fn handle_new_slot(&mut self, slot: u64) -> Result<()> {
        // The beginning of a new slot is the end of an old slot.
        // Publish any input blocks left over from the last slot

        if slot % self.sim_config.stage_length == 0 {
            // A new stage has begun.

            // Decide how many votes to generate in each slot
            self.schedule_endorser_block_votes(slot);

            // Generate any EBs we're allowed to in this slot.
            self.generate_endorser_blocks(slot);

            // Decide how many IBs to generate in each slot.
            self.schedule_input_block_generation(slot);
        }

        // Vote for any EBs which satisfy all requirements.
        self.vote_for_endorser_blocks(slot);

        // Generate any IBs scheduled for this slot.
        self.generate_input_blocks(slot);

        self.try_generate_praos_block(slot)?;

        self.events.push(FutureEvent(
            self.clock.now() + Duration::from_secs(1),
            NodeEvent::NewSlot(slot + 1),
        ));

        Ok(())
    }

    fn schedule_input_block_generation(&mut self, slot: u64) {
        let mut slot_vrfs: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
        // IBs are generated at the start of any slot within this stage
        for stage_slot in slot..slot + self.sim_config.stage_length {
            let vrfs: Vec<u64> = vrf_probabilities(self.sim_config.ib_generation_probability)
                .filter_map(|p| self.run_vrf(p))
                .collect();
            if !vrfs.is_empty() {
                slot_vrfs.insert(stage_slot, vrfs);
            }
        }
        for (slot, vrfs) in slot_vrfs {
            let headers = vrfs
                .into_iter()
                .enumerate()
                .map(|(index, vrf)| InputBlockHeader {
                    id: InputBlockId {
                        slot,
                        pipeline: self.slot_to_pipeline(slot),
                        producer: self.id,
                        index: index as u64,
                    },
                    vrf,
                    timestamp: self.clock.now(),
                    bytes: self.sim_config.sizes.ib_header,
                })
                .collect();
            self.leios.ibs_to_generate.insert(slot, headers);
        }
    }

    fn generate_endorser_blocks(&mut self, slot: u64) {
        for next_p in vrf_probabilities(self.sim_config.eb_generation_probability) {
            if self.run_vrf(next_p).is_some() {
                self.tracker.track_eb_lottery_won(EndorserBlockId {
                    slot,
                    pipeline: self.slot_to_pipeline(slot),
                    producer: self.id,
                });
                let ibs = self.select_ibs_for_eb(slot);
                let ebs = self.select_ebs_for_eb(slot);
                let bytes = self.sim_config.sizes.eb(ibs.len(), ebs.len());
                let eb = EndorserBlock {
                    slot,
                    pipeline: self.slot_to_pipeline(slot),
                    producer: self.id,
                    bytes,
                    ibs,
                    ebs,
                };
                self.schedule_cpu_task(CpuTaskType::EBBlockGenerated(eb));
                // A node should only generate at most 1 EB per slot
                return;
            }
        }
    }

    fn schedule_endorser_block_votes(&mut self, slot: u64) {
        let vrf_wins = vrf_probabilities(self.sim_config.vote_probability)
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
        let Some(vote_count) = self.leios.votes_to_generate.remove(&slot) else {
            return;
        };
        // When we vote, we vote for EBs which were sent at the start of the prior stage.
        let eb_slot = match slot.checked_sub(self.sim_config.stage_length) {
            Some(s) => s - (s % self.sim_config.stage_length),
            None => {
                return;
            }
        };
        let Some(ebs) = self.leios.ebs_by_slot.get(&eb_slot) else {
            return;
        };
        let mut ebs = ebs.clone();
        ebs.retain(|eb_id| {
            let Some(EndorserBlockState::Received(eb)) = self.leios.ebs.get(eb_id) else {
                panic!("Tried voting for EB which we haven't received");
            };
            match self.should_vote_for(slot, eb) {
                Ok(()) => true,
                Err(reason) => {
                    self.tracker.track_no_vote(
                        slot,
                        self.slot_to_pipeline(slot),
                        self.id,
                        *eb_id,
                        reason,
                    );
                    false
                }
            }
        });
        if ebs.is_empty() {
            return;
        }
        // For every VRF lottery you won, you can vote for every EB
        let votes_allowed = vote_count * ebs.len();
        let votes = VoteBundle {
            id: VoteBundleId {
                slot,
                pipeline: self.slot_to_pipeline(slot),
                producer: self.id,
            },
            bytes: self.sim_config.sizes.vote_bundle(ebs.len()),
            ebs: ebs.into_iter().map(|eb| (eb, votes_allowed)).collect(),
        };
        if !votes.ebs.is_empty() {
            self.schedule_cpu_task(CpuTaskType::VTBundleGenerated(votes));
        }
    }

    fn generate_input_blocks(&mut self, slot: u64) {
        let Some(headers) = self.leios.ibs_to_generate.remove(&slot) else {
            return;
        };
        for header in headers {
            self.tracker.track_ib_lottery_won(header.id);
            let mut ib = InputBlock {
                header,
                transactions: vec![],
            };
            self.try_filling_ib(&mut ib);
            self.schedule_cpu_task(CpuTaskType::IBBlockGenerated(ib));
        }
    }

    fn try_generate_praos_block(&mut self, slot: u64) -> Result<()> {
        // L1 block generation
        let Some(vrf) = self.run_vrf(self.sim_config.block_generation_probability) else {
            return Ok(());
        };

        // Let's see if we are minting an RB
        let endorsement = self.choose_endorsed_block_for_rb(slot);
        if let Some(endorsement) = &endorsement {
            // If we are, get all referenced TXs out of the mempool
            let Some(eb) = self.leios.ebs.get(&endorsement.eb) else {
                bail!("Missing endorsement block {}", endorsement.eb);
            };
            let EndorserBlockState::Received(eb) = eb else {
                bail!("Haven't yet received endorsement block {}", endorsement.eb);
            };
            for ib_id in &eb.ibs {
                let Some(InputBlockState::Received(ib)) = self.leios.ibs.get(ib_id) else {
                    bail!("Missing input block {}", ib_id);
                };
                for tx in &ib.transactions {
                    self.praos.mempool.remove(&tx.id);
                }
            }
        }

        let mut transactions = vec![];
        if let TransactionConfig::Mock(config) = &self.sim_config.transactions {
            // Add one transaction, the right size for the extra RB payload
            let tx = Transaction {
                id: config.next_id(),
                shard: 0,
                bytes: config.rb_size,
            };
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
            }
        }

        let parent = self
            .praos
            .blocks
            .last_key_value()
            .map(|(_, block)| block.id);

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
        self.tracker.track_praos_block_lottery_won(&block);
        self.schedule_cpu_task(CpuTaskType::RBBlockGenerated(block));

        Ok(())
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
            LeiosVariant::Full => candidates
                .max_by_key(|(eb, age, votes)| (Reverse(*age), self.count_txs_in_eb(eb), *votes))?,
        };

        let votes = self.leios.votes_by_eb.get(&block)?.clone();
        let size_bytes = self.sim_config.sizes.cert(votes.len());

        Some(Endorsement {
            eb: block,
            size_bytes,
            votes,
        })
    }

    fn choose_endorsed_block_from_slot(&self, slot: u64) -> Option<EndorserBlockId> {
        // an EB is eligible for endorsement if it has this many votes
        let vote_threshold = self.sim_config.vote_threshold;

        // Choose an EB based on, in order,
        //  - the TXs in the EB (more TXs take priority)
        //  - the number of votes (more votes is better)
        let (&block, _) = self
            .leios
            .ebs_by_slot
            .get(&slot)
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

    fn all_ibs_seen(&self, eb: &EndorserBlockId) -> bool {
        let Some(EndorserBlockState::Received(eb_body)) = self.leios.ebs.get(eb) else {
            return false;
        };
        eb_body
            .ibs
            .iter()
            .all(|ib| matches!(self.leios.ibs.get(ib), Some(InputBlockState::Received(_))))
    }

    fn count_txs_in_eb(&self, eb_id: &EndorserBlockId) -> Option<usize> {
        let Some(EndorserBlockState::Received(eb)) = self.leios.ebs.get(eb_id) else {
            return None;
        };
        let mut tx_set = HashSet::new();
        for ib_id in &eb.ibs {
            let InputBlockState::Received(ib) = self.leios.ibs.get(ib_id)? else {
                return None;
            };
            for tx in &ib.transactions {
                tx_set.insert(tx.id);
            }
        }
        Some(tx_set.len())
    }

    fn finish_generating_block(&mut self, block: Block) -> Result<()> {
        self.tracker.track_praos_block_generated(&block);

        self.publish_block(Arc::new(block))
    }

    fn publish_block(&mut self, block: Arc<Block>) -> Result<()> {
        // Remove TXs in these blocks from the leios mempool.
        for tx in &block.transactions {
            self.leios.mempool.remove(&tx.id);
        }
        for peer in &self.consumers {
            if self
                .praos
                .peer_heads
                .get(peer)
                .is_none_or(|&s| s < block.id.slot)
            {
                self.send_to(*peer, SimulationMessage::RollForward(block.id.slot))?;
                self.praos.peer_heads.insert(*peer, block.id.slot);
            }
        }
        self.praos.blocks.insert(block.id.slot, block);
        Ok(())
    }

    fn receive_announce_tx(&mut self, from: NodeId, id: TransactionId) -> Result<()> {
        if self.txs.get(&id).is_none_or(|t| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(t, TransactionView::Pending)
        }) {
            self.txs.insert(id, TransactionView::Pending);
            self.send_to(from, SimulationMessage::RequestTx(id))?;
        }
        Ok(())
    }

    fn receive_request_tx(&mut self, from: NodeId, id: TransactionId) -> Result<()> {
        if let Some(TransactionView::Received(tx)) = self.txs.get(&id) {
            self.tracker.track_transaction_sent(tx.id, self.id, from);
            self.send_to(from, SimulationMessage::Tx(tx.clone()))?;
        }
        Ok(())
    }

    fn receive_tx(&mut self, from: NodeId, tx: Arc<Transaction>) {
        self.tracker
            .track_transaction_received(tx.id, from, self.id);
        self.schedule_cpu_task(CpuTaskType::TransactionValidated(from, tx));
    }

    fn generate_tx(&mut self, tx: Arc<Transaction>) -> Result<()> {
        self.tracker.track_transaction_generated(&tx, self.id);
        self.propagate_tx(self.id, tx)
    }

    fn propagate_tx(&mut self, from: NodeId, tx: Arc<Transaction>) -> Result<()> {
        let id = tx.id;
        if self
            .txs
            .insert(id, TransactionView::Received(tx.clone()))
            .is_some_and(|tx| matches!(tx, TransactionView::Received(_)))
        {
            return Ok(());
        }
        if self.trace {
            info!("node {} saw tx {id}", self.name);
        }
        self.praos.mempool.insert(tx.id, tx.clone());
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceTx(id))?;
        }
        self.leios.mempool.insert(tx.id, tx);
        Ok(())
    }

    fn receive_roll_forward(&mut self, from: NodeId, slot: u64) -> Result<()> {
        if self.praos.blocks_seen.insert(slot) {
            self.send_to(from, SimulationMessage::RequestBlock(slot))?;
        }
        Ok(())
    }

    fn receive_request_block(&mut self, from: NodeId, slot: u64) -> Result<()> {
        if let Some(block) = self.praos.blocks.get(&slot) {
            self.tracker.track_praos_block_sent(block, self.id, from);
            self.send_to(from, SimulationMessage::Block(block.clone()))?;
        }
        Ok(())
    }

    fn receive_block(&mut self, from: NodeId, block: Arc<Block>) {
        self.tracker
            .track_praos_block_received(&block, from, self.id);
        self.schedule_cpu_task(CpuTaskType::RBBlockValidated(from, block));
    }

    fn finish_validating_block(&mut self, from: NodeId, block: Arc<Block>) -> Result<()> {
        if let Some(old_block) = self.praos.blocks.get(&block.id.slot) {
            // SLOT BATTLE!!! lower VRF wins
            if old_block.vrf <= block.vrf {
                // We like our block better than this new one.
                return Ok(());
            }
        }
        self.praos.blocks.insert(block.id.slot, block.clone());

        let head = self.praos.peer_heads.entry(from).or_default();
        if *head < block.id.slot {
            *head = block.id.slot
        }
        self.publish_block(block)?;
        Ok(())
    }

    fn receive_announce_ib_header(&mut self, from: NodeId, id: InputBlockId) -> Result<()> {
        if self.leios.ibs.get(&id).is_none_or(|ib| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(ib, InputBlockState::HeaderPending)
        }) {
            self.leios.ibs.insert(id, InputBlockState::HeaderPending);
            self.send_to(from, SimulationMessage::RequestIBHeader(id))?;
        }
        Ok(())
    }

    fn receive_request_ib_header(&mut self, from: NodeId, id: InputBlockId) -> Result<()> {
        if let Some(ib) = self.leios.ibs.get(&id) {
            if let Some(header) = ib.header() {
                let have_body = matches!(ib, InputBlockState::Received(_));
                self.send_to(from, SimulationMessage::IBHeader(header.clone(), have_body))?;
            }
        }
        Ok(())
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
        self.leios
            .ibs
            .insert(id, InputBlockState::Pending(header.clone()));
        self.schedule_cpu_task(CpuTaskType::IBHeaderValidated(from, header, has_body));
    }

    fn finish_validating_ib_header(
        &mut self,
        from: NodeId,
        header: InputBlockHeader,
        has_body: bool,
    ) -> Result<()> {
        let id = header.id;
        // We haven't seen this header before, so propagate it to our neighbors
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceIBHeader(id))?;
        }
        if has_body {
            // Whoever sent us this IB header has also announced that they have the body.
            // If we still need it, download it from them.
            self.receive_announce_ib(from, id)?;
        }
        Ok(())
    }

    fn receive_announce_ib(&mut self, from: NodeId, id: InputBlockId) -> Result<()> {
        let header = match self.leios.ibs.get(&id) {
            Some(InputBlockState::Pending(header)) => header,
            Some(InputBlockState::Requested(header))
                if self.sim_config.relay_strategy == RelayStrategy::RequestFromAll =>
            {
                header
            }
            _ => return Ok(()),
        };
        // Do we have capacity to request this block?
        let reqs = self
            .leios
            .ib_requests
            .entry(from)
            .or_insert(PeerInputBlockRequests::new(&self.sim_config));
        if reqs.active.len() < self.sim_config.max_ib_requests_per_peer {
            // If so, make the request
            self.leios
                .ibs
                .insert(id, InputBlockState::Requested(header.clone()));
            reqs.active.insert(id);
            self.send_to(from, SimulationMessage::RequestIB(id))?;
        } else {
            // If not, just track that this peer has this IB when we're ready
            reqs.queue(id, header.timestamp);
        }
        Ok(())
    }

    fn receive_request_ib(&mut self, from: NodeId, id: InputBlockId) -> Result<()> {
        if let Some(InputBlockState::Received(ib)) = self.leios.ibs.get(&id) {
            self.tracker.track_ib_sent(id, self.id, from);
            self.send_to(from, SimulationMessage::IB(ib.clone()))?;
        }
        Ok(())
    }

    fn receive_ib(&mut self, from: NodeId, ib: Arc<InputBlock>) {
        self.tracker.track_ib_received(ib.header.id, from, self.id);
        self.schedule_cpu_task(CpuTaskType::IBBlockValidated(from, ib));
    }

    fn finish_validating_ib(&mut self, from: NodeId, ib: Arc<InputBlock>) -> Result<()> {
        let id = ib.header.id;
        let slot = ib.header.id.slot;
        for transaction in &ib.transactions {
            // Do not include transactions from this IB in any IBs we produce ourselves.
            self.leios.mempool.remove(&transaction.id);
        }
        if self
            .leios
            .ibs
            .insert(id, InputBlockState::Received(ib))
            .is_some_and(|ib| matches!(ib, InputBlockState::Received(_)))
        {
            return Ok(());
        }
        self.leios.ibs_by_slot.entry(slot).or_default().push(id);

        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceIB(id))?;
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
            let header = match self.leios.ibs.get(&id) {
                Some(InputBlockState::Pending(header)) => header,
                Some(InputBlockState::Requested(header))
                    if self.sim_config.relay_strategy == RelayStrategy::RequestFromAll =>
                {
                    header
                }
                _ => {
                    // We fetched this IB from some other node already
                    continue;
                }
            };

            // Make the request
            self.leios
                .ibs
                .insert(id, InputBlockState::Requested(header.clone()));
            reqs.active.insert(id);
            self.send_to(from, SimulationMessage::RequestIB(id))?;
            break;
        }

        Ok(())
    }

    fn receive_announce_eb(&mut self, from: NodeId, id: EndorserBlockId) -> Result<()> {
        if self.leios.ebs.get(&id).is_none_or(|eb| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(eb, EndorserBlockState::Pending)
        }) {
            self.leios.ebs.insert(id, EndorserBlockState::Pending);
            self.send_to(from, SimulationMessage::RequestEB(id))?;
        }
        Ok(())
    }

    fn receive_request_eb(&mut self, from: NodeId, id: EndorserBlockId) -> Result<()> {
        if let Some(EndorserBlockState::Received(eb)) = self.leios.ebs.get(&id) {
            self.tracker.track_eb_sent(id, self.id, from);
            self.send_to(from, SimulationMessage::EB(eb.clone()))?;
        }
        Ok(())
    }

    fn receive_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) {
        self.tracker.track_eb_received(eb.id(), from, self.id);
        self.schedule_cpu_task(CpuTaskType::EBBlockValidated(from, eb));
    }

    fn finish_validating_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) -> Result<()> {
        let id = eb.id();
        if self
            .leios
            .ebs
            .insert(id, EndorserBlockState::Received(eb))
            .is_some_and(|eb| matches!(eb, EndorserBlockState::Received(_)))
        {
            return Ok(());
        }
        self.leios.ebs_by_slot.entry(id.slot).or_default().push(id);
        // We haven't seen this EB before, so propagate it to our neighbors
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceEB(id))?;
        }
        Ok(())
    }

    fn receive_announce_votes(&mut self, from: NodeId, id: VoteBundleId) -> Result<()> {
        if self.leios.votes.get(&id).is_none_or(|v| {
            self.sim_config.relay_strategy == RelayStrategy::RequestFromAll
                && matches!(v, VoteBundleState::Requested)
        }) {
            self.leios.votes.insert(id, VoteBundleState::Requested);
            self.send_to(from, SimulationMessage::RequestVotes(id))?;
        }
        Ok(())
    }

    fn receive_request_votes(&mut self, from: NodeId, id: VoteBundleId) -> Result<()> {
        if let Some(VoteBundleState::Received(votes)) = self.leios.votes.get(&id) {
            self.tracker.track_votes_sent(votes, self.id, from);
            self.send_to(from, SimulationMessage::Votes(votes.clone()))?;
        }
        Ok(())
    }

    fn receive_votes(&mut self, from: NodeId, votes: Arc<VoteBundle>) {
        self.tracker.track_votes_received(&votes, from, self.id);
        self.schedule_cpu_task(CpuTaskType::VTBundleValidated(from, votes));
    }

    fn finish_validating_vote_bundle(
        &mut self,
        from: NodeId,
        votes: Arc<VoteBundle>,
    ) -> Result<()> {
        let id = votes.id;
        if self
            .leios
            .votes
            .insert(id, VoteBundleState::Received(votes.clone()))
            .is_some_and(|v| matches!(v, VoteBundleState::Received(_)))
        {
            return Ok(());
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
            if *eb_votes as u64 > self.sim_config.vote_threshold {
                self.leios
                    .earliest_eb_cert_times_by_slot
                    .entry(eb.slot)
                    .or_insert(self.clock.now());
            }
        }
        // We haven't seen these votes before, so propagate them to our neighbors
        for peer in &self.consumers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceVotes(id))?;
        }
        Ok(())
    }

    fn try_filling_ib(&mut self, ib: &mut InputBlock) {
        if let TransactionConfig::Mock(config) = &self.sim_config.transactions {
            let tx = Transaction {
                id: config.next_id(),
                shard: 0,
                bytes: config.ib_size,
            };
            self.tracker.track_transaction_generated(&tx, self.id);
            ib.transactions.push(Arc::new(tx));
            return;
        }

        let shard = ib.header.vrf % self.sim_config.ib_shards;
        let candidate_txs: Vec<_> = self
            .leios
            .mempool
            .values()
            .filter_map(|tx| {
                if tx.shard == shard {
                    Some((tx.id, tx.bytes))
                } else {
                    None
                }
            })
            .collect();
        for (id, bytes) in candidate_txs {
            let remaining_capacity = self.sim_config.max_ib_size - ib.bytes();
            if remaining_capacity < bytes {
                continue;
            }
            ib.transactions
                .push(self.leios.mempool.remove(&id).unwrap());
        }
    }

    fn finish_generating_ib(&mut self, mut ib: InputBlock) -> Result<()> {
        ib.header.timestamp = self.clock.now();
        let ib = Arc::new(ib);

        self.tracker.track_ib_generated(&ib);

        let id = ib.header.id;
        self.leios
            .ibs_by_slot
            .entry(ib.header.id.slot)
            .or_default()
            .push(id);
        self.leios.ibs.insert(id, InputBlockState::Received(ib));
        for peer in &self.consumers {
            self.send_to(*peer, SimulationMessage::AnnounceIBHeader(id))?;
        }
        Ok(())
    }

    fn select_ibs_for_eb(&mut self, slot: u64) -> Vec<InputBlockId> {
        let config = &self.sim_config;
        let Some(earliest_slot) = slot.checked_sub(config.stage_length * 3) else {
            return vec![];
        };
        let mut ibs = vec![];
        for slot in earliest_slot..(earliest_slot + config.stage_length) {
            let Some(slot_ibs) = self.leios.ibs_by_slot.remove(&slot) else {
                continue;
            };
            ibs.extend(slot_ibs);
        }
        ibs
    }

    fn select_ebs_for_eb(&self, slot: u64) -> Vec<EndorserBlockId> {
        let Some(referenced_slots) = self.slots_referenced_by_ebs(slot) else {
            return vec![];
        };

        // include one certified EB from each of these pipelines
        let mut ebs = vec![];
        for pipeline_slot in referenced_slots {
            if let Some(eb) = self.choose_endorsed_block_from_slot(pipeline_slot) {
                ebs.push(eb);
            }
        }
        ebs
    }

    fn slots_referenced_by_ebs(&self, slot: u64) -> Option<impl Iterator<Item = u64> + use<'_>> {
        if self.sim_config.variant != LeiosVariant::Full {
            // EBs don't reference other EBs unless we're running Full Leios
            return None;
        }

        let current_pipeline = slot / self.sim_config.stage_length;
        // The newest pipeline to include EBs from is i-3, where i is the current pipeline.
        let Some(newest_included_pipeline) = current_pipeline.checked_sub(3) else {
            // If there haven't been 3 pipelines yet, just don't recurse.
            return None;
        };

        // the oldest pipeline is i-⌈3η/L⌉, where i is the current pipeline,
        // η is the "quality parameter" (expected block rate), and L is stage length.
        let old_pipelines =
            (3 * self.sim_config.praos_chain_quality).div_ceil(self.sim_config.stage_length);
        let oldest_included_pipeline = current_pipeline
            .checked_sub(old_pipelines)
            .unwrap_or(newest_included_pipeline);

        Some(
            (oldest_included_pipeline..=newest_included_pipeline)
                .map(|i| i * self.sim_config.stage_length),
        )
    }

    fn finish_generating_eb(&mut self, eb: EndorserBlock) -> Result<()> {
        let eb = Arc::new(eb);
        self.tracker.track_eb_generated(&eb);

        let id = eb.id();
        self.leios
            .ebs
            .insert(id, EndorserBlockState::Received(eb.clone()));
        self.leios.ebs_by_slot.entry(id.slot).or_default().push(id);
        for peer in &self.consumers {
            self.send_to(*peer, SimulationMessage::AnnounceEB(id))?;
        }
        Ok(())
    }

    fn should_vote_for(&self, slot: u64, eb: &EndorserBlock) -> Result<(), NoVoteReason> {
        let stage_length = self.sim_config.stage_length;

        let Some(ib_slot_start) = slot.checked_sub(stage_length * 4) else {
            // The IBs for this EB were "generated" before the sim began.
            // It's valid iff there are no IBs.
            return if eb.ibs.is_empty() {
                Ok(())
            } else {
                Err(NoVoteReason::ExtraIB)
            };
        };
        let ib_slot_end = ib_slot_start + stage_length;
        let ib_slot_range = ib_slot_start..ib_slot_end;

        let mut ib_set = HashSet::new();
        for ib in &eb.ibs {
            if !matches!(self.leios.ibs.get(ib), Some(InputBlockState::Received(_))) {
                return Err(NoVoteReason::MissingIB);
            }
            if !ib_slot_range.contains(&ib.slot) {
                return Err(NoVoteReason::InvalidSlot);
            }
            ib_set.insert(*ib);
        }
        for ib_slot in ib_slot_range {
            for ib in self
                .leios
                .ibs_by_slot
                .get(&ib_slot)
                .iter()
                .flat_map(|f| f.iter())
            {
                if !ib_set.contains(ib) {
                    return Err(NoVoteReason::ExtraIB);
                }
            }
        }

        // If this EB is meant to reference other EBs, validate that it references whatever it needs
        if let Some(expected_referenced_slots) = self.slots_referenced_by_ebs(eb.slot) {
            let actual_referenced_slots: HashSet<u64> = eb.ebs.iter().map(|id| id.slot).collect();
            for expected_slot in expected_referenced_slots {
                let Some(certified_at) = self
                    .leios
                    .earliest_eb_cert_times_by_slot
                    .get(&expected_slot)
                else {
                    // We don't require an EB referenced from this pipeline if none of that pipeline's EBs have been certified yet,
                    continue;
                };

                let last_pipeline_slot = expected_slot + self.sim_config.stage_length - 1;
                let cutoff = Timestamp::from_secs(last_pipeline_slot)
                    .checked_sub_duration(self.sim_config.header_diffusion_time)
                    .unwrap_or_default();
                if certified_at > &cutoff {
                    // Don't need an EB from this pipeline if it was certified so recently that it may not have propagated.
                    continue;
                }

                if !actual_referenced_slots.contains(&expected_slot) {
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

    fn finish_generating_vote_bundle(&mut self, votes: VoteBundle) -> Result<()> {
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
                    .earliest_eb_cert_times_by_slot
                    .entry(eb.slot)
                    .or_insert(self.clock.now());
            }
        }
        let votes = Arc::new(votes);
        self.leios
            .votes
            .insert(votes.id, VoteBundleState::Received(votes.clone()));
        for peer in &self.consumers {
            self.send_to(*peer, SimulationMessage::AnnounceVotes(votes.id))?;
        }
        Ok(())
    }

    // Simulates the output of a VRF using this node's stake (if any).
    fn run_vrf(&mut self, success_rate: f64) -> Option<u64> {
        let target_vrf_stake = compute_target_vrf_stake(self.stake, self.total_stake, success_rate);
        let result = self.rng.random_range(0..self.total_stake);
        if result < target_vrf_stake {
            Some(result)
        } else {
            None
        }
    }

    fn send_to(&self, to: NodeId, msg: SimulationMessage) -> Result<()> {
        if self.trace {
            trace!(
                "node {} sent msg of size {} to node {to}",
                self.name,
                msg.bytes_size()
            );
        }
        self.clock.start_task();
        self.msg_sink
            .send_to(to, msg.bytes_size(), msg.protocol(), msg, self.clock.now())
    }

    fn slot_to_pipeline(&self, slot: u64) -> u64 {
        slot / self.sim_config.stage_length
    }
}

fn compute_target_vrf_stake(stake: u64, total_stake: u64, success_rate: f64) -> u64 {
    let ratio = stake as f64 / total_stake as f64;
    (total_stake as f64 * ratio * success_rate) as u64
}

fn vrf_probabilities(probability: f64) -> impl Iterator<Item = f64> {
    let final_success_rate = Some(probability.fract()).filter(|f| *f > 0.0);
    std::iter::repeat_n(1.0, probability.trunc() as usize).chain(final_success_rate)
}
