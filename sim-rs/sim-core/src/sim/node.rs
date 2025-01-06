use std::{
    collections::{btree_map, hash_map, BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet},
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
    config::{NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::{
        Block, Endorsement, EndorserBlock, EndorserBlockId, InputBlock, InputBlockHeader,
        InputBlockId, NoVoteReason, Transaction, TransactionId, VoteBundle, VoteBundleId,
    },
    network::{NetworkSink, NetworkSource},
};

use super::{
    cpu::{CpuTaskQueue, Subtask},
    SimulationMessage,
};

enum TransactionView {
    Pending,
    Received(Arc<Transaction>),
}

enum CpuTask {
    /// A transaction has been received and validated, and is ready to propagate
    TransactionValidated(NodeId, Arc<Transaction>),
    /// A Praos block has been generated and is ready to propagate
    PraosBlockGenerated(Block),
    /// A Praos block has been received and validated, and is ready to propagate
    PraosBlockValidated(NodeId, Arc<Block>),
    /// An input block has been generated and is ready to propagate
    InputBlockGenerated(InputBlock),
    /// An input block has been received and validated, and is ready to propagate
    InputBlockValidated(NodeId, Arc<InputBlock>),
    /// An endorser block has been generated and is ready to propagate
    EndorserBlockGenerated(EndorserBlock),
    /// An endorser block has been received and validated, and is ready to propagate
    EndorserBlockValidated(NodeId, Arc<EndorserBlock>),
    /// A bundle of votes has been generated and is ready to propagate
    VoteBundleGenerated(VoteBundle),
    /// A bundle of votes has been received and validated, and is ready to propagate
    VoteBundleValidated(NodeId, Arc<VoteBundle>),
}

impl CpuTask {
    fn cpu_times(&self, config: &SimConfiguration) -> Vec<Duration> {
        match self {
            Self::TransactionValidated(_, _) => vec![config.tx_validation_cpu_time],
            Self::PraosBlockGenerated(block) => {
                let base_time = config.block_generation_cpu_time;
                if block.endorsement.is_some() {
                    vec![base_time + config.certificate_generation_cpu_time]
                } else {
                    vec![base_time]
                }
            }
            Self::PraosBlockValidated(_, block) => {
                let base_time = config.block_validation_cpu_time;
                if block.endorsement.is_some() {
                    vec![base_time + config.certificate_validation_cpu_time]
                } else {
                    vec![base_time]
                }
            }
            Self::InputBlockGenerated(_) => vec![config.ib_generation_cpu_time],
            Self::InputBlockValidated(_, _) => vec![config.ib_validation_cpu_time],
            Self::EndorserBlockGenerated(_) => vec![config.eb_generation_cpu_time],
            Self::EndorserBlockValidated(_, _) => vec![config.eb_validation_cpu_time],
            Self::VoteBundleGenerated(votes) => {
                vec![config.vote_generation_cpu_time; votes.ebs.len()]
            }
            Self::VoteBundleValidated(_, votes) => {
                vec![config.vote_validation_cpu_time; votes.ebs.len()]
            }
        }
    }
}

/// Things that can happen next for a node
enum NodeEvent {
    /// A new slot has started.
    NewSlot(u64),
    /// A message has been received.
    MessageReceived(NodeId, SimulationMessage),
    /// A core has finished running some task, and is free to run another.
    CpuSubtaskCompleted(Subtask),
}

pub struct Node {
    pub id: NodeId,
    trace: bool,
    sim_config: Arc<SimConfiguration>,
    msg_source: Option<NetworkSource<SimulationMessage>>,
    msg_sink: NetworkSink<SimulationMessage>,
    tx_source: Option<mpsc::UnboundedReceiver<Arc<Transaction>>>,
    events: BinaryHeap<FutureEvent<NodeEvent>>,
    tracker: EventTracker,
    rng: ChaChaRng,
    clock: ClockBarrier,
    stake: u64,
    total_stake: u64,
    cpu: CpuTaskQueue<CpuTask>,
    peers: Vec<NodeId>,
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
    ebs: BTreeMap<EndorserBlockId, Arc<EndorserBlock>>,
    ebs_by_slot: BTreeMap<u64, Vec<EndorserBlockId>>,
    votes_by_eb: BTreeMap<EndorserBlockId, Vec<NodeId>>,
    votes: BTreeMap<VoteBundleId, VoteBundleState>,
}

enum InputBlockState {
    Pending(InputBlockHeader),
    Requested(InputBlockHeader),
    Received(Arc<InputBlock>),
}
impl InputBlockState {
    fn header(&self) -> &InputBlockHeader {
        match self {
            Self::Pending(header) => header,
            Self::Requested(header) => header,
            Self::Received(ib) => &ib.header,
        }
    }
}

enum VoteBundleState {
    Requested,
    Received(Arc<VoteBundle>),
}

#[derive(Default)]
struct PeerInputBlockRequests {
    pending: PriorityQueue<InputBlockId, Timestamp>,
    active: HashSet<InputBlockId>,
}

impl Node {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        total_stake: u64,
        msg_source: NetworkSource<SimulationMessage>,
        msg_sink: NetworkSink<SimulationMessage>,
        tx_source: mpsc::UnboundedReceiver<Arc<Transaction>>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: ClockBarrier,
    ) -> Self {
        let id = config.id;
        let stake = config.stake;
        let cpu = CpuTaskQueue::new(config.cores, config.cpu_multiplier);
        let peers = config.peers.clone();
        let mut events = BinaryHeap::new();
        events.push(FutureEvent(clock.now(), NodeEvent::NewSlot(0)));

        Self {
            id,
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
            peers,
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

    fn schedule_cpu_task(&mut self, task: CpuTask) {
        let cpu_times = task.cpu_times(&self.sim_config);
        for subtask in self.cpu.schedule_task(task, cpu_times) {
            self.schedule_cpu_subtask(subtask);
        }
    }

    fn schedule_cpu_subtask(&mut self, subtask: Subtask) {
        let timestamp = self.clock.now() + subtask.duration;
        self.events.push(FutureEvent(
            timestamp,
            NodeEvent::CpuSubtaskCompleted(subtask),
        ))
    }

    pub async fn run(mut self) -> Result<()> {
        // TODO: split struct Node into the mechanics (which can then be extracted here) and the high-level logic that handles messages
        // (then we could remove these Option shenanigans)
        let mut msg_source = self.msg_source.take().unwrap();
        let mut tx_source = self.tx_source.take().unwrap();

        loop {
            select! {
                maybe_msg = msg_source.recv() => {
                    let Some((from, timestamp, msg)) = maybe_msg else {
                        // sim has stopped running
                        break;
                    };
                    self.events.push(FutureEvent(timestamp, NodeEvent::MessageReceived(from, msg)));
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
                        NodeEvent::MessageReceived(from, msg) => self.handle_message(from, msg)?,
                        NodeEvent::CpuSubtaskCompleted(subtask) => {
                            let (finished_task, next_subtask) = self.cpu.complete_subtask(subtask);
                            if let Some(subtask) = next_subtask {
                                self.schedule_cpu_subtask(subtask);
                            }
                            let Some(task) = finished_task else {
                                continue;
                            };
                            match task {
                                CpuTask::TransactionValidated(from, tx) => self.propagate_tx(from, tx)?,
                                CpuTask::PraosBlockGenerated(block) => self.finish_generating_block(block)?,
                                CpuTask::PraosBlockValidated(from, block) => self.finish_validating_block(from, block)?,
                                CpuTask::InputBlockGenerated(ib) => self.finish_generating_ib(ib)?,
                                CpuTask::InputBlockValidated(from, ib) => self.finish_validating_ib(from, ib)?,
                                CpuTask::EndorserBlockGenerated(eb) => self.finish_generating_eb(eb)?,
                                CpuTask::EndorserBlockValidated(from, eb) => self.finish_validating_eb(from, eb)?,
                                CpuTask::VoteBundleGenerated(votes) => self.finish_generating_vote_bundle(votes)?,
                                CpuTask::VoteBundleValidated(from, votes) => self.finish_validating_vote_bundle(from, votes)?,
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
                self.receive_ib_header(from, header, has_body)?;
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

            // Vote for any EBs which satisfy all requirements.
            self.vote_for_endorser_blocks(slot);

            // Generate any EBs we're allowed to in this slot.
            self.generate_endorser_blocks(slot);

            // Decide how many IBs to generate in each slot.
            self.schedule_input_block_generation(slot);
        }

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
        for next_p in vrf_probabilities(self.sim_config.ib_generation_probability) {
            if let Some(vrf) = self.run_vrf(next_p) {
                let vrf_slot = if self.sim_config.uniform_ib_generation {
                    // IBs are generated at the start of any slot within this stage
                    slot + self.rng.gen_range(0..self.sim_config.stage_length)
                } else {
                    // IBs are generated at the start of the first slot of this stage
                    slot
                };
                slot_vrfs.entry(vrf_slot).or_default().push(vrf);
            }
        }
        for (slot, vrfs) in slot_vrfs {
            let headers = vrfs
                .into_iter()
                .enumerate()
                .map(|(index, vrf)| InputBlockHeader {
                    id: InputBlockId {
                        slot,
                        producer: self.id,
                        index: index as u64,
                    },
                    vrf,
                    timestamp: self.clock.now(),
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
                    producer: self.id,
                });
                let mut eb = EndorserBlock {
                    slot,
                    producer: self.id,
                    ibs: vec![],
                };
                self.try_filling_eb(&mut eb);
                self.schedule_cpu_task(CpuTask::EndorserBlockGenerated(eb));
                // A node should only generate at most 1 EB per slot
                return;
            }
        }
    }

    fn vote_for_endorser_blocks(&mut self, slot: u64) {
        let Some(eb_slot) = slot.checked_sub(self.sim_config.stage_length) else {
            return;
        };
        let Some(ebs) = self.leios.ebs_by_slot.get(&eb_slot) else {
            return;
        };
        let mut ebs = ebs.clone();
        let vrf_wins = vrf_probabilities(self.sim_config.vote_probability)
            .filter_map(|f| self.run_vrf(f))
            .count();
        if vrf_wins == 0 {
            return;
        }
        ebs.retain(|eb_id| {
            let eb = self.leios.ebs.get(eb_id).unwrap();
            match self.should_vote_for(slot, eb) {
                Ok(()) => true,
                Err(reason) => {
                    self.tracker.track_no_vote(slot, self.id, *eb_id, reason);
                    false
                }
            }
        });
        if ebs.is_empty() {
            return;
        }
        let votes_allowed = if self.sim_config.one_vote_per_vrf {
            // For every VRF lottery you won, you can vote for one EB
            vrf_wins
        } else {
            // For every VRF lottery you won, you can vote for every EB
            vrf_wins * ebs.len()
        };
        let votes = VoteBundle {
            id: VoteBundleId {
                slot,
                producer: self.id,
            },
            ebs: ebs.iter().cloned().cycle().take(votes_allowed).collect(),
        };
        if !votes.ebs.is_empty() {
            self.tracker.track_vote_lottery_won(&votes);
            self.schedule_cpu_task(CpuTask::VoteBundleGenerated(votes));
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
            self.schedule_cpu_task(CpuTask::InputBlockGenerated(ib));
        }
    }

    fn try_generate_praos_block(&mut self, slot: u64) -> Result<()> {
        // L1 block generation
        let Some(vrf) = self.run_vrf(self.sim_config.block_generation_probability) else {
            return Ok(());
        };

        // Let's see if we are minting an RB
        let endorsement = self.choose_endorsed_block();
        if let Some(endorsement) = &endorsement {
            // If we are, get all referenced TXs out of the mempool
            let Some(eb) = self.leios.ebs.get(&endorsement.eb) else {
                bail!("Missing endorsement block {}", endorsement.eb);
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

        // Fill a block with as many pending transactions as can fit
        let mut size = 0;
        let mut transactions = vec![];
        while let Some((id, tx)) = self.praos.mempool.first_key_value() {
            if size + tx.bytes > self.sim_config.max_block_size {
                break;
            }
            size += tx.bytes;
            let id = *id;
            transactions.push(self.praos.mempool.remove(&id).unwrap());
        }

        let block = Block {
            slot,
            producer: self.id,
            vrf,
            endorsement,
            transactions,
        };
        self.tracker.track_praos_block_lottery_won(&block);
        self.schedule_cpu_task(CpuTask::PraosBlockGenerated(block));

        Ok(())
    }

    fn choose_endorsed_block(&mut self) -> Option<Endorsement> {
        // an EB is eligible for endorsement if it has this many votes
        let vote_threshold = self.sim_config.vote_threshold;
        // and if it is not in a pipeline already represented in the chain
        // (NB: all EBs produced in a pipeline are produced during the same slot)
        let forbidden_slots: HashSet<u64> = self
            .praos
            .blocks
            .values()
            .flat_map(|b| b.endorsement.iter())
            .map(|e| e.eb.slot)
            .collect();

        let (&block, _) = self
            .leios
            .votes_by_eb
            .iter()
            .filter(|(eb, votes)| {
                votes.len() as u64 >= vote_threshold && !forbidden_slots.contains(&eb.slot)
            })
            .max_by_key(|(eb, votes)| (self.count_txs_in_eb(eb), votes.len()))?;

        let (block, votes) = self.leios.votes_by_eb.remove_entry(&block)?;

        Some(Endorsement { eb: block, votes })
    }

    fn count_txs_in_eb(&self, eb_id: &EndorserBlockId) -> Option<usize> {
        let eb = self.leios.ebs.get(eb_id)?;
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
        // Do not remove TXs in these blocks from the leios mempool.
        // Wait until we learn more about how praos and leios interact.
        for peer in &self.peers {
            if self
                .praos
                .peer_heads
                .get(peer)
                .is_none_or(|&s| s < block.slot)
            {
                self.send_to(*peer, SimulationMessage::RollForward(block.slot))?;
                self.praos.peer_heads.insert(*peer, block.slot);
            }
        }
        self.praos.blocks.insert(block.slot, block);
        Ok(())
    }

    fn receive_announce_tx(&mut self, from: NodeId, id: TransactionId) -> Result<()> {
        if let hash_map::Entry::Vacant(e) = self.txs.entry(id) {
            e.insert(TransactionView::Pending);
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
        self.schedule_cpu_task(CpuTask::TransactionValidated(from, tx));
    }

    fn generate_tx(&mut self, tx: Arc<Transaction>) -> Result<()> {
        self.tracker.track_transaction_generated(&tx, self.id);
        self.propagate_tx(self.id, tx)
    }

    fn propagate_tx(&mut self, from: NodeId, tx: Arc<Transaction>) -> Result<()> {
        let id = tx.id;
        if self.trace {
            info!("node {} saw tx {id}", self.id);
        }
        self.txs.insert(id, TransactionView::Received(tx.clone()));
        self.praos.mempool.insert(tx.id, tx.clone());
        for peer in &self.peers {
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
        self.schedule_cpu_task(CpuTask::PraosBlockValidated(from, block));
    }

    fn finish_validating_block(&mut self, from: NodeId, block: Arc<Block>) -> Result<()> {
        if let Some(old_block) = self.praos.blocks.get(&block.slot) {
            // SLOT BATTLE!!! lower VRF wins
            if old_block.vrf <= block.vrf {
                // We like our block better than this new one.
                return Ok(());
            }
        }
        self.praos.blocks.insert(block.slot, block.clone());

        let head = self.praos.peer_heads.entry(from).or_default();
        if *head < block.slot {
            *head = block.slot
        }
        self.publish_block(block)?;
        Ok(())
    }

    fn receive_announce_ib_header(&mut self, from: NodeId, id: InputBlockId) -> Result<()> {
        self.send_to(from, SimulationMessage::RequestIBHeader(id))?;
        Ok(())
    }

    fn receive_request_ib_header(&mut self, from: NodeId, id: InputBlockId) -> Result<()> {
        if let Some(ib) = self.leios.ibs.get(&id) {
            let header = ib.header().clone();
            let have_body = matches!(ib, InputBlockState::Received(_));
            self.send_to(from, SimulationMessage::IBHeader(header, have_body))?;
        }
        Ok(())
    }

    fn receive_ib_header(
        &mut self,
        from: NodeId,
        header: InputBlockHeader,
        has_body: bool,
    ) -> Result<()> {
        let id = header.id;
        if self.leios.ibs.contains_key(&id) {
            return Ok(());
        }
        self.leios.ibs.insert(id, InputBlockState::Pending(header));
        // We haven't seen this header before, so propagate it to our neighbors
        for peer in &self.peers {
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
        let Some(InputBlockState::Pending(header)) = self.leios.ibs.get(&id) else {
            return Ok(());
        };
        // Do we have capacity to request this block?
        let reqs = self.leios.ib_requests.entry(from).or_default();
        if reqs.active.len() < self.sim_config.max_ib_requests_per_peer {
            // If so, make the request
            self.leios
                .ibs
                .insert(id, InputBlockState::Requested(header.clone()));
            reqs.active.insert(id);
            self.send_to(from, SimulationMessage::RequestIB(id))?;
        } else {
            // If not, just track that this peer has this IB when we're ready
            reqs.pending.push(id, header.timestamp);
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
        self.schedule_cpu_task(CpuTask::InputBlockValidated(from, ib));
    }

    fn finish_validating_ib(&mut self, from: NodeId, ib: Arc<InputBlock>) -> Result<()> {
        let id = ib.header.id;
        for transaction in &ib.transactions {
            // Do not include transactions from this IB in any IBs we produce ourselves.
            self.leios.mempool.remove(&transaction.id);
        }
        self.leios
            .ibs_by_slot
            .entry(ib.header.id.slot)
            .or_default()
            .push(id);
        self.leios.ibs.insert(id, InputBlockState::Received(ib));

        for peer in &self.peers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceIB(id))?;
        }

        // Mark that this IB is no longer pending
        let reqs = self.leios.ib_requests.entry(from).or_default();
        reqs.active.remove(&id);

        // We now have capacity to request one more IB from this peer
        while let Some((id, _)) = reqs.pending.pop() {
            let Some(InputBlockState::Pending(header)) = self.leios.ibs.get(&id) else {
                // We fetched this IB from some other node already
                continue;
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
        self.send_to(from, SimulationMessage::RequestEB(id))?;
        Ok(())
    }

    fn receive_request_eb(&mut self, from: NodeId, id: EndorserBlockId) -> Result<()> {
        if let Some(eb) = self.leios.ebs.get(&id) {
            self.tracker.track_eb_sent(id, self.id, from);
            self.send_to(from, SimulationMessage::EB(eb.clone()))?;
        }
        Ok(())
    }

    fn receive_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) {
        self.tracker.track_eb_received(eb.id(), from, self.id);
        self.schedule_cpu_task(CpuTask::EndorserBlockValidated(from, eb));
    }

    fn finish_validating_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) -> Result<()> {
        let id = eb.id();
        if self.leios.ebs.insert(id, eb).is_some() {
            return Ok(());
        }
        self.leios.ebs_by_slot.entry(id.slot).or_default().push(id);
        // We haven't seen this EB before, so propagate it to our neighbors
        for peer in &self.peers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceEB(id))?;
        }
        Ok(())
    }

    fn receive_announce_votes(&mut self, from: NodeId, id: VoteBundleId) -> Result<()> {
        if let btree_map::Entry::Vacant(e) = self.leios.votes.entry(id) {
            e.insert(VoteBundleState::Requested);
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
        self.schedule_cpu_task(CpuTask::VoteBundleValidated(from, votes));
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
        for eb in votes.ebs.iter() {
            self.leios
                .votes_by_eb
                .entry(*eb)
                .or_default()
                .push(votes.id.producer);
        }
        // We haven't seen these votes before, so propagate them to our neighbors
        for peer in &self.peers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceVotes(id))?;
        }
        Ok(())
    }

    fn try_filling_ib(&mut self, ib: &mut InputBlock) {
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
        for peer in &self.peers {
            self.send_to(*peer, SimulationMessage::AnnounceIBHeader(id))?;
        }
        Ok(())
    }

    fn try_filling_eb(&mut self, eb: &mut EndorserBlock) {
        let config = &self.sim_config;
        let Some(earliest_slot) = eb
            .slot
            .checked_sub(config.stage_length * (config.deliver_stage_count + 1))
        else {
            return;
        };
        for slot in earliest_slot..(earliest_slot + config.stage_length) {
            let Some(ibs) = self.leios.ibs_by_slot.remove(&slot) else {
                continue;
            };
            eb.ibs.extend(ibs);
        }
    }

    fn finish_generating_eb(&mut self, eb: EndorserBlock) -> Result<()> {
        let eb = Arc::new(eb);
        self.tracker.track_eb_generated(&eb);

        let id = eb.id();
        self.leios.ebs.insert(id, eb.clone());
        self.leios.ebs_by_slot.entry(id.slot).or_default().push(id);
        for peer in &self.peers {
            self.send_to(*peer, SimulationMessage::AnnounceEB(id))?;
        }
        Ok(())
    }

    fn should_vote_for(&self, slot: u64, eb: &EndorserBlock) -> Result<(), NoVoteReason> {
        let stage_length = self.sim_config.stage_length;
        let deliver_stage_count = self.sim_config.deliver_stage_count;

        let Some(ib_slot_start) = slot.checked_sub(stage_length * (deliver_stage_count + 2)) else {
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
        Ok(())
    }

    fn finish_generating_vote_bundle(&mut self, votes: VoteBundle) -> Result<()> {
        self.tracker.track_votes_generated(&votes);
        for eb in &votes.ebs {
            self.leios
                .votes_by_eb
                .entry(*eb)
                .or_default()
                .push(votes.id.producer);
        }
        let votes = Arc::new(votes);
        self.leios
            .votes
            .insert(votes.id, VoteBundleState::Received(votes.clone()));
        for peer in &self.peers {
            self.send_to(*peer, SimulationMessage::AnnounceVotes(votes.id))?;
        }
        Ok(())
    }

    // Simulates the output of a VRF using this node's stake (if any).
    fn run_vrf(&mut self, success_rate: f64) -> Option<u64> {
        let target_vrf_stake = compute_target_vrf_stake(self.stake, self.total_stake, success_rate);
        let result = self.rng.gen_range(0..self.total_stake);
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
                self.id,
                msg.bytes_size()
            );
        }
        self.clock.start_task();
        self.msg_sink.send_to(to, msg)
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
