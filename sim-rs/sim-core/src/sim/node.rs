use std::{
    collections::{hash_map::Entry, BTreeMap, BTreeSet, HashMap, HashSet},
    sync::Arc,
};

use anyhow::Result;
use netsim_async::HasBytesSize as _;
use priority_queue::PriorityQueue;
use rand::Rng as _;
use rand_chacha::ChaChaRng;
use tokio::{
    select,
    sync::{mpsc, watch},
};
use tracing::{info, trace};

use crate::{
    clock::{Clock, Timestamp},
    config::{NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::{
        Block, EndorserBlock, EndorserBlockId, InputBlock, InputBlockHeader, InputBlockId,
        NoVoteReason, Transaction, TransactionId, Vote,
    },
    network::{NetworkSink, NetworkSource},
};

use super::SimulationMessage;

enum TransactionView {
    Pending,
    Received(Arc<Transaction>),
}

pub struct Node {
    pub id: NodeId,
    trace: bool,
    sim_config: Arc<SimConfiguration>,
    msg_source: NetworkSource<SimulationMessage>,
    msg_sink: NetworkSink<SimulationMessage>,
    slot_receiver: watch::Receiver<u64>,
    tx_source: mpsc::UnboundedReceiver<Arc<Transaction>>,
    tracker: EventTracker,
    rng: ChaChaRng,
    clock: Clock,
    stake: u64,
    total_stake: u64,
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
    votes_by_eb: BTreeMap<EndorserBlockId, BTreeSet<Vote>>,
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
        slot_receiver: watch::Receiver<u64>,
        tx_source: mpsc::UnboundedReceiver<Arc<Transaction>>,
        tracker: EventTracker,
        rng: ChaChaRng,
        clock: Clock,
    ) -> Self {
        let id = config.id;
        let stake = config.stake;
        let peers = config.peers.clone();
        Self {
            id,
            trace: sim_config.trace_nodes.contains(&id),
            sim_config,
            msg_source,
            msg_sink,
            slot_receiver,
            tx_source,
            tracker,
            rng,
            clock,
            stake,
            total_stake,
            peers,
            txs: HashMap::new(),
            praos: NodePraosState::default(),
            leios: NodeLeiosState::default(),
        }
    }

    pub async fn run(mut self) -> Result<()> {
        loop {
            select! {
                change_res = self.slot_receiver.changed() => {
                    if change_res.is_err() {
                        // sim has stopped running
                        break;
                    }
                    let slot = *self.slot_receiver.borrow();
                    self.handle_new_slot(slot)?;
                }
                maybe_tx = self.tx_source.recv() => {
                    let Some(tx) = maybe_tx else {
                        // sim has stopped running
                        break;
                    };
                    self.receive_tx(self.id, tx)?;
                }
                maybe_msg = self.msg_source.recv() => {
                    let Some((from, msg)) = maybe_msg else {
                        // sim has stopped running
                        break;
                    };
                    match msg {
                        // TX propagation
                        SimulationMessage::AnnounceTx(id) => {
                            self.receive_announce_tx(from, id)?;
                        }
                        SimulationMessage::RequestTx(id) => {
                            self.receive_request_tx(from, id)?;
                        }
                        SimulationMessage::Tx(tx) => {
                            self.receive_tx(from, tx)?;
                        }

                        // Block propagation
                        SimulationMessage::RollForward(slot) => {
                            self.receive_roll_forward(from, slot)?;
                        }
                        SimulationMessage::RequestBlock(slot) => {
                            self.receive_request_block(from, slot)?;
                        }
                        SimulationMessage::Block(block) => {
                            self.receive_block(from, block)?;
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
                            self.receive_ib(from, ib)?;
                        }

                        // EB propagation
                        SimulationMessage::AnnounceEB(id) => {
                            self.receive_announce_eb(from, id)?;
                        }
                        SimulationMessage::RequestEB(id) => {
                            self.receive_request_eb(from, id)?;
                        }
                        SimulationMessage::EB(eb) => {
                            self.receive_eb(from, eb)?;
                        }

                        // Voting
                        SimulationMessage::Votes(votes) => {
                            self.receive_votes(from, votes)?;
                        }
                    }
                }
            };
        }
        Ok(())
    }

    fn handle_new_slot(&mut self, slot: u64) -> Result<()> {
        // The beginning of a new slot is the end of an old slot.
        // Publish any input blocks left over from the last slot

        if slot % self.sim_config.stage_length == 0 {
            // A new stage has begun.

            // Vote for any EBs which satisfy all requirements.
            self.vote_for_endorser_blocks(slot)?;

            // Generate any EBs we're allowed to in this slot.
            self.generate_endorser_blocks(slot)?;

            // Decide how many IBs to generate in each slot.
            self.schedule_input_block_generation(slot);
        }

        // Generate any IBs scheduled for this slot.
        self.generate_input_blocks(slot)?;

        self.try_generate_praos_block(slot)?;

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
                    slot,
                    producer: self.id,
                    index: index as u64,
                    vrf,
                    timestamp: self.clock.now(),
                })
                .collect();
            self.leios.ibs_to_generate.insert(slot, headers);
        }
    }

    fn generate_endorser_blocks(&mut self, slot: u64) -> Result<()> {
        for next_p in vrf_probabilities(self.sim_config.eb_generation_probability) {
            if self.run_vrf(next_p).is_some() {
                let mut eb = EndorserBlock {
                    slot,
                    producer: self.id,
                    ibs: vec![],
                };
                self.try_filling_eb(&mut eb);
                self.generate_eb(eb)?;
                // A node should only generate at most 1 EB per slot
                return Ok(());
            }
        }
        Ok(())
    }

    fn vote_for_endorser_blocks(&mut self, slot: u64) -> Result<()> {
        for next_p in vrf_probabilities(self.sim_config.vote_probability) {
            if self.run_vrf(next_p).is_some() {
                let Some(eb_slot) = slot.checked_sub(self.sim_config.stage_length) else {
                    return Ok(());
                };
                let Some(ebs) = self.leios.ebs_by_slot.remove(&eb_slot) else {
                    return Ok(());
                };
                let mut votes = vec![];
                for eb_id in ebs {
                    let eb = self.leios.ebs.get(&eb_id).unwrap();
                    match self.should_vote_for(slot, eb) {
                        Ok(()) => {
                            let vote = Vote {
                                slot,
                                producer: self.id,
                                eb: eb_id,
                            };
                            votes.push(vote);
                        }
                        Err(reason) => {
                            self.tracker.track_no_vote(slot, self.id, eb_id, reason);
                        }
                    }
                }
                if !votes.is_empty() {
                    self.send_votes(votes)?;
                }
                return Ok(());
            }
        }
        Ok(())
    }

    fn generate_input_blocks(&mut self, slot: u64) -> Result<()> {
        let Some(headers) = self.leios.ibs_to_generate.remove(&slot) else {
            return Ok(());
        };
        for header in headers {
            let mut ib = InputBlock {
                header,
                transactions: vec![],
            };
            self.try_filling_ib(&mut ib);
            self.generate_ib(ib)?;
        }
        Ok(())
    }

    fn try_generate_praos_block(&mut self, slot: u64) -> Result<()> {
        // L1 block generation
        let Some(vrf) = self.run_vrf(self.sim_config.block_generation_probability) else {
            return Ok(());
        };

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
            transactions,
        };
        self.tracker.track_praos_block_generated(&block);
        self.publish_block(Arc::new(block))?;

        Ok(())
    }

    fn publish_block(&mut self, block: Arc<Block>) -> Result<()> {
        // Do not remove TXs in these blocks from the leios mempool.
        // Wait until we learn more about how praos and leios interact.
        for peer in &self.peers {
            if !self
                .praos
                .peer_heads
                .get(peer)
                .is_some_and(|&s| s >= block.slot)
            {
                self.send_to(*peer, SimulationMessage::RollForward(block.slot))?;
                self.praos.peer_heads.insert(*peer, block.slot);
            }
        }
        self.praos.blocks.insert(block.slot, block);
        Ok(())
    }

    fn receive_announce_tx(&mut self, from: NodeId, id: TransactionId) -> Result<()> {
        if let Entry::Vacant(e) = self.txs.entry(id) {
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

    fn receive_tx(&mut self, from: NodeId, tx: Arc<Transaction>) -> Result<()> {
        let id = tx.id;
        if from != self.id {
            self.tracker
                .track_transaction_received(tx.id, from, self.id);
        }
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

    fn receive_block(&mut self, from: NodeId, block: Arc<Block>) -> Result<()> {
        self.tracker
            .track_praos_block_received(&block, from, self.id);
        if self
            .praos
            .blocks
            .insert(block.slot, block.clone())
            .is_none()
        {
            // Do not remove TXs in these blocks from the leios mempool.
            // Wait until we learn more about how praos and leios interact.
            let head = self.praos.peer_heads.entry(from).or_default();
            if *head < block.slot {
                *head = block.slot
            }
            self.publish_block(block)?;
        }
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
        let id = header.id();
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

    fn receive_ib(&mut self, from: NodeId, ib: Arc<InputBlock>) -> Result<()> {
        let id = ib.header.id();
        self.tracker.track_ib_received(id, from, self.id);
        for transaction in &ib.transactions {
            // Do not include transactions from this IB in any IBs we produce ourselves.
            self.leios.mempool.remove(&transaction.id);
        }
        self.leios
            .ibs_by_slot
            .entry(ib.header.slot)
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

    fn receive_eb(&mut self, from: NodeId, eb: Arc<EndorserBlock>) -> Result<()> {
        let id = eb.id();
        self.tracker.track_eb_received(id, from, self.id);
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

    fn receive_votes(&mut self, from: NodeId, votes: Arc<Vec<Vote>>) -> Result<()> {
        self.tracker.track_votes_received(&votes, from, self.id);
        for vote in votes.iter() {
            let eb_votes = self.leios.votes_by_eb.entry(vote.eb).or_default();
            if !eb_votes.insert(vote.clone()) {
                return Ok(());
            }
        }
        // We haven't seen these votes before, so propagate them to our neighbors
        for peer in &self.peers {
            if *peer == from {
                continue;
            }
            self.tracker.track_votes_sent(&votes, self.id, *peer);
            self.send_to(*peer, SimulationMessage::Votes(votes.clone()))?;
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

    fn generate_ib(&mut self, mut ib: InputBlock) -> Result<()> {
        ib.header.timestamp = self.clock.now();
        let ib = Arc::new(ib);

        self.tracker.track_ib_generated(&ib);

        let id = ib.header.id();
        self.leios
            .ibs_by_slot
            .entry(ib.header.slot)
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

    fn generate_eb(&mut self, eb: EndorserBlock) -> Result<()> {
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

    fn send_votes(&mut self, votes: Vec<Vote>) -> Result<()> {
        for vote in &votes {
            self.tracker.track_vote(vote);
            self.leios
                .votes_by_eb
                .entry(vote.eb)
                .or_default()
                .insert(vote.clone());
        }
        let votes = Arc::new(votes);
        for peer in &self.peers {
            self.tracker.track_votes_sent(&votes, self.id, *peer);
            self.send_to(*peer, SimulationMessage::Votes(votes.clone()))?;
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
