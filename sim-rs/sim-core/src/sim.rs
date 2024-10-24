use std::{
    collections::{BTreeMap, BTreeSet, HashSet, VecDeque},
    sync::Arc,
    time::Duration,
};

use anyhow::{bail, Context, Result};
use event_queue::EventQueue;
use netsim_async::{EdgePolicy, HasBytesSize, Latency};
use priority_queue::PriorityQueue;
use rand::Rng as _;
use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
use rand_distr::Distribution as _;
use tracing::{debug, info, trace};

use crate::{
    clock::{Clock, Timestamp},
    config::{NodeConfiguration, NodeId, SimConfiguration},
    events::EventTracker,
    model::{Block, InputBlock, InputBlockHeader, InputBlockId, Transaction, TransactionId},
    network::{Network, NetworkSink},
};

mod event_queue;

pub struct Simulation {
    config: SimConfiguration,
    tracker: EventTracker,
    rng: ChaChaRng,
    network: Network<SimulationMessage>,
    event_queue: EventQueue,
    nodes: BTreeMap<NodeId, Node>,
    next_tx_id: u64,
    unpublished_txs: VecDeque<Arc<Transaction>>,
    txs: BTreeMap<TransactionId, Arc<Transaction>>,
}

impl Simulation {
    pub fn new(config: SimConfiguration, tracker: EventTracker, clock: Clock) -> Result<Self> {
        let total_stake = config.nodes.iter().map(|p| p.stake).sum();

        let mut network = Network::new(config.timescale);

        let rng = ChaChaRng::seed_from_u64(config.seed);
        let mut nodes = BTreeMap::new();
        let mut msg_sources = vec![];
        for node_config in &config.nodes {
            let id = node_config.id;
            let (msg_source, msg_sink) = network.open(id).context("could not open socket")?;
            let node = Node::new(
                node_config,
                &config,
                total_stake,
                msg_sink,
                tracker.clone(),
                clock.clone(),
            );
            msg_sources.push((node.id, msg_source));
            nodes.insert(node.id, node);
        }
        for link_config in config.links.iter() {
            network.set_edge_policy(
                link_config.nodes.0,
                link_config.nodes.1,
                EdgePolicy {
                    latency: Latency::new(link_config.latency),
                    ..EdgePolicy::default()
                },
            )?;
        }

        let mut event_queue = EventQueue::new(clock, msg_sources);
        event_queue.queue_event(SimulationEvent::NewSlot(0), Duration::ZERO);
        event_queue.queue_event(SimulationEvent::NewTransaction, Duration::ZERO);
        Ok(Self {
            config,
            tracker,
            rng,
            network,
            event_queue,
            nodes,
            next_tx_id: 0,
            unpublished_txs: VecDeque::new(),
            txs: BTreeMap::new(),
        })
    }

    // Run the simulation indefinitely.
    pub async fn run(&mut self) -> Result<()> {
        while let Some(event) = self.event_queue.next_event().await {
            match event {
                SimulationEvent::NewSlot(slot) => self.handle_new_slot(slot)?,
                SimulationEvent::NewTransaction => self.generate_tx()?,
                SimulationEvent::NetworkMessage { from, to, msg } => {
                    if self.config.trace_nodes.contains(&to) {
                        trace!(
                            "node {to} received msg of size {} from node {from}",
                            msg.bytes_size()
                        );
                    }
                    let Some(target) = self.nodes.get_mut(&to) else {
                        bail!("unrecognized message target {to}");
                    };
                    match msg {
                        // TX propagation
                        SimulationMessage::AnnounceTx(id) => {
                            target.receive_announce_tx(from, id)?;
                        }
                        SimulationMessage::RequestTx(id) => {
                            let tx = self.txs.get(&id).expect("unexpected missing tx").clone();
                            target.receive_request_tx(from, tx)?;
                        }
                        SimulationMessage::Tx(tx) => {
                            self.tracker.track_transaction_received(tx.id, from, to);
                            target.receive_tx(from, tx)?;
                        }

                        // Block propagation
                        SimulationMessage::RollForward(slot) => {
                            target.receive_roll_forward(from, slot)?;
                        }
                        SimulationMessage::RequestBlock(slot) => {
                            target.receive_request_block(from, slot)?;
                        }
                        SimulationMessage::Block(block) => {
                            self.tracker.track_block_received(block.slot, from, to);
                            target.receive_block(from, block)?;
                        }

                        // IB header propagation
                        SimulationMessage::AnnounceIBHeader(id) => {
                            target.receive_announce_ib_header(from, id)?;
                        }
                        SimulationMessage::RequestIBHeader(id) => {
                            target.receive_request_ib_header(from, id)?;
                        }
                        SimulationMessage::IBHeader(header, has_body) => {
                            target.receive_ib_header(from, header, has_body)?;
                        }

                        // IB transmission
                        SimulationMessage::AnnounceIB(id) => {
                            target.receive_announce_ib(from, id)?;
                        }
                        SimulationMessage::RequestIB(id) => {
                            target.receive_request_ib(from, id)?;
                        }
                        SimulationMessage::IB(ib) => {
                            self.tracker.track_ib_received(ib.clone(), from, to);
                            target.receive_ib(from, ib)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    pub fn shutdown(self) -> Result<()> {
        self.network.shutdown()
    }

    fn handle_new_slot(&mut self, slot: u64) -> Result<()> {
        self.handle_input_block_generation(slot)?;
        self.try_generate_praos_block(slot)?;

        self.event_queue
            .queue_event(SimulationEvent::NewSlot(slot + 1), Duration::from_secs(1));
        Ok(())
    }

    fn handle_input_block_generation(&mut self, slot: u64) -> Result<()> {
        // Publish any input blocks from last round
        if slot > 0 {
            for node in self.nodes.values_mut() {
                node.finish_generating_ibs(slot - 1)?;
            }
        }

        let mut probability = self.config.ib_generation_probability;
        let mut block_counts = BTreeMap::new();
        while probability > 0.0 {
            let next_p = f64::min(probability, 1.0);
            for (id, _) in self.run_vrf_lottery(next_p) {
                *block_counts.entry(id).or_default() += 1;
            }
            probability -= 1.0;
        }
        for (id, count) in block_counts {
            self.get_node_mut(&id).begin_generating_ibs(slot, count)?;
        }
        Ok(())
    }

    fn try_generate_praos_block(&mut self, slot: u64) -> Result<()> {
        let vrf_winners = self.run_vrf_lottery(self.config.block_generation_probability);

        let winner = vrf_winners
            .iter()
            .max_by_key(|(_, result)| *result)
            .map(|(id, _)| *id);

        // L1 block generation
        if let Some(producer) = winner {
            let conflicts = vrf_winners
                .into_iter()
                .filter_map(|(id, _)| if producer != id { Some(id) } else { None })
                .collect();

            // Fill a block with as many pending transactions as can fit
            let mut size = 0;
            let mut transactions = vec![];
            while let Some(tx) = self.unpublished_txs.front() {
                if size + tx.bytes > self.config.max_block_size {
                    break;
                }
                size += tx.bytes;
                transactions.push(self.unpublished_txs.pop_front().unwrap());
            }

            let block = Block {
                slot,
                producer,
                conflicts,
                transactions,
            };
            self.get_node_mut(&producer)
                .publish_block(Arc::new(block.clone()))?;
            self.tracker.track_slot(slot, Some(block));
        } else {
            self.tracker.track_slot(slot, None);
        }

        Ok(())
    }

    fn run_vrf_lottery(&mut self, success_rate: f64) -> Vec<(NodeId, u64)> {
        self.nodes
            .values()
            .filter_map(|node| {
                let result = node.run_vrf(&mut self.rng, success_rate)?;
                Some((node.id, result))
            })
            .collect()
    }

    fn generate_tx(&mut self) -> Result<()> {
        let id = TransactionId::new(self.next_tx_id);
        let bytes = self
            .config
            .max_tx_size
            .min(self.config.transaction_size_bytes.sample(&mut self.rng) as u64);
        let tx = Arc::new(Transaction { id, bytes });

        // any node could be the first to see a transaction
        let publisher_id = self.choose_random_node();

        self.tracker.track_transaction(&tx, publisher_id);
        self.unpublished_txs.push_back(tx.clone());
        self.txs.insert(id, tx.clone());

        self.next_tx_id += 1;
        let ms_until_tx = self.config.transaction_frequency_ms.sample(&mut self.rng) as u64;
        self.event_queue.queue_event(
            SimulationEvent::NewTransaction,
            Duration::from_millis(ms_until_tx),
        );

        debug!("node {publisher_id} generated tx {id}");
        self.get_node_mut(&publisher_id)
            .receive_tx(publisher_id, tx)
    }

    fn get_node_mut(&mut self, id: &NodeId) -> &mut Node {
        self.nodes.get_mut(id).expect("chose nonexistent node")
    }

    fn choose_random_node(&mut self) -> NodeId {
        let index = self.rng.gen_range(0..self.nodes.len());
        NodeId::new(index)
    }
}

struct Node {
    id: NodeId,
    trace: bool,
    msg_sink: NetworkSink<SimulationMessage>,
    tracker: EventTracker,
    clock: Clock,
    stake: u64,
    total_stake: u64,
    max_ib_size: u64,
    max_ib_requests_per_peer: usize,
    peers: Vec<NodeId>,
    praos: NodePraosState,
    leios: NodeLeiosState,
}

#[derive(Default)]
struct NodePraosState {
    peer_heads: BTreeMap<NodeId, u64>,
    blocks_seen: BTreeSet<u64>,
    blocks: BTreeMap<u64, Arc<Block>>,
    txs_seen: BTreeSet<TransactionId>,
}

#[derive(Default)]
struct PeerInputBlockRequests {
    pending: PriorityQueue<InputBlockId, Timestamp>,
    active: HashSet<InputBlockId>,
}

struct PendingInputBlock {
    header: InputBlockHeader,
    has_been_requested: bool,
}

#[derive(Default)]
struct NodeLeiosState {
    mempool: BTreeMap<TransactionId, Arc<Transaction>>,
    unsent_ibs: BTreeMap<u64, VecDeque<InputBlock>>,
    ibs: BTreeMap<InputBlockId, Arc<InputBlock>>,
    pending_ibs: BTreeMap<InputBlockId, PendingInputBlock>,
    ib_requests: BTreeMap<NodeId, PeerInputBlockRequests>,
}

impl Node {
    fn new(
        config: &NodeConfiguration,
        sim_config: &SimConfiguration,
        total_stake: u64,
        msg_sink: NetworkSink<SimulationMessage>,
        tracker: EventTracker,
        clock: Clock,
    ) -> Self {
        let id = config.id;
        let stake = config.stake;
        let peers = config.peers.clone();
        Self {
            id,
            trace: sim_config.trace_nodes.contains(&id),
            msg_sink,
            tracker,
            clock,
            stake,
            total_stake,
            max_ib_size: sim_config.max_ib_size,
            max_ib_requests_per_peer: sim_config.max_ib_requests_per_peer,
            peers,
            praos: NodePraosState::default(),
            leios: NodeLeiosState::default(),
        }
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
        if self.praos.txs_seen.insert(id) {
            self.send_to(from, SimulationMessage::RequestTx(id))?;
        }
        Ok(())
    }

    fn receive_request_tx(&mut self, from: NodeId, tx: Arc<Transaction>) -> Result<()> {
        self.send_to(from, SimulationMessage::Tx(tx))
    }

    fn receive_tx(&mut self, from: NodeId, tx: Arc<Transaction>) -> Result<()> {
        let id = tx.id;
        if self.trace {
            info!("node {} saw tx {id}", self.id);
        }
        self.leios.mempool.insert(tx.id, tx);
        for peer in &self.peers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceTx(id))?;
        }
        self.try_fill_ibs()
    }

    fn receive_roll_forward(&mut self, from: NodeId, slot: u64) -> Result<()> {
        if self.praos.blocks_seen.insert(slot) {
            self.send_to(from, SimulationMessage::RequestBlock(slot))?;
        }
        Ok(())
    }

    fn receive_request_block(&mut self, from: NodeId, slot: u64) -> Result<()> {
        if let Some(block) = self.praos.blocks.get(&slot) {
            self.send_to(from, SimulationMessage::Block(block.clone()))?;
        }
        Ok(())
    }

    fn receive_block(&mut self, from: NodeId, block: Arc<Block>) -> Result<()> {
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
        if let Some(pending_ib) = self.leios.pending_ibs.get(&id) {
            // We don't have this IB, just the header. Send that.
            self.send_to(
                from,
                SimulationMessage::IBHeader(pending_ib.header.clone(), false),
            )?;
        } else if let Some(ib) = self.leios.ibs.get(&id) {
            // We have the full IB. Send the header, and also advertise that we have the full IB.
            self.send_to(from, SimulationMessage::IBHeader(ib.header.clone(), true))?;
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
        if self.leios.pending_ibs.contains_key(&id) {
            return Ok(());
        }
        self.leios.pending_ibs.insert(
            id,
            PendingInputBlock {
                header,
                has_been_requested: false,
            },
        );
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
        let Some(pending_ib) = self.leios.pending_ibs.get_mut(&id) else {
            return Ok(());
        };
        // Ignore IBs which have already been requested
        if pending_ib.has_been_requested {
            return Ok(());
        }
        // Do we have capacity to request this block?
        let reqs = self.leios.ib_requests.entry(from).or_default();
        if reqs.active.len() < self.max_ib_requests_per_peer {
            // If so, make the request
            pending_ib.has_been_requested = true;
            reqs.active.insert(id);
            self.send_to(from, SimulationMessage::RequestIB(id))?;
        } else {
            // If not, just track that this peer has this IB when we're ready
            reqs.pending.push(id, pending_ib.header.timestamp);
        }
        Ok(())
    }

    fn receive_request_ib(&mut self, from: NodeId, id: InputBlockId) -> Result<()> {
        if let Some(ib) = self.leios.ibs.get(&id) {
            self.send_to(from, SimulationMessage::IB(ib.clone()))?;
        }
        Ok(())
    }

    fn receive_ib(&mut self, from: NodeId, ib: Arc<InputBlock>) -> Result<()> {
        let id = ib.header.id();
        for transaction in &ib.transactions {
            // Do not include transactions from this IB in any IBs we produce ourselves.
            self.leios.mempool.remove(&transaction.id);
            for pending_ibs in self.leios.unsent_ibs.values_mut() {
                for pending_ib in pending_ibs {
                    pending_ib.transactions.retain(|tx| tx.id != transaction.id);
                }
            }
        }
        self.leios.ibs.insert(id, ib);

        for peer in &self.peers {
            if *peer == from {
                continue;
            }
            self.send_to(*peer, SimulationMessage::AnnounceIB(id))?;
        }

        // Mark that this IB is no longer pending
        self.leios.pending_ibs.remove(&id);
        let reqs = self.leios.ib_requests.entry(from).or_default();
        reqs.active.remove(&id);

        // We now have capacity to request one more IB from this peer
        while let Some((id, _)) = reqs.pending.pop() {
            let Some(pending_ib) = self.leios.pending_ibs.get_mut(&id) else {
                // We fetched this IB from some other node already
                continue;
            };
            if pending_ib.has_been_requested {
                // There's already a request for this IB in flight
                continue;
            }

            // Make the request
            pending_ib.has_been_requested = true;
            reqs.active.insert(id);
            self.send_to(from, SimulationMessage::RequestIB(id))?;
            break;
        }

        Ok(())
    }

    fn begin_generating_ibs(&mut self, slot: u64, count: u64) -> Result<()> {
        let mut unsent_ibs = VecDeque::new();
        for index in 0..count {
            let header = InputBlockHeader {
                slot,
                producer: self.id,
                index,
                timestamp: self.clock.now(),
            };
            unsent_ibs.push_back(InputBlock {
                header,
                transactions: vec![],
            });
        }
        self.leios.unsent_ibs.insert(slot, unsent_ibs);
        self.try_fill_ibs()
    }

    fn try_fill_ibs(&mut self) -> Result<()> {
        loop {
            let Some(mut first_ib_entry) = self.leios.unsent_ibs.first_entry() else {
                // we aren't sending any IBs
                return Ok(());
            };
            let slot = *first_ib_entry.key();
            let unsent_ibs = first_ib_entry.get_mut();
            let Some(unsent_ib) = unsent_ibs.front_mut() else {
                // we aren't sending any more IBs this round
                self.leios.unsent_ibs.remove(&slot);
                return Ok(());
            };
            let Some((_, tx)) = self.leios.mempool.first_key_value() else {
                // our mempool is empty
                return Ok(());
            };

            let remaining_capacity = self.max_ib_size - unsent_ib.bytes();
            let tx_bytes = tx.bytes;

            if remaining_capacity >= tx_bytes {
                // This IB has room for another TX, add it in
                let (id, tx) = self.leios.mempool.pop_first().unwrap();
                self.leios.mempool.remove(&id);
                unsent_ib.transactions.push(tx);
            }

            if remaining_capacity <= tx_bytes {
                // This IB is full, :shipit:
                let ib = unsent_ibs.pop_front().unwrap();
                self.generate_ib(ib)?;
            }
        }
    }

    fn finish_generating_ibs(&mut self, slot: u64) -> Result<()> {
        let Some(unsent_ibs) = self.leios.unsent_ibs.remove(&slot) else {
            return Ok(());
        };
        for ib in unsent_ibs {
            if ib.transactions.is_empty() {
                continue;
            }
            self.generate_ib(ib)?;
        }
        Ok(())
    }

    fn generate_ib(&mut self, mut ib: InputBlock) -> Result<()> {
        ib.header.timestamp = self.clock.now();
        let ib = Arc::new(ib);

        self.tracker.track_ib_generated(ib.clone());

        let id = ib.header.id();
        self.leios.ibs.insert(id, ib);
        for peer in &self.peers {
            self.send_to(*peer, SimulationMessage::AnnounceIBHeader(id))?;
        }
        Ok(())
    }

    // Simulates the output of a VRF using this node's stake (if any).
    fn run_vrf(&self, rng: &mut ChaChaRng, success_rate: f64) -> Option<u64> {
        let target_vrf_stake = compute_target_vrf_stake(self.stake, self.total_stake, success_rate);
        let result = rng.gen_range(0..self.total_stake);
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

#[derive(Clone, Debug)]
enum SimulationEvent {
    NewSlot(u64),
    NewTransaction,
    NetworkMessage {
        from: NodeId,
        to: NodeId,
        msg: SimulationMessage,
    },
}

#[derive(Clone, Debug)]
enum SimulationMessage {
    // tx "propagation"
    AnnounceTx(TransactionId),
    RequestTx(TransactionId),
    Tx(Arc<Transaction>),
    // praos block propagation
    RollForward(u64),
    RequestBlock(u64),
    Block(Arc<Block>),
    // IB header propagation
    AnnounceIBHeader(InputBlockId),
    RequestIBHeader(InputBlockId),
    IBHeader(InputBlockHeader, bool /* has_body */),
    // IB transmission
    AnnounceIB(InputBlockId),
    RequestIB(InputBlockId),
    IB(Arc<InputBlock>),
}

impl HasBytesSize for SimulationMessage {
    fn bytes_size(&self) -> u64 {
        match self {
            Self::AnnounceTx(_) => 8,
            Self::RequestTx(_) => 8,
            Self::Tx(tx) => tx.bytes,

            Self::RollForward(_) => 8,
            Self::RequestBlock(_) => 8,
            Self::Block(block) => block.transactions.iter().map(|t| t.bytes).sum(),

            Self::AnnounceIBHeader(_) => 8,
            Self::RequestIBHeader(_) => 8,
            Self::IBHeader(_, _) => 32,

            Self::AnnounceIB(_) => 8,
            Self::RequestIB(_) => 8,
            Self::IB(ib) => ib.bytes(),
        }
    }
}
