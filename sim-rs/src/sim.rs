use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque},
    sync::Arc,
    time::Duration,
};

use anyhow::{bail, Context, Result};
use futures::{stream::FuturesUnordered, StreamExt};
use netsim_async::{EdgePolicy, HasBytesSize, Latency};
use rand::Rng as _;
use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
use rand_distr::Distribution as _;
use tokio::select;

use crate::{
    clock::{Clock, Timestamp},
    config::{NodeConfiguration, NodeId, SimConfiguration},
    events::{Block, EventTracker, Transaction, TransactionId},
    network::{Network, NetworkSink, NetworkSource},
};

pub struct Simulation {
    config: SimConfiguration,
    clock: Clock,
    rng: ChaChaRng,
    network: Network<SimulationMessage>,
    nodes: BTreeMap<NodeId, Node>,
    msg_sources: BTreeMap<NodeId, NetworkSource<SimulationMessage>>,
    next_slot: u64,
    next_tx_id: u64,
    event_queue: BinaryHeap<FutureEvent>,
    unpublished_txs: VecDeque<Arc<Transaction>>,
    txs: BTreeMap<TransactionId, Arc<Transaction>>,
}

impl Simulation {
    pub fn new(config: SimConfiguration, clock: Clock) -> Result<Self> {
        let total_stake = config.nodes.iter().map(|p| p.stake).sum();

        let mut network = Network::new();

        let rng = ChaChaRng::seed_from_u64(config.seed);
        let mut nodes = BTreeMap::new();
        let mut msg_sources = BTreeMap::new();
        for node_config in &config.nodes {
            let id = node_config.id;
            let (msg_source, msg_sink) = network.open(id).context("could not open socket")?;
            let node = Node::new(node_config, &config, total_stake, msg_sink);
            msg_sources.insert(node.id, msg_source);
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

        let mut sim = Self {
            config,
            clock,
            rng,
            network,
            nodes,
            msg_sources,
            next_slot: 0,
            next_tx_id: 0,
            event_queue: BinaryHeap::new(),
            unpublished_txs: VecDeque::new(),
            txs: BTreeMap::new(),
        };
        sim.queue_event(SimulationEvent::NewSlot, Duration::ZERO);
        sim.queue_event(SimulationEvent::NewTransaction, Duration::ZERO);

        Ok(sim)
    }

    // Run the simulation indefinitely.
    pub async fn run(&mut self, tracker: EventTracker) -> Result<()> {
        while let Some(event) = self.next_event().await {
            match event {
                SimulationEvent::NewSlot => self.run_slot_lottery(&tracker)?,
                SimulationEvent::NewTransaction => self.generate_tx(&tracker)?,
                SimulationEvent::NetworkMessage { from, to, msg } => {
                    let Some(target) = self.nodes.get_mut(&to) else {
                        bail!("unrecognized message target {to}");
                    };
                    match msg {
                        SimulationMessage::AnnounceTx(id) => {
                            target.receive_announce_tx(from, id)?;
                        }
                        SimulationMessage::RequestTx(id) => {
                            let tx = self.txs.get(&id).expect("unexpected missing tx").clone();
                            target.receive_request_tx(from, tx)?;
                        }
                        SimulationMessage::Tx(tx) => {
                            target.receive_tx(from, tx)?;
                        }
                        SimulationMessage::RollForward(slot) => {
                            target.receive_roll_forward(from, slot)?;
                        }
                        SimulationMessage::RequestBlock(slot) => {
                            target.receive_request_block(from, slot)?;
                        }
                        SimulationMessage::Block(block) => {
                            tracker.track_block_received(block.slot, from, to);
                            target.receive_block(from, block)?;
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

    fn queue_event(&mut self, event: SimulationEvent, after: Duration) {
        self.event_queue
            .push(FutureEvent(self.clock.now() + after, event));
    }

    async fn next_event(&mut self) -> Option<SimulationEvent> {
        let queued_event = self.event_queue.peek().cloned();

        let clock = self.clock.clone();
        let next_queued_event = async move {
            let FutureEvent(timestamp, event) = queued_event?;
            clock.wait_until(timestamp).await;
            Some(event)
        };

        let mut next_incoming_message = FuturesUnordered::new();
        for (id, source) in self.msg_sources.iter_mut() {
            next_incoming_message.push(async move {
                let (from, msg) = source.recv().await?;
                Some(SimulationEvent::NetworkMessage { from, to: *id, msg })
            });
        }

        select! {
            biased; // always poll the "next queued event" future first
            Some(event) = next_queued_event => {
                self.event_queue.pop();
                Some(event)
            }
            Some(Some(event)) = next_incoming_message.next() => Some(event),
            else => None
        }
    }

    fn run_slot_lottery(&mut self, tracker: &EventTracker) -> Result<()> {
        let vrf_winners: Vec<(NodeId, u64)> = self
            .nodes
            .values()
            .filter_map(|node| {
                let result = node.run_vrf(&mut self.rng)?;
                Some((node.id, result))
            })
            .collect();

        let winner = vrf_winners
            .iter()
            .max_by_key(|(_, result)| *result)
            .map(|(id, _)| *id);

        if let Some(publisher) = winner {
            let conflicts = vrf_winners
                .into_iter()
                .filter_map(|(id, _)| if publisher != id { Some(id) } else { None })
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
                slot: self.next_slot,
                publisher,
                conflicts,
                transactions,
            };
            self.nodes
                .get_mut(&publisher)
                .unwrap()
                .publish_block(Arc::new(block.clone()))?;
            tracker.track_slot(self.next_slot, Some(block));
        } else {
            tracker.track_slot(self.next_slot, None);
        }

        self.next_slot += 1;
        self.queue_event(SimulationEvent::NewSlot, Duration::from_secs(1));
        Ok(())
    }

    fn generate_tx(&mut self, tracker: &EventTracker) -> Result<()> {
        let id = TransactionId::new(self.next_tx_id);
        let bytes = self
            .config
            .max_tx_size
            .min(self.config.transaction_size_bytes.sample(&mut self.rng) as u64);
        let tx = Arc::new(Transaction { id, bytes });

        tracker.track_transaction(&tx);
        self.unpublished_txs.push_back(tx.clone());
        self.txs.insert(id, tx);

        self.next_tx_id += 1;
        let ms_until_tx = self.config.transaction_frequency_ms.sample(&mut self.rng) as u64;
        self.queue_event(
            SimulationEvent::NewTransaction,
            Duration::from_millis(ms_until_tx),
        );

        // any node could be the first to see a transaction
        let publisher_id = self.choose_random_node();
        let publisher = self
            .nodes
            .get_mut(&publisher_id)
            .expect("chose nonexistent node");
        publisher.propagate_tx(id)
    }

    fn choose_random_node(&mut self) -> NodeId {
        let index = self.rng.gen_range(0..self.nodes.len());
        NodeId::from_usize(index)
    }
}

struct Node {
    id: NodeId,
    msg_sink: NetworkSink<SimulationMessage>,
    target_vrf_stake: u64,
    total_stake: u64,
    peers: Vec<NodeId>,
    peer_heads: BTreeMap<NodeId, u64>,
    blocks_seen: BTreeSet<u64>,
    blocks: BTreeMap<u64, Arc<Block>>,
    txs_seen: BTreeSet<TransactionId>,
}

impl Node {
    fn new(
        config: &NodeConfiguration,
        sim_config: &SimConfiguration,
        total_stake: u64,
        msg_sink: NetworkSink<SimulationMessage>,
    ) -> Self {
        let id = config.id;
        let target_vrf_stake = compute_target_vrf_stake(
            config.stake,
            total_stake,
            sim_config.block_generation_probability,
        );
        let peers = config.peers.clone();
        Self {
            id,
            msg_sink,
            target_vrf_stake,
            total_stake,
            peers,
            peer_heads: BTreeMap::new(),
            blocks_seen: BTreeSet::new(),
            blocks: BTreeMap::new(),
            txs_seen: BTreeSet::new(),
        }
    }

    fn propagate_tx(&mut self, id: TransactionId) -> Result<()> {
        for peer in &self.peers {
            self.msg_sink
                .send_to(*peer, SimulationMessage::AnnounceTx(id))?;
        }
        Ok(())
    }

    fn publish_block(&mut self, block: Arc<Block>) -> Result<()> {
        for peer in &self.peers {
            if !self.peer_heads.get(peer).is_some_and(|&s| s >= block.slot) {
                self.msg_sink
                    .send_to(*peer, SimulationMessage::RollForward(block.slot))?;
                self.peer_heads.insert(*peer, block.slot);
            }
        }
        self.blocks.insert(block.slot, block);
        Ok(())
    }

    fn receive_announce_tx(&mut self, from: NodeId, id: TransactionId) -> Result<()> {
        if self.txs_seen.insert(id) {
            self.msg_sink
                .send_to(from, SimulationMessage::RequestTx(id))?;
        }
        Ok(())
    }

    fn receive_request_tx(&mut self, from: NodeId, tx: Arc<Transaction>) -> Result<()> {
        self.msg_sink.send_to(from, SimulationMessage::Tx(tx))
    }

    fn receive_tx(&mut self, from: NodeId, tx: Arc<Transaction>) -> Result<()> {
        for peer in &self.peers {
            if *peer == from {
                continue;
            }
            self.msg_sink
                .send_to(*peer, SimulationMessage::AnnounceTx(tx.id))?;
        }
        Ok(())
    }

    fn receive_roll_forward(&mut self, from: NodeId, slot: u64) -> Result<()> {
        if self.blocks_seen.insert(slot) {
            self.msg_sink
                .send_to(from, SimulationMessage::RequestBlock(slot))?;
        }
        Ok(())
    }

    fn receive_request_block(&mut self, from: NodeId, slot: u64) -> Result<()> {
        if let Some(block) = self.blocks.get(&slot) {
            self.msg_sink
                .send_to(from, SimulationMessage::Block(block.clone()))?;
        }
        Ok(())
    }

    fn receive_block(&mut self, from: NodeId, block: Arc<Block>) -> Result<()> {
        if self.blocks.insert(block.slot, block.clone()).is_none() {
            let head = self.peer_heads.entry(from).or_default();
            if *head < block.slot {
                *head = block.slot
            }
            self.publish_block(block)?;
        }
        Ok(())
    }

    // Simulates the output of a VRF using this node's stake (if any).
    fn run_vrf(&self, rng: &mut ChaChaRng) -> Option<u64> {
        let result = rng.gen_range(0..self.total_stake);
        if result < self.target_vrf_stake {
            Some(result)
        } else {
            None
        }
    }
}

fn compute_target_vrf_stake(
    stake: u64,
    total_stake: u64,
    block_generation_probability: f64,
) -> u64 {
    let ratio = stake as f64 / total_stake as f64;
    let p_success = 1. - (1. - block_generation_probability).powf(ratio);
    (total_stake as f64 * p_success) as u64
}

// wrapper struct which holds a SimulationEvent,
// but is ordered by a timestamp (in reverse)
#[derive(Clone)]
struct FutureEvent(Timestamp, SimulationEvent);
impl FutureEvent {
    fn key(&self) -> Reverse<Timestamp> {
        Reverse(self.0)
    }
}

impl PartialEq for FutureEvent {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}
impl Eq for FutureEvent {}
impl PartialOrd for FutureEvent {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for FutureEvent {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

#[derive(Clone)]
enum SimulationEvent {
    NewSlot,
    NewTransaction,
    NetworkMessage {
        from: NodeId,
        to: NodeId,
        msg: SimulationMessage,
    },
}

#[derive(Clone)]
enum SimulationMessage {
    AnnounceTx(TransactionId),
    RequestTx(TransactionId),
    Tx(Arc<Transaction>),
    RollForward(u64),
    RequestBlock(u64),
    Block(Arc<Block>),
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
        }
    }
}
