use std::{collections::HashMap, sync::Arc, time::Duration};

use anyhow::{Context, Result};
use event_queue::EventQueue;
use netsim_async::{Bandwidth, EdgePolicy, HasBytesSize, Latency};
use node::Node;
use rand::{Rng as _, RngCore};
use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
use rand_distr::Distribution as _;
use tokio::{
    select,
    sync::{mpsc, watch},
    task::JoinSet,
};
use tokio_util::sync::CancellationToken;
use tracing::{debug, warn};

use crate::{
    clock::Clock,
    config::{NodeId, SimConfiguration},
    events::EventTracker,
    model::{Block, InputBlock, InputBlockHeader, InputBlockId, Transaction, TransactionId},
    network::Network,
};

mod event_queue;
mod node;

pub struct Simulation {
    config: Arc<SimConfiguration>,
    tracker: EventTracker,
    rng: ChaChaRng,
    network: Network<SimulationMessage>,
    event_queue: EventQueue,
    nodes: Vec<Node>,
    slot_broadcaster: watch::Sender<u64>,
    tx_sinks: HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>,
    next_tx_id: u64,
}

impl Simulation {
    pub fn new(config: SimConfiguration, tracker: EventTracker, clock: Clock) -> Result<Self> {
        let config = Arc::new(config);
        let total_stake = config.nodes.iter().map(|p| p.stake).sum();

        let mut network = Network::new(config.timescale);
        let slot_broadcaster = watch::Sender::new(0);

        let mut rng = ChaChaRng::seed_from_u64(config.seed);
        let mut nodes = vec![];
        let mut tx_sinks = HashMap::new();
        for node_config in &config.nodes {
            let id = node_config.id;
            let (msg_source, msg_sink) = network.open(id).context("could not open socket")?;
            let (tx_sink, tx_source) = mpsc::unbounded_channel();
            tx_sinks.insert(id, tx_sink);
            let node = Node::new(
                node_config,
                config.clone(),
                total_stake,
                msg_source,
                msg_sink,
                slot_broadcaster.subscribe(),
                tx_source,
                tracker.clone(),
                ChaChaRng::seed_from_u64(rng.next_u64()),
                clock.clone(),
            );
            nodes.push(node);
        }
        for link_config in config.links.iter() {
            network.set_edge_policy(
                link_config.nodes.0,
                link_config.nodes.1,
                EdgePolicy {
                    latency: Latency::new(link_config.latency),
                    bandwidth_down: Bandwidth::bits_per(u64::MAX, Duration::from_millis(1)),
                    bandwidth_up: Bandwidth::bits_per(u64::MAX, Duration::from_millis(1)),
                    ..EdgePolicy::default()
                },
            )?;
        }

        let mut event_queue = EventQueue::new(clock);
        event_queue.queue_event(SimulationEvent::NewSlot(0), Duration::ZERO);
        event_queue.queue_event(SimulationEvent::NewTransaction, Duration::ZERO);
        Ok(Self {
            config,
            tracker,
            rng,
            network,
            event_queue,
            nodes,
            slot_broadcaster,
            tx_sinks,
            next_tx_id: 0,
        })
    }

    // Run the simulation indefinitely.
    pub async fn run(&mut self, token: CancellationToken) -> Result<()> {
        let mut set = JoinSet::new();
        let mut nodes = vec![];
        nodes.append(&mut self.nodes);

        for node in nodes {
            set.spawn(node.run());
        }
        let handle_events = async move {
            while let Some(event) = self.event_queue.next_event().await {
                match event {
                    SimulationEvent::NewSlot(slot) => {
                        let done = self.handle_new_slot(slot);
                        if done {
                            break;
                        }
                    }
                    SimulationEvent::NewTransaction => self.generate_tx(),
                }
            }
        };

        select! {
            biased;
            _ = token.cancelled() => {}
            _ = handle_events => {}
            results = set.join_all() => {
                for res in results {
                    res?;
                }
            }
        };

        Ok(())
    }

    pub fn shutdown(self) -> Result<()> {
        self.network.shutdown()
    }

    fn handle_new_slot(&mut self, slot: u64) -> bool {
        if self.config.slots.is_some_and(|s| slot == s) {
            // done running
            return true;
        }

        self.tracker.track_slot(slot);
        self.slot_broadcaster.send_replace(slot);
        self.event_queue
            .queue_event(SimulationEvent::NewSlot(slot + 1), Duration::from_secs(1));

        false
    }

    fn generate_tx(&mut self) {
        let id = TransactionId::new(self.next_tx_id);
        let shard = self.rng.gen_range(0..self.config.ib_shards);
        let bytes = self
            .config
            .max_tx_size
            .min(self.config.transaction_size_bytes.sample(&mut self.rng) as u64);
        let tx = Arc::new(Transaction { id, shard, bytes });

        // any node could be the first to see a transaction
        let publisher_id = self.choose_random_node();

        self.tracker.track_transaction_generated(&tx, publisher_id);
        if let Err(err) = self.tx_sinks.get(&publisher_id).unwrap().send(tx) {
            warn!(
                "node {} shut down before the sim completed: {err}",
                publisher_id
            );
        }

        self.next_tx_id += 1;
        let ms_until_tx = self.config.transaction_frequency_ms.sample(&mut self.rng) as u64;
        self.event_queue.queue_event(
            SimulationEvent::NewTransaction,
            Duration::from_millis(ms_until_tx),
        );

        debug!("node {publisher_id} generated tx {id}");
    }

    fn choose_random_node(&mut self) -> NodeId {
        let index = self.rng.gen_range(0..self.config.nodes.len());
        NodeId::new(index)
    }
}

#[derive(Clone, Debug)]
enum SimulationEvent {
    NewSlot(u64),
    NewTransaction,
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
