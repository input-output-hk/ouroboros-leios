use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet, BinaryHeap, VecDeque},
    time::{Duration, Instant},
};

use anyhow::{bail, Context, Result};
use futures::{stream::FuturesUnordered, StreamExt};
use netsim_async::{EdgePolicy, HasBytesSize, Latency};
use rand::{thread_rng, Rng};
use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
use rand_distr::Distribution as _;
use tokio::{select, time};

use crate::{
    config::{PoolConfiguration, PoolId, SimConfiguration},
    events::{Block, EventTracker, Transaction},
    network::{Network, NetworkSink, NetworkSource},
    probability::FloatDistribution,
};

pub struct Simulation {
    rng: ChaChaRng,
    network: Network<SimulationMessage>,
    pools: BTreeMap<PoolId, Pool>,
    msg_sources: BTreeMap<PoolId, NetworkSource<SimulationMessage>>,
    max_block_size: u64,
    max_tx_size: u64,
    next_slot: u64,
    next_tx_id: u64,
    transaction_frequency_ms: FloatDistribution,
    transaction_size_bytes: FloatDistribution,
    event_queue: BinaryHeap<FutureEvent>,
    unpublished_txs: VecDeque<Transaction>,
}

impl Simulation {
    pub fn new(config: SimConfiguration) -> Result<Self> {
        let total_stake = config.pools.iter().map(|p| p.stake).sum();

        let mut network = Network::new();

        let rng = ChaChaRng::from_rng(thread_rng()).context("couldn't initialize RNG")?;
        let mut pools = BTreeMap::new();
        let mut msg_sources = BTreeMap::new();
        for pool_config in &config.pools {
            let id = pool_config.id;
            let (msg_source, msg_sink) = network.open(id).context("could not open socket")?;
            let pool = Pool::new(pool_config, &config, total_stake, msg_sink);
            msg_sources.insert(pool.id, msg_source);
            pools.insert(pool.id, pool);
        }
        for link_config in config.links {
            network.set_edge_policy(
                link_config.pools[0],
                link_config.pools[1],
                EdgePolicy {
                    latency: Latency::new(link_config.latency),
                    ..EdgePolicy::default()
                },
            )?;
        }

        let mut sim = Self {
            rng,
            network,
            pools,
            msg_sources,
            max_block_size: config.max_block_size,
            max_tx_size: config.max_tx_size,
            transaction_frequency_ms: config.transaction_frequency_ms,
            transaction_size_bytes: config.transaction_size_bytes,
            next_slot: 0,
            next_tx_id: 0,
            event_queue: BinaryHeap::new(),
            unpublished_txs: VecDeque::new(),
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
                SimulationEvent::NewTransaction => self.generate_tx(&tracker),
                SimulationEvent::NetworkMessage { from, to, msg } => {
                    let Some(target) = self.pools.get_mut(&to) else {
                        bail!("unrecognized message target {to}");
                    };
                    match msg {
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
            .push(FutureEvent(Instant::now() + after, event));
    }

    async fn next_event(&mut self) -> Option<SimulationEvent> {
        let queued_event = self.event_queue.peek().cloned();

        let next_queued_event = async move {
            let FutureEvent(instant, event) = queued_event?;
            time::sleep_until(instant.into()).await;
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
            Some(event) = next_queued_event => {
                self.event_queue.pop();
                Some(event)
            }
            Some(Some(event)) = next_incoming_message.next() => Some(event),
            else => None
        }
    }

    fn run_slot_lottery(&mut self, tracker: &EventTracker) -> Result<()> {
        let vrf_winners: Vec<(PoolId, u64)> = self
            .pools
            .values()
            .filter_map(|pool| {
                let result = pool.run_vrf(&mut self.rng)?;
                Some((pool.id, result))
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
                if size + tx.bytes > self.max_block_size {
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
            self.pools
                .get_mut(&publisher)
                .unwrap()
                .publish_block(&block)?;
            tracker.track_slot(self.next_slot, Some(block));
        } else {
            tracker.track_slot(self.next_slot, None);
        }

        self.next_slot += 1;
        self.queue_event(SimulationEvent::NewSlot, Duration::from_secs(1));
        Ok(())
    }

    fn generate_tx(&mut self, tracker: &EventTracker) {
        let id = self.next_tx_id;
        let bytes = self
            .max_tx_size
            .min(self.transaction_size_bytes.sample(&mut self.rng) as u64);
        let tx = Transaction { id, bytes };

        tracker.track_transaction(&tx);
        self.unpublished_txs.push_back(tx);

        self.next_tx_id += 1;
        let ms_until_tx = self.transaction_frequency_ms.sample(&mut self.rng) as u64;
        self.queue_event(
            SimulationEvent::NewTransaction,
            Duration::from_millis(ms_until_tx),
        );
    }
}

struct Pool {
    id: PoolId,
    msg_sink: NetworkSink<SimulationMessage>,
    target_vrf_stake: u64,
    total_stake: u64,
    peers: Vec<PoolId>,
    blocks_sent_to_peers: BTreeSet<(PoolId, u64)>,
}

impl Pool {
    fn new(
        config: &PoolConfiguration,
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
            blocks_sent_to_peers: BTreeSet::new(),
        }
    }

    fn publish_block(&mut self, block: &Block) -> Result<()> {
        for peer in &self.peers {
            if self.blocks_sent_to_peers.insert((*peer, block.slot)) {
                self.msg_sink
                    .send_to(*peer, SimulationMessage::Block(block.clone()))?
            }
        }
        Ok(())
    }

    fn receive_block(&mut self, from: PoolId, block: Block) -> Result<()> {
        self.blocks_sent_to_peers.insert((from, block.slot));
        self.publish_block(&block)
    }

    // Simulates the output of a VRF using this pool's stake.
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
struct FutureEvent(Instant, SimulationEvent);
impl FutureEvent {
    fn key(&self) -> Reverse<Instant> {
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
        from: PoolId,
        to: PoolId,
        msg: SimulationMessage,
    },
}

#[derive(Clone)]
enum SimulationMessage {
    Block(Block),
}

impl HasBytesSize for SimulationMessage {
    fn bytes_size(&self) -> u64 {
        match self {
            Self::Block(block) => block.transactions.iter().map(|t| t.bytes).sum(),
        }
    }
}
