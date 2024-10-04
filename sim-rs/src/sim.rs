use std::{
    cmp::Reverse,
    collections::{BinaryHeap, VecDeque},
    time::{Duration, Instant},
};

use rand::{thread_rng, Rng};
use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
use rand_distr::Distribution as _;
use tokio::time;

use crate::{
    config::{PoolId, SimConfiguration},
    events::{Block, EventTracker, Transaction},
    probability::FloatDistribution,
};

pub struct Simulation {
    rng: ChaChaRng,
    pools: Vec<Pool>,
    total_stake: u64,
    max_block_size: u64,
    max_tx_size: u64,
    next_slot: u64,
    next_tx_id: u64,
    transaction_frequency_ms: FloatDistribution,
    transaction_size_bytes: FloatDistribution,
    event_queue: BinaryHeap<Reverse<(Instant, SimulationEvent)>>,
    unpublished_txs: VecDeque<Transaction>,
}

impl Simulation {
    pub fn new(config: SimConfiguration) -> Self {
        let total_stake = config.pools.iter().map(|p| p.stake).sum();
        let block_generation_probability = config.block_generation_probability;

        let mut rng = ChaChaRng::from_rng(thread_rng()).expect("couldn't initialize RNG");
        let pools: Vec<Pool> = config
            .pools
            .into_iter()
            .map(|c| Pool {
                id: c.id,
                target_vrf_stake: compute_target_vrf_stake(
                    c.stake,
                    total_stake,
                    block_generation_probability,
                ),
                rng: ChaChaRng::from_rng(&mut rng).unwrap(),
            })
            .collect();

        let mut sim = Self {
            rng,
            pools,
            total_stake,
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

        sim
    }

    // Run the simulation indefinitely.
    pub async fn run(mut self, tracker: EventTracker) {
        while let Some(event) = self.next_event().await {
            match event {
                SimulationEvent::NewSlot => self.run_slot_lottery(&tracker),
                SimulationEvent::NewTransaction => self.generate_tx(&tracker),
            }
        }
    }

    fn queue_event(&mut self, event: SimulationEvent, after: Duration) {
        self.event_queue
            .push(Reverse((Instant::now() + after, event)));
    }

    async fn next_event(&mut self) -> Option<SimulationEvent> {
        let Reverse((instant, event)) = self.event_queue.pop()?;
        time::sleep_until(instant.into()).await;
        Some(event)
    }

    fn run_slot_lottery(&mut self, tracker: &EventTracker) {
        let vrf_winners: Vec<(PoolId, u64)> = self
            .pools
            .iter_mut()
            .filter_map(|pool| {
                let result = pool.run_vrf(self.total_stake)?;
                Some((pool.id, result))
            })
            .collect();

        let winner = vrf_winners
            .iter()
            .max_by_key(|(_, result)| result)
            .map(|(id, _)| *id);

        let block = winner.map(|publisher| {
            let conflicts = vrf_winners
                .into_iter()
                .filter_map(|(id, _)| if publisher != id { Some(id) } else { None })
                .collect();

            let mut size = 0;
            let mut transactions = vec![];
            while let Some(tx) = self.unpublished_txs.front() {
                if size + tx.bytes > self.max_block_size {
                    break;
                }
                size += tx.bytes;
                transactions.push(self.unpublished_txs.pop_front().unwrap());
            }

            Block {
                publisher,
                conflicts,
                transactions,
            }
        });

        tracker.track_slot(self.next_slot, block);

        self.next_slot += 1;
        self.queue_event(SimulationEvent::NewSlot, Duration::from_secs(1));
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
    target_vrf_stake: u64,
    rng: ChaChaRng,
}

impl Pool {
    // Simulates the output of a VRF using this pool's stake.
    fn run_vrf(&mut self, total_stake: u64) -> Option<u64> {
        let result = self.rng.gen_range(0..total_stake);
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

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum SimulationEvent {
    NewSlot,
    NewTransaction,
}
