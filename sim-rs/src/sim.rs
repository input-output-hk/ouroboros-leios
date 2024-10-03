use std::time::Duration;

use rand::{thread_rng, Rng};
use rand_chacha::{rand_core::SeedableRng, ChaChaRng};
use tokio::time;

use crate::{
    config::{PoolId, SimConfiguration},
    events::EventTracker,
};

pub struct Simulation {
    pools: Vec<Pool>,
    vrf_max_score: u64,
    current_slot: u64,
}

impl Simulation {
    pub fn new(config: SimConfiguration) -> Self {
        let mut rng = ChaChaRng::from_rng(thread_rng()).expect("couldn't initialize RNG");
        let pools: Vec<Pool> = config
            .pools
            .into_iter()
            .map(|c| Pool {
                id: c.id,
                stake: c.stake,
                rng: ChaChaRng::from_rng(&mut rng).unwrap(),
            })
            .collect();
        Self {
            pools,
            vrf_max_score: config.vrf_max_score,
            current_slot: 0,
        }
    }

    // Run the simulation indefinitely.
    pub async fn run(mut self, tracker: EventTracker) {
        loop {
            self.run_slot_lottery(&tracker);
            time::sleep(Duration::from_secs(1)).await;
        }
    }

    fn run_slot_lottery(&mut self, tracker: &EventTracker) {
        let vrf_winners: Vec<(PoolId, u64)> = self
            .pools
            .iter_mut()
            .filter_map(|pool| {
                let result = pool.run_vrf(self.vrf_max_score)?;
                Some((pool.id, result))
            })
            .collect();

        let publisher = vrf_winners
            .iter()
            .max_by_key(|(_, result)| result)
            .map(|(id, _)| *id);
        let conflicts = vrf_winners
            .into_iter()
            .filter_map(|(id, _)| {
                if publisher != Some(id) {
                    Some(id)
                } else {
                    None
                }
            })
            .collect();
        tracker.track_slot(self.current_slot, publisher, conflicts);
        self.current_slot += 1;
    }
}

struct Pool {
    id: PoolId,
    stake: u64,
    rng: ChaChaRng,
}

impl Pool {
    // Simulates the output of a VRF using this pool's stake.
    fn run_vrf(&mut self, max_score: u64) -> Option<u64> {
        let result = self.rng.gen_range(0..max_score);
        if result < self.stake {
            Some(result)
        } else {
            None
        }
    }
}
