use std::{collections::VecDeque, sync::Arc};

use dashmap::DashMap;
use rand::Rng;
use rand_chacha::ChaChaRng;

pub fn compute_target_vrf_stake(stake: u64, total_stake: u64, success_rate: f64) -> u64 {
    let ratio = stake as f64 / total_stake as f64;
    (total_stake as f64 * ratio * success_rate) as u64
}

pub fn vrf_probabilities(probability: f64) -> impl Iterator<Item = f64> {
    let final_success_rate = Some(probability.fract()).filter(|f| *f > 0.0);
    std::iter::repeat_n(1.0, probability.trunc() as usize).chain(final_success_rate)
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum LotteryKind {
    GenerateRB,
    GenerateVote,
}

#[derive(Default)]
pub struct MockLotteryResults {
    results: DashMap<LotteryKind, VecDeque<u64>>,
}
impl MockLotteryResults {
    pub fn run(&self, kind: LotteryKind) -> Option<u64> {
        self.results.entry(kind).or_default().pop_front()
    }
    #[allow(unused)]
    pub fn configure_win(&self, kind: LotteryKind, result: u64) {
        self.results.entry(kind).or_default().push_back(result);
    }
}

pub enum LotteryConfig {
    Random {
        stake: u64,
        total_stake: u64,
    },
    #[allow(unused)]
    Mock {
        results: Arc<MockLotteryResults>,
    },
}

impl LotteryConfig {
    pub fn run(&self, kind: LotteryKind, success_rate: f64, rng: &mut ChaChaRng) -> Option<u64> {
        match self {
            Self::Random { stake, total_stake } => {
                let target_vrf_stake = compute_target_vrf_stake(*stake, *total_stake, success_rate);
                let result = rng.random_range(0..*total_stake);
                if result < target_vrf_stake {
                    Some(result)
                } else {
                    None
                }
            }
            Self::Mock { results } => results.run(kind),
        }
    }
}
