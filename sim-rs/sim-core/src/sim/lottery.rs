use std::{collections::VecDeque, sync::Arc};

use dashmap::DashMap;

use crate::{
    config::NodeId,
    rng::{DrawSite, Rng},
};

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
    /// Run one lottery trial. For `Random`, the outcome is a pure function
    /// of `(rng.global_seed, node, slot, site)`: a VRF-style draw. For
    /// `Mock`, the pre-configured queue for `kind` is popped and the
    /// context is ignored (tests are already deterministic by construction).
    pub fn run(
        &self,
        kind: LotteryKind,
        success_rate: f64,
        rng: &Rng,
        node: NodeId,
        slot: u64,
        site: DrawSite,
    ) -> Option<u64> {
        match self {
            Self::Random { stake, total_stake } => {
                let target_vrf_stake = compute_target_vrf_stake(*stake, *total_stake, success_rate);
                let result = rng.draw_range(node, slot, site, *total_stake);
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
