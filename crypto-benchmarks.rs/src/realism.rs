//! Realistic stake distribution for Cardano mainnet.

use pallas::ledger::primitives::Coin;
use quickcheck::{Arbitrary, Gen};
use rand::prelude::Distribution;
use rand::rngs::StdRng;
use rand::SeedableRng;
use statrs::distribution::ContinuousCDF;
use statrs::distribution::{Beta, Uniform};

/// Generate a realistic number of pools.
pub fn realistic_pool_count(g: &mut Gen) -> usize {
    usize::arbitrary(g) % 1500 + 1500
}

/// Generate a realistic total stake.
pub fn realistic_total_stake(g: &mut Gen) -> Coin {
    u64::arbitrary(g) % 30000000000000000 + 15000000000000000
}

/// Generate a realistic voter-count protocol parameter.
pub fn realistic_voters(g: &mut Gen, pools: usize) -> usize {
    pools * (usize::arbitrary(g) % 500 + 500) / 1000
}

/// Generate a realistic stake distribution.
/// 
/// The stake `total` is distributed among `n` pools according to a beta distribution with parameters `alpha` and `beta`.
pub(crate) fn realistic_stake_dist(
    g: &mut Gen,
    total: u64,
    n: usize,
    alpha: f64,
    beta: f64,
) -> Vec<Coin> {
    let rng = &mut StdRng::seed_from_u64(u64::arbitrary(g));
    let noise = Uniform::new(0.75, 1.25).unwrap();
    let curve = Beta::new(alpha, beta).unwrap();
    let cum: Vec<f64> = (0..n)
        .map(|i| curve.cdf((i as f64) / (total as f64)))
        .collect();
    let dif: Vec<f64> = (1..n)
        .map(|i| (cum[i] - cum[i - 1]) * noise.sample(rng))
        .collect();
    let scale: f64 = (total as f64) / dif.iter().sum::<f64>();
    dif.iter()
        .map(|coin| (scale * *coin).round() as Coin)
        .collect()
}
