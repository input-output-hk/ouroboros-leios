//! Fait Accompli operations.

use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use std::cmp::max;
use std::collections::BTreeMap;

use crate::primitive::{Coin, CoinFraction, PoolKeyhash};

/// Fait Accompli sortition results in a committee of persistent and non-persistent voters.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FaSortition {
    /// Number of persistent voters.
    pub n_persistent: usize,
    /// Number of non-persistent voters.
    pub n_nonpersistent: usize,
    /// Stake held by persistent voters.
    pub persistent: Vec<(PoolKeyhash, CoinFraction)>,
    /// State held by non-persistent voters.
    pub nonpersistent: BTreeMap<PoolKeyhash, CoinFraction>,
    /// Stake cutoff for persistent vs non-persistent voters.
    pub rho: CoinFraction,
}

impl FaSortition {
    /// Perform Fait Accompli sortiion on the stake distribution `pools` and target committee size `n`.
    pub fn fait_accompli(pools: &BTreeMap<PoolKeyhash, Coin>, n: usize) -> Self {
        let zero: Ratio<BigInt> = Ratio::from_integer(BigInt::zero());
        let (s, p): (Vec<Ratio<BigInt>>, Vec<PoolKeyhash>) = sort_stake(pools);
        let rho: Vec<Ratio<BigInt>> = sum_stake(&s);
        let mut i_star: usize = 1;
        while !fa_test(&s, &rho, n, i_star) {
            i_star += 1
        }
        let rho_star = &rho[i_star - 1];
        let n_persistent = max(1, i_star) - 1;
        let (pp, pnp) = p.split_at(n_persistent);
        FaSortition {
            persistent: pp
                .iter()
                .map(|pool| {
                    (
                        *pool,
                        CoinFraction(Ratio::from_integer(BigInt::from(pools[pool]))),
                    )
                })
                .collect(),
            nonpersistent: if *rho_star > zero {
                pnp.iter()
                    .map(|pool| {
                        (
                            *pool,
                            CoinFraction(Ratio::from_integer(BigInt::from(pools[pool])) / rho_star),
                        )
                    })
                    .collect()
            } else {
                BTreeMap::new()
            },
            rho: CoinFraction(rho_star.clone()),
            n_persistent,
            n_nonpersistent: n - n_persistent,
        }
    }
}

/// Sort stake pools in order of decreasing stake.
fn sort_stake(pools: &BTreeMap<PoolKeyhash, Coin>) -> (Vec<Ratio<BigInt>>, Vec<PoolKeyhash>) {
    let mut sp: Vec<(Ratio<BigInt>, &PoolKeyhash)> = pools
        .iter()
        .map(|(pool, coins)| (Ratio::from_integer(BigInt::from(*coins)), pool))
        .collect();
    sp.sort();
    sp.reverse();
    sp.into_iter().unzip()
}

/// Sum stake fractions.
fn sum_stake(s: &[Ratio<BigInt>]) -> Vec<Ratio<BigInt>> {
    let zero: Ratio<BigInt> = Ratio::from_integer(BigInt::zero());
    let (mut rho, _): (Vec<Ratio<BigInt>>, Ratio<BigInt>) =
        s.iter()
            .rev()
            .fold((Vec::new(), zero), |(mut acc, x), stake| {
                let y = x + stake;
                acc.push(y.clone());
                (acc, y)
            });
    rho.reverse();
    rho
}

/// Perform the Fait Accompli test that check whether there are any more persistent pools to be selected.
fn fa_test(s: &[Ratio<BigInt>], rho: &[Ratio<BigInt>], n: usize, i: usize) -> bool {
    let zero: Ratio<BigInt> = Ratio::from_integer(BigInt::zero());
    let one: Ratio<BigInt> = Ratio::from_integer(BigInt::one());
    if rho[i - 1] == zero {
        true
    } else {
        let x = one - s[i - 1].clone() / rho[i - 1].clone();
        x.clone() * x >= Ratio::new(BigInt::from(n - i), BigInt::from(n - i + 1))
    }
}
