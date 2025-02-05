use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{One, Zero};
use std::cmp::max;
use std::collections::BTreeMap;

use crate::primitive::{Coin, PoolKeyhash};

fn sort_stake(
    pools: &BTreeMap<PoolKeyhash, Coin>,
    total: Coin,
) -> (Vec<Ratio<BigInt>>, Vec<PoolKeyhash>) {
    let stake = BigInt::from(total);
    let mut sp: Vec<(Ratio<BigInt>, &PoolKeyhash)> = pools
        .into_iter()
        .map(|(pool, coins)| (Ratio::new(BigInt::from(*coins), stake.clone()), pool))
        .collect();
    sp.sort();
    sp.reverse();
    sp.into_iter().unzip()
}

fn sum_stake(s: &Vec<Ratio<BigInt>>) -> Vec<Ratio<BigInt>> {
    let zero: Ratio<BigInt> = Ratio::new(BigInt::zero(), BigInt::one());
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

#[derive(Debug)]
pub struct FaSortition {
    pub n_persistent: usize,
    pub n_nonpersistent: usize,
    pub persistent: Vec<(PoolKeyhash, Ratio<BigInt>)>,
    pub nonpersistent: BTreeMap<PoolKeyhash, Ratio<BigInt>>,
    pub rho: Ratio<BigInt>,
}

fn fa_test(s: &Vec<Ratio<BigInt>>, rho: &Vec<Ratio<BigInt>>, n: usize, i: usize) -> bool {
    let one: Ratio<BigInt> = Ratio::new(BigInt::one(), BigInt::one());
    let x = one - s[i - 1].clone() / rho[i - 1].clone();
    x.clone() * x >= Ratio::new(BigInt::from(n - i), BigInt::from(n - i + 1))
}

pub fn fait_accompli(pools: &BTreeMap<PoolKeyhash, Coin>, n: usize) -> FaSortition {
    let stake: Coin = pools.values().sum();
    let (s, p): (Vec<Ratio<BigInt>>, Vec<PoolKeyhash>) = sort_stake(pools, stake);
    let rho: Vec<Ratio<BigInt>> = sum_stake(&s);
    let mut i_star: usize = 0;
    while fa_test(&s, &rho, n, i_star + 1) {
        i_star = i_star + 1
    }
    let rho_star = &rho[i_star];
    let n_persistent = max(1, i_star) - 1;
    let (pp, pnp) = p.split_at(n_persistent);
    FaSortition {
        persistent: pp
            .into_iter()
            .map(|pool| (*pool, Ratio::new(BigInt::from(pools[&pool]), BigInt::one())))
            .collect(),
        nonpersistent: pnp
            .into_iter()
            .map(|pool| {
                (
                    *pool,
                    Ratio::new(BigInt::from(pools[&pool]), BigInt::one()) / rho_star,
                )
            })
            .collect(),
        rho: rho_star.clone(),
        n_persistent,
        n_nonpersistent: n - n_persistent,
    }
}
