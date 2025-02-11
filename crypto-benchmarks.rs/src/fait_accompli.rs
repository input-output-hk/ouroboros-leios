use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use std::cmp::max;
use std::collections::BTreeMap;

use crate::primitive::{Coin, CoinFraction, PoolKeyhash};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FaSortition {
    pub n_persistent: usize,
    pub n_nonpersistent: usize,
    pub persistent: Vec<(PoolKeyhash, CoinFraction)>,
    pub nonpersistent: BTreeMap<PoolKeyhash, CoinFraction>,
    pub rho: CoinFraction,
}

fn sort_stake(pools: &BTreeMap<PoolKeyhash, Coin>) -> (Vec<Ratio<BigInt>>, Vec<PoolKeyhash>) {
    let mut sp: Vec<(Ratio<BigInt>, &PoolKeyhash)> = pools
        .iter()
        .map(|(pool, coins)| (Ratio::from_integer(BigInt::from(*coins)), pool))
        .collect();
    sp.sort();
    sp.reverse();
    sp.into_iter().unzip()
}

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

pub fn fait_accompli(pools: &BTreeMap<PoolKeyhash, Coin>, n: usize) -> FaSortition {
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
