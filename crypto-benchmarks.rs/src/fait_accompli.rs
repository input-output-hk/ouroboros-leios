use num_rational::Ratio;
use pallas::ledger::primitives::{Coin, PoolKeyhash};
use std::collections::BTreeMap;

fn sort_stake(pools: &BTreeMap<PoolKeyhash, Coin>, total: Coin) -> (Vec<Ratio<Coin>>, Vec<PoolKeyhash>) {
  let mut sp : Vec<(Ratio<Coin>, &PoolKeyhash)> =
    pools.into_iter()
      .map(|x| (Ratio::<Coin>::new(*x.1, total), x.0))
      .collect();
  sp.sort();
  sp.reverse();
  sp.into_iter().unzip()
}

fn sum_stake(s: &Vec<Ratio<Coin>>) -> Vec<Ratio<Coin>> {
  let (mut rho, _) : (Vec<Ratio<Coin>>, Ratio<Coin>) =
    s.iter()
     .rev()
     .fold((Vec::new(), Ratio::ZERO), |(mut acc, x), &stake| {
        let y = x + stake;
        acc.push(y);
        (acc, y)
      });
  rho.reverse();
  rho
}

pub struct FaSortition {
  pub n_persistent: usize,
  pub n_nonpersistent: usize,
  pub persistent: Vec<(PoolKeyhash, Ratio<Coin>)>, 
  pub nonpersistent: BTreeMap<PoolKeyhash, Ratio<Coin>>,
  pub rho: Ratio<Coin>,
}

pub fn fait_accompli(pools: &BTreeMap<PoolKeyhash, Coin>, n: usize) -> FaSortition {
  let stake: Coin = pools.values().sum();
  let (s, p): (Vec<Ratio<Coin>>, Vec<PoolKeyhash>) = sort_stake(pools, stake);
  let rho: Vec<Ratio<Coin>> = sum_stake(&s);
  let test = |i: usize| {
    let x = Ratio::ONE - s[i-1] / rho[i-1];
    x * x >= Ratio::new((n - i) as u64, (n - i + 1) as u64)
  };
  let mut i_star: usize = 0;
  while test(i_star + 1) {i_star = i_star + 1};
  let rho_star = rho[i_star];
  let n_persistent = i_star - 1;
  let (pp, pnp) = p.split_at(n_persistent);
  FaSortition {
    persistent: pp.into_iter().map(|pool| (*pool, Ratio::new(pools[&pool], 1))).collect(),
    nonpersistent: pnp.into_iter().map(|pool| (*pool, Ratio::new(pools[&pool], 1) / rho_star)).collect(),
    rho: rho_star,
    n_persistent,
    n_nonpersistent: n - n_persistent,
  }
}