use quickcheck::{Arbitrary, Gen};
use rand::prelude::Distribution;
use rand::SeedableRng;
use rand::rngs::StdRng;
use statrs::distribution::Beta;
use std::collections::HashMap;

use crate::cert::*;
use crate::key::*;
use crate::primitive::*;
use crate::registry::*;


pub fn realistic_stake_default(g: &mut Gen) -> HashMap<PoolKeyhash, Coin> {
  realistic_stake(g, 45000000000000000, 2500)
}

pub fn realistic_stake(g: &mut Gen, total: u64, n: usize) -> HashMap<PoolKeyhash, Coin> {
  HashMap::from_iter(
    realistic_stake_dist(g, total, n)
      .iter()
      .map(|coin| (arbitrary_poolkeyhash(g), *coin))
  )
}

fn realistic_stake_dist(g: &mut Gen, total: u64, n: usize) -> Vec<Coin> {

  let dist = Beta::new(11f64, 1f64).unwrap();
  let rng = &mut StdRng::seed_from_u64(u64::arbitrary(g));

  let mut raw: Vec<f64> = (0..n).map(|_| dist.sample(rng)).collect();
  raw.sort_by(|x, y| x.partial_cmp(y).unwrap());
  let (cum, _) =
    raw
      .iter()
      .fold((Vec::new(), 0f64), |(mut acc, stake), delta| {
        let new_stake = stake + delta;
        acc.push(stake.clone());
        (acc, new_stake)
      });
  let scale: f64 = (total as f64) / cum.iter().sum::<f64>();

  cum.iter().map(|coin| (scale * *coin).round() as Coin).collect()

}

pub fn realistic_pools(g: &mut Gen, total: u64, n: usize) -> Vec<PoolInfo> {
  realistic_stake(g, total, n)
    .iter()
    .map(|(pool, coin)| PoolInfo{reg: Reg{pool: *pool, ..Reg::arbitrary(g)}, stake: *coin})
    .collect()
}

/*
pub fn realistic_cert(g: &mut Gen) -> Cert {

  let eid = Eid::arbitrary(g);

  let ebhash = EbHash::arbitrary(g);



}
*/