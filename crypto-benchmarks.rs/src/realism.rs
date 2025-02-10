use quickcheck::{Arbitrary, Gen};
use rand::prelude::Distribution;
use rand::rngs::StdRng;
use rand::SeedableRng;
use statrs::distribution::{Beta, Uniform};
use statrs::distribution::ContinuousCDF;
use std::collections::HashMap;

use crate::cert::*;
use crate::fait_accompli::fait_accompli;
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
  let rng = &mut StdRng::seed_from_u64(u64::arbitrary(g));
  let noise = Uniform::new(0.75, 1.25).unwrap();
  let beta = Beta::new(11f64, 1f64).unwrap();
  let cum: Vec<f64> = (0..n).map(|i| beta.cdf((i as f64) / (total as f64))).collect();
  let dif: Vec<f64> = (1..n).map(|i| (cum[i] - cum[i-1]) * noise.sample(rng)).collect();
  let scale: f64 = (total as f64) / dif.iter().sum::<f64>();
  dif.iter().map(|coin| (scale * *coin).round() as Coin).collect()
}

pub fn realistic_pools(g: &mut Gen, total: u64, n: usize) -> Vec<PoolInfo> {
  realistic_stake(g, total, n)
    .iter()
    .map(|(pool, coin)| PoolInfo{reg: Reg{pool: *pool, ..Reg::arbitrary(g)}, stake: *coin})
    .collect()
}

pub fn realistic_registry(g: &mut Gen, total: u64, n: usize, voters: usize) -> Registry {

  let stake: Vec<PoolInfo> = realistic_pools(g, total, n);
  let info: HashMap<PoolKeyhash, PoolInfo> =
    HashMap::from_iter(
      stake.iter()
      .map(|pool| (pool.reg.pool.clone(), pool.clone()))
    );

  let pools: HashMap<PoolKeyhash, Coin> =
    HashMap::from_iter(
      stake.iter()
      .map(|pool| (pool.reg.pool.clone(), pool.stake))
    );
  let fa = fait_accompli(&pools, voters);
  let persistent: HashMap<PersistentId, PoolKeyhash> =
    HashMap::from_iter(
      (0..fa.persistent.len())
      .zip(fa.persistent)
      .map(|(i, (pool, _))| (PersistentId(i as u16), pool))
  );

  let total_stake: Coin = stake.iter().map(|pool| pool.stake).sum();

    Registry {info, persistent, total_stake,}

}

/*
pub fn realistic_cert(g: &mut Gen) -> Cert {

  let eid = Eid::arbitrary(g);

  let ebhash = EbHash::arbitrary(g);



}
*/