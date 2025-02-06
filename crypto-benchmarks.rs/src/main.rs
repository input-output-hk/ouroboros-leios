use quickcheck::Gen;
use std::collections::BTreeMap;

use leios_crypto_benchmarks::fait_accompli::*;
use leios_crypto_benchmarks::primitive::*;

fn main() {
    let g = &mut Gen::new(10);

    let mut stakes: BTreeMap<PoolKeyhash, Coin> = BTreeMap::new();
        for _ in 1..10 {
          stakes.insert(arbitrary_poolkeyhash(g), arbitrary_coin(g));
        }
    /*
    stakes.insert(arbitrary_poolkeyhash(g), 10);
    stakes.insert(arbitrary_poolkeyhash(g), 40);
    stakes.insert(arbitrary_poolkeyhash(g), 50);
    stakes.insert(arbitrary_poolkeyhash(g), 100);
    stakes.insert(arbitrary_poolkeyhash(g), 100);
    stakes.insert(arbitrary_poolkeyhash(g), 200);
    stakes.insert(arbitrary_poolkeyhash(g), 500);
    stakes.insert(arbitrary_poolkeyhash(g), 750);
    */
    println!("");
    println!("Stake");
    stakes
        .iter()
        .for_each(|(pool, stake)| println!("  {} : {}", pool.to_string(), stake));

    println!("");
    let fa = fait_accompli(&stakes, 5);
    println!("Persistent: {}", fa.n_persistent);
    fa.persistent
        .iter()
        .for_each(|(pool, weight)| println!("  {} : {}", pool, weight));
    println!("Non-persistent: {}", fa.n_nonpersistent);
    fa.nonpersistent
        .iter()
        .for_each(|(pool, weight)| println!("  {} : {}", pool, weight));
    println!("Rho: {}", fa.rho);
}
