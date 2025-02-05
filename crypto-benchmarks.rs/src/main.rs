use quickcheck::Gen;
use std::collections::BTreeMap;

use leios_crypto_benchmarks::fait_accompli::*;
use leios_crypto_benchmarks::primitive::*;

fn main() {
    let g = &mut Gen::new(10);

    let mut stakes: BTreeMap<PoolKeyhash, Coin> = BTreeMap::new();
    /*
        for _ in 1..10 {
          stakes.insert(arbitrary_poolkeyhash(g), arbitrary_coin(g));
        }
    */
    stakes.insert(arbitrary_poolkeyhash(g), 10);
    stakes.insert(arbitrary_poolkeyhash(g), 50);
    stakes.insert(arbitrary_poolkeyhash(g), 100);
    stakes.insert(arbitrary_poolkeyhash(g), 200);
    stakes.insert(arbitrary_poolkeyhash(g), 500);
    print!("\n");
    print!("Stake\n");
    stakes
        .iter()
        .for_each(|(pool, stake)| print!("  {} : {}\n", pool.to_string(), stake));

    print!("\n");
    let fa = fait_accompli(&stakes, 3);
    print!("Persistent: {}\n", fa.n_persistent);
    fa.persistent
        .iter()
        .for_each(|(pool, weight)| print!("  {} : {}\n", pool, weight));
    print!("Non-persistent: {}\n", fa.n_nonpersistent);
    fa.nonpersistent
        .iter()
        .for_each(|(pool, weight)| print!("  {} : {}\n", pool, weight));
    print!("Rho: {}\n", fa.rho);
}
