use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{FromPrimitive, One};
use quickcheck::Gen;
use std::collections::BTreeMap;

use leios_crypto_benchmarks::fait_accompli::*;
use leios_crypto_benchmarks::primitive::*;
use leios_crypto_benchmarks::sortition::*;

fn main() {
    let g = &mut Gen::new(10);

    let mut stakes: BTreeMap<PoolKeyhash, Coin> = BTreeMap::new();
    for i in 1..10 {
        let pool = PoolKeyhash::from([
            (i >> 8) as u8,
            (i & 0xFF) as u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
            0u8,
        ]);
        stakes.insert(pool, arbitrary_coin(g));
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
    println!();
    println!("Stake");
    stakes
        .iter()
        .for_each(|(pool, stake)| println!("  {} : {}", pool, stake));

    println!();
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

    let f = Ratio::new(BigInt::one(), BigInt::from_i16(20).unwrap());
    let ln1f = ln_1_minus(&f);
    println!("ln(1 - {}) = {}", f.clone(), ln1f.clone());
    let s = Ratio::new(BigInt::one(), BigInt::from_i16(1000).unwrap());
    let p0 = Ratio::new(BigInt::from_i128(512919789090i128).unwrap(), BigInt::from_i128(10000000000000000i128).unwrap());
    let p1 = Ratio::new(BigInt::from_i128(512919789091i128).unwrap(), BigInt::from_i128(10000000000000000i128).unwrap());
    println!("{}", leader_check(&ln1f, &s, &p0));
    println!("{}", leader_check(&ln1f, &s, &p1));

}
