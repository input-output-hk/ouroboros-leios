use num_bigint::BigInt;
use num_rational::Ratio;
use std::collections::BTreeMap;

use leios_crypto_benchmarks::fait_accompli::*;
use leios_crypto_benchmarks::primitive::*;

#[test]
fn fa_test() {
    let p1 = PoolKeyhash::from([0x81; 28]);
    let p2 = PoolKeyhash::from([0x83; 28]);
    let p3 = PoolKeyhash::from([0x41; 28]);
    let p4 = PoolKeyhash::from([0x49; 28]);
    let p5 = PoolKeyhash::from([0x23; 28]);
    let p6 = PoolKeyhash::from([0x33; 28]);
    let p7 = PoolKeyhash::from([0x52; 28]);
    let p8 = PoolKeyhash::from([0x17; 28]);

    let mut stakes: BTreeMap<PoolKeyhash, Coin> = BTreeMap::new();
    stakes.insert(p7, 40);
    stakes.insert(p1, 3000);
    stakes.insert(p8, 10);
    stakes.insert(p5, 100);
    stakes.insert(p4, 100);
    stakes.insert(p3, 200);
    stakes.insert(p6, 50);
    stakes.insert(p2, 500);

    let fa = fait_accompli(&stakes, 5);

    assert_eq!(4, fa.n_persistent, "Incorrect number of persistent voters.");
    assert_eq!(
        1, fa.n_nonpersistent,
        "Incorrect number of non-persistent voters."
    );
    assert_eq!(
        Ratio::from_integer(BigInt::from(200)),
        fa.rho.0,
        "Incorrect rho."
    );

    let expected_persistent: Vec<(PoolKeyhash, CoinFraction)> =
        [(p1, 3000u64), (p2, 500u64), (p3, 200u64), (p4, 100u64)]
            .iter()
            .map(|(p, x)| (*p, CoinFraction::from_coins(*x, 1)))
            .collect();
    assert_eq!(
        expected_persistent, fa.persistent,
        "Unexpected persistent voters."
    );

    let expected_nonpersistent: Vec<(PoolKeyhash, CoinFraction)> =
        [(p8, 10u64), (p5, 100u64), (p6, 50u64), (p7, 40u64)]
            .iter()
            .map(|(p, x)| (*p, CoinFraction::from_coins(*x, 200)))
            .collect();
    let actual_nonpersistent: Vec<(PoolKeyhash, CoinFraction)> =
        fa.nonpersistent.into_iter().collect();
    assert_eq!(
        expected_nonpersistent, actual_nonpersistent,
        "Unexpected non-persistent voters."
    );
}
