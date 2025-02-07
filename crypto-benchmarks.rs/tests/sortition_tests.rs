use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{FromPrimitive, One};
use quickcheck::{Arbitrary, Gen};
use std::cmp::{max, min};

use leios_crypto_benchmarks::key::Sig;
use leios_crypto_benchmarks::sortition::*;

#[test]
fn leader() {
    let f = Ratio::new(BigInt::one(), BigInt::from_i16(20).unwrap());
    let ln1f = ln_1_minus(&f);
    let s = Ratio::new(BigInt::one(), BigInt::from_i16(1000).unwrap());
    let p0 = Ratio::new(
        BigInt::from_i128(512919789090i128).unwrap(),
        BigInt::from_i128(10000000000000000i128).unwrap(),
    );
    let p1 = Ratio::new(
        BigInt::from_i128(512919789091i128).unwrap(),
        BigInt::from_i128(10000000000000000i128).unwrap(),
    );
    assert!(leader_check(&ln1f, &s, &p0));
    assert!(!leader_check(&ln1f, &s, &p1));
}

#[test]
fn uniform_sig_to_rational() {
    let g = &mut Gen::new(10);
    let xs: Vec<Ratio<BigInt>> = (1..100)
        .enumerate()
        .map(|_| Sig::arbitrary(g).to_rational())
        .collect();
    let mn = xs.iter().fold(xs[0].clone(), |acc, x| min(acc, x.clone()));
    let mx = xs.iter().fold(xs[0].clone(), |acc, x| max(acc, x.clone()));
    let av: Ratio<BigInt> = xs.iter().sum();
    assert!(
        mn < Ratio::new(BigInt::from(943u16), BigInt::from(10000u16)),
        "Minimum was {}.",
        mn
    );
    assert!(
        mx > Ratio::new(BigInt::from(9057u16), BigInt::from(10000u16)),
        "Maximum was {}.",
        mx
    );
    assert!(
        av > Ratio::new(BigInt::from(3877u16), BigInt::from(100u16)),
        "Mean (LB) was {}.",
        mx
    );
    assert!(
        av < Ratio::new(BigInt::from(6123u16), BigInt::from(100u16)),
        "Mean (UB) was {}.",
        mx
    );
}
