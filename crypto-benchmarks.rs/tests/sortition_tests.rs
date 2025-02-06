use num_bigint::BigInt;
use num_rational::Ratio;
use rustc_apfloat::ieee::Quad;
use quickcheck::{Arbitrary, Gen};
use std::cmp::{min,max};

use leios_crypto_benchmarks::key::Sig;
use leios_crypto_benchmarks::sortition::*;

#[test]
fn leader() {
    let f: Quad = "4.8771764574959465286614323309274434524463393558834E-2"
        .parse::<Quad>()
        .unwrap();
    let f1: Quad = ln_1_minus(f);
    let s: Quad = into_quad(0.001);
    let pexpected: f64 = 1.0 - (1.0 - 4.877_176_457_495_946_4e-2_f64).powf(0.001_f64);
    assert!(leader_check(f1, s, into_quad(pexpected - 1e-15)));
    assert!(!leader_check(f1, s, into_quad(pexpected + 1e-15)));
}

#[test]
fn uniform_sig_to_rational()
{
    let g = &mut Gen::new(10);
    let xs: Vec<Ratio<BigInt>> = (1..100).enumerate().map(|_| Sig::arbitrary(g).to_rational()).collect();
    let mn = xs.iter().fold(xs[0].clone(), |acc, x| min(acc, x.clone()));
    let mx = xs.iter().fold(xs[0].clone(), |acc, x| max(acc, x.clone()));
    let av: Ratio<BigInt> = xs.iter().sum();
    assert!(mn < Ratio::new(BigInt::from(943u16), BigInt::from(10000u16)), "Minimum was {}.", mn);
    assert!(mx > Ratio::new(BigInt::from(9057u16), BigInt::from(10000u16)), "Maximum was {}.", mx);
    assert!(av > Ratio::new(BigInt::from(3877u16), BigInt::from(100u16)), "Mean (LB) was {}.", mx);
    assert!(av < Ratio::new(BigInt::from(6123u16), BigInt::from(100u16)), "Mean (UB) was {}.", mx);
}