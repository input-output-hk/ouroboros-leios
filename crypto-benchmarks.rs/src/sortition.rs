//! Sortition operations.

use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{FromPrimitive, One, Signed, Zero};

/// Compute the logarithm of one minus a value `f`, to the precision allowed by `Ratio<BigInt`.
pub fn ln_1_minus(f: &Ratio<BigInt>) -> Ratio<BigInt> {
    let epsilon = Ratio::new(
        BigInt::one(),
        BigInt::from_i128(10000000000000000000000000000000000i128).unwrap(),
    );
    let zero = Ratio::from_integer(BigInt::zero());
    let one = Ratio::from_integer(BigInt::one());
    let mut acc = zero;
    let mut prev = one.clone();
    let mut i = one.clone();
    loop {
        let term = prev * f;
        let acc1 = acc.clone() - term.clone() / i.clone();
        if Signed::abs(&(acc.clone() - acc1.clone())) < epsilon {
            break acc;
        }
        prev = term;
        acc = acc1;
        i += one.clone();
    }
}

/// Verify that a pool with fraction `s` of the stake is selected in the block-production lottery at probability `p`, given the logarithm of one minus the active slot coefficient `ln1f`.
pub fn leader_check(ln1f: &Ratio<BigInt>, s: &Ratio<BigInt>, p: &Ratio<BigInt>) -> bool {
    let t0 = s * ln1f;
    let zero = Ratio::from_integer(BigInt::zero());
    let one = Ratio::from_integer(BigInt::one());
    let mut acc = zero;
    let mut prev = one.clone();
    let mut i = one.clone();
    loop {
        let term = prev.clone() * t0.clone() / i.clone();
        let err = Signed::abs(&term);
        let acc1 = acc.clone() - term.clone();
        if p < &(acc1.clone() - err.clone()) {
            break true;
        } else if p > &(acc1.clone() + err.clone()) {
            break false;
        }
        prev = term;
        acc = acc1;
        i += one.clone();
    }
}

/// Compute $e^x$ to the precision allowed by `Ratio<BigInt>`.
fn exp(x: &Ratio<BigInt>) -> Ratio<BigInt> {
    let epsilon = Ratio::new(
        BigInt::one(),
        BigInt::from_i128(10000000000000000000000000000000000i128).unwrap(),
    );
    let one = Ratio::from_integer(BigInt::one());
    let mut prev = one.clone();
    let mut acc = prev.clone();
    let mut i = one.clone();
    loop {
        let term = prev.clone() * x.clone() / i.clone();
        let acc1 = acc.clone() + term.clone();
        // FIXME: This could be terminated sooner if we do a careful analysis of errors.
        if Signed::abs(&(acc.clone() - acc1.clone())) < epsilon {
            break acc;
        }
        prev = term;
        acc = acc1;
        i += one.clone();
    }
}

/// Verify that a pool with fraction `s` of the stake is selected as a voter at probability `p`, given a committee size of `votes`.
pub fn voter_check(votes: usize, s: &Ratio<BigInt>, p: &Ratio<BigInt>) -> usize {
    let x = Ratio::from_integer(BigInt::from_usize(votes).unwrap()) * s;
    let v = p / exp(&(-x.clone()));
    let mut i: usize = 0;
    let mut prev = Ratio::from_integer(BigInt::one());
    let mut acc = prev.clone();
    loop {
        if v <= acc.clone() || i > 10 {
            break i;
        }
        i += 1;
        let ii = Ratio::from_integer(BigInt::from_usize(i).unwrap());
        if i == votes {
            break i;
        }
        let term = prev * x.clone() / ii;
        acc += term.clone();
        prev = term;
    }
}
