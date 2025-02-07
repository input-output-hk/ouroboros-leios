use criterion::{criterion_group, criterion_main, Criterion};
use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{FromPrimitive, One};
use quickcheck::{Arbitrary, Gen};

use leios_crypto_benchmarks::sortition::*;

fn arbitrary_f(g: &mut Gen) -> Ratio<BigInt> {
    Ratio::new(
        BigInt::one(),
        BigInt::from_i16(i16::arbitrary(g) % 30 + 5).unwrap(),
    )
}

fn arbitrary_stake(g: &mut Gen) -> Ratio<BigInt> {
    Ratio::new(
        BigInt::one(),
        BigInt::from_i16(i16::arbitrary(g) % 500 + 1).unwrap(),
    )
}

fn arbitrary_votes(g: &mut Gen) -> usize {
    usize::arbitrary(g) % 50 + 100
}

fn arbitrary_probability(g: &mut Gen) -> Ratio<BigInt> {
    Ratio::new(
        BigInt::from_i32(i32::arbitrary(g) % 1000000000).unwrap(),
        BigInt::from_i32(1000000000).unwrap(),
    )
}

fn benchmark_log(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    let f = arbitrary_f(g);
    c.bench_function("log (1 - f)", |b| b.iter(|| ln_1_minus(&f)));
}

fn benchmark_rb(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    let ln1f = arbitrary_f(g);
    let s = arbitrary_stake(g);
    let p = arbitrary_probability(g);
    c.bench_function("RB leadership", |b| b.iter(|| leader_check(&ln1f, &s, &p)));
}

fn benchmark_voter(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    let votes = arbitrary_votes(g);
    let s = arbitrary_stake(g);
    let p = arbitrary_probability(g);
    c.bench_function("IB/EB/vote sortition", |b| {
        b.iter(|| voter_check(votes, &s, &p))
    });
}

criterion_group!(benches, benchmark_log, benchmark_rb, benchmark_voter);
criterion_main!(benches);
