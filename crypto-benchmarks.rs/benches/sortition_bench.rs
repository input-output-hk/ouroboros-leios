use criterion::{criterion_group, criterion_main, Criterion};
use num_traits::{FromPrimitive, One};
use num_bigint::BigInt;
use num_rational::Ratio;
use rustc_apfloat::ieee::Quad;

use leios_crypto_benchmarks::sortition::*;

fn benchmark_log(c: &mut Criterion) {
    let f = Ratio::new(BigInt::one(), BigInt::from_i16(20).unwrap());
    c.bench_function("log (1 - f)", |b| b.iter(|| ln_1_minus(&f)));
}

fn benchmark_rb(c: &mut Criterion) {
    let f = Ratio::new(BigInt::one(), BigInt::from_i16(20).unwrap());
    let ln1f = ln_1_minus(&f);
    let s = Ratio::new(BigInt::one(), BigInt::from_i16(1000).unwrap());
    let p = Ratio::new(BigInt::from_i128(512919789090i128).unwrap(), BigInt::from_i128(10000000000000000i128).unwrap());
    c.bench_function("RB leadership", |b| b.iter(|| leader_check(&ln1f, &s, &p)));
}

fn benchmark_voter(c: &mut Criterion) {
    let votes: Quad = into_quad(500.0);
    let s: Quad = into_quad(0.002);
    let p: Quad = into_quad(0.999);
    c.bench_function("Votes", |b| b.iter(|| voter_check(votes, s, p)));
}

criterion_group!(
    benches,
    benchmark_log,
    benchmark_rb,
    benchmark_voter
);
criterion_main!(benches);
