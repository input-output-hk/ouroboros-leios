use criterion::{criterion_group, criterion_main, Criterion};
use rustc_apfloat::ieee::Quad;

use leios_crypto_benchmarks::sortition::*;

fn benchmark_log(c: &mut Criterion) {
    let f: Quad = into_quad(0.05);
    c.bench_function("log (1 - f)", |b| b.iter(|| ln_1_minus(f)));
}

fn benchmark_rb(c: &mut Criterion) {
    let f: Quad = into_quad(0.05);
    let s: Quad = into_quad(0.002);
    let p: Quad = into_quad(1.0 - (1.0 - 0.05_f64).powf(0.0001_f64));
    c.bench_function("RB leadership", |b| b.iter(|| leader_check(f, s, p)));
}

fn benchmark_ib(c: &mut Criterion) {
    let f: Quad = into_quad(0.90);
    let s: Quad = into_quad(0.002);
    let p: Quad = into_quad(1.0 - (1.0 - 0.90_f64).powf(0.002_f64));
    c.bench_function("IB leadership", |b| b.iter(|| leader_check(f, s, p)));
}

fn benchmark_eb(c: &mut Criterion) {
    let f: Quad = into_quad(0.75);
    let s: Quad = into_quad(0.02);
    let p: Quad = into_quad(1.0 - (1.0 - 0.75_f64).powf(0.002_f64));
    c.bench_function("EB leadership", |b| b.iter(|| leader_check(f, s, p)));
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
    benchmark_ib,
    benchmark_eb,
    benchmark_voter
);
criterion_main!(benches);
