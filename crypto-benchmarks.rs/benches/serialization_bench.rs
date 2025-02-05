use criterion::{criterion_group, criterion_main, Criterion};
use quickcheck::{Arbitrary, Gen};

use leios_crypto_benchmarks::key::Reg;
use leios_crypto_benchmarks::vote::Vote;

fn benchmark_serialize_reg(c: &mut Criterion) {
    let mut g = Gen::new(10);
    c.bench_function("Reg::serialize", |b| {
        b.iter_batched(
            || Reg::arbitrary(&mut g),
            |reg: Reg| {
                serde_cbor::to_vec(&reg).unwrap().as_slice();
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

fn benchmark_deserialize_reg(c: &mut Criterion) {
    let mut g = Gen::new(10);
    c.bench_function("Reg::deserialize", |b| {
        b.iter_batched(
            || {
                let reg = Reg::arbitrary(&mut g);
                serde_cbor::to_vec(&reg).unwrap()
            },
            |bytes| {
                let _: Reg = serde_cbor::from_slice(&bytes).unwrap();
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

fn benchmark_serialize_vote(c: &mut Criterion) {
    let mut g = Gen::new(10);
    c.bench_function("Vote::serialize", |b| {
        b.iter_batched(
            || Vote::arbitrary(&mut g),
            |reg: Vote| {
                serde_cbor::to_vec(&reg).unwrap().as_slice();
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

fn benchmark_deserialize_vote(c: &mut Criterion) {
    let mut g = Gen::new(10);
    c.bench_function("Vote::deserialize", |b| {
        b.iter_batched(
            || {
                let reg = Vote::arbitrary(&mut g);
                serde_cbor::to_vec(&reg).unwrap()
            },
            |bytes| {
                let _: Vote = serde_cbor::from_slice(&bytes).unwrap();
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

criterion_group!(
    benches,
    benchmark_serialize_reg,
    benchmark_deserialize_reg,
    benchmark_serialize_vote,
    benchmark_deserialize_vote,
);

criterion_main!(benches);
