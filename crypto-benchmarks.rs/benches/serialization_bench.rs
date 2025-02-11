use criterion::{criterion_group, criterion_main, Criterion};
use quickcheck::{Arbitrary, Gen};

use leios_crypto_benchmarks::cert::*;
use leios_crypto_benchmarks::key::Reg;
use leios_crypto_benchmarks::primitive::*;
use leios_crypto_benchmarks::realism::*;
use leios_crypto_benchmarks::registry::*;
use leios_crypto_benchmarks::vote::*;

fn benchmark_serialize_reg(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("Reg::serialize", |b| {
        b.iter_batched(
            || Reg::arbitrary(g),
            |reg: Reg| {
                serde_cbor::to_vec(&reg).unwrap().as_slice();
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

fn benchmark_deserialize_reg(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("Reg::deserialize", |b| {
        b.iter_batched(
            || {
                let reg = Reg::arbitrary(g);
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
    let g = &mut Gen::new(10);
    c.bench_function("Vote::serialize", |b| {
        b.iter_batched(
            || Vote::arbitrary(g),
            |reg: Vote| {
                serde_cbor::to_vec(&reg).unwrap().as_slice();
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

fn benchmark_deserialize_vote(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("Vote::deserialize", |b| {
        b.iter_batched(
            || {
                let reg = Vote::arbitrary(g);
                serde_cbor::to_vec(&reg).unwrap()
            },
            |bytes| {
                let _: Vote = serde_cbor::from_slice(&bytes).unwrap();
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

fn benchmark_serialize_cert(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("Cert::serialize", |b| {
        b.iter_batched(
            || {
                let total = realistic_total_stake(g);
                let n = realistic_pool_count(g);
                let voters = realistic_voters(g, n);
                let stake = arbitrary_stake_distribution(g, total, n, 11., 1.);
                let pools = arbitrary_pools(g, &stake);
                let reg = Registry::make(&pools, voters);
                let votes = arbitrary_votes(g, &reg);
                let cert = gen_cert(&reg, &votes).unwrap();
                cert
            },
            |cert: Cert| {
                serde_cbor::to_vec(&cert).unwrap().as_slice();
            },
            criterion::BatchSize::LargeInput,
        )
    });
}

fn benchmark_deserialize_cert(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("Cert::deserialize", |b| {
        b.iter_batched(
            || {
                let total = realistic_total_stake(g);
                let n = realistic_pool_count(g);
                let voters = realistic_voters(g, n);
                let stake = arbitrary_stake_distribution(g, total, n, 11., 1.);
                let pools = arbitrary_pools(g, &stake);
                let reg = Registry::make(&pools, voters);
                let votes = arbitrary_votes(g, &reg);
                let cert = gen_cert(&reg, &votes).unwrap();
                serde_cbor::to_vec(&cert).unwrap()
            },
            |bytes| {
                let _: Cert = serde_cbor::from_slice(&bytes).unwrap();
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
    benchmark_serialize_cert,
    benchmark_deserialize_cert,
);

criterion_main!(benches);
