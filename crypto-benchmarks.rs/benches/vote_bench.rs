use criterion::{criterion_group, criterion_main, Criterion};
use leios_crypto_benchmarks::cert::*;
use leios_crypto_benchmarks::registry::{arbitrary_pools, PersistentId, Registry};
use quickcheck::{Arbitrary, Gen};

use leios_crypto_benchmarks::key::{check_pop, key_gen, SecKey};
use leios_crypto_benchmarks::primitive::{
    arbitrary_poolkeyhash, arbitrary_stake_distribution, EbHash, Eid,
};
use leios_crypto_benchmarks::realism::*;
use leios_crypto_benchmarks::vote::*;

fn benchmark_check_pop(c: &mut Criterion) {
    c.bench_function("key::check_pop", |b| {
        b.iter_batched(
            || {
                let (_, mvk, mu) = key_gen();
                (mvk, mu)
            },
            |(mvk, mu)| check_pop(&mvk, &mu),
            criterion::BatchSize::SmallInput,
        )
    });
}

fn benchmark_gen_vote_persistent(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("vote::gen_vote_persistent", |b| {
        b.iter_batched(
            || {
                let persistent = PersistentId::arbitrary(g);
                let eid = Eid::arbitrary(g);
                let m = EbHash::arbitrary(g);
                let sk = SecKey::arbitrary(g);
                (persistent, eid, m, sk)
            },
            |(persistent, eid, m, sk)| {
                gen_vote_persistent(&persistent, &eid, &m, &sk);
            },
            criterion::BatchSize::SmallInput,
        )
    });
}

fn benchmark_gen_vote_nonpersistent(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("vote::gen_vote_nonpersistent", |b| {
        b.iter_batched(
            || {
                let pool = arbitrary_poolkeyhash(g);
                let eid = Eid::arbitrary(g);
                let m = EbHash::arbitrary(g);
                let sk = SecKey::arbitrary(g);
                (pool, eid, m, sk)
            },
            |(pool, eid, m, sk)| {
                gen_vote_nonpersistent(&pool, &eid, &m, &sk);
            },
            criterion::BatchSize::SmallInput,
        )
    });
}

fn benchmark_verify_vote_persistent(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("vote::verify_vote_persistent", |b| {
        b.iter_batched(
            || {
                let persistent = PersistentId::arbitrary(g);
                let eid = Eid::arbitrary(g);
                let m = EbHash::arbitrary(g);
                let sk = SecKey::arbitrary(g);
                let vote = gen_vote_persistent(&persistent, &eid, &m, &sk);
                (sk.pub_key(), vote)
            },
            |(mvk, vote)| verify_vote(&mvk, &vote),
            criterion::BatchSize::SmallInput,
        )
    });
}

fn benchmark_verify_vote_nonpersistent(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("vote::verify_vote_nonpersistent", |b| {
        b.iter_batched(
            || {
                let pool = arbitrary_poolkeyhash(g);
                let eid = Eid::arbitrary(g);
                let m = EbHash::arbitrary(g);
                let sk = SecKey::arbitrary(g);
                let vote = gen_vote_nonpersistent(&pool, &eid, &m, &sk);
                (sk.pub_key(), vote)
            },
            |(mvk, vote)| verify_vote(&mvk, &vote),
            criterion::BatchSize::SmallInput,
        )
    });
}

fn benchmark_gen_cert(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("cert::gen_cert", |b| {
        b.iter_batched(
            || {
                let total = realistic_total_stake(g);
                let n = realistic_pool_count(g);
                let voters = realistic_voters(g, n);
                let stake = arbitrary_stake_distribution(g, total, n, 11., 1.);
                let pools = arbitrary_pools(g, &stake);
                let reg = Registry::make(&pools, voters);
                let votes = arbitrary_votes(g, &reg);
                (reg, votes)
            },
            |(reg, votes)| gen_cert(&reg, &votes),
            criterion::BatchSize::SmallInput,
        )
    });
}

fn benchmark_verify_cert(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("cert::verify_cert", |b| {
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
                (reg, cert)
            },
            |(reg, cert)| verify_cert(&reg, &cert),
            criterion::BatchSize::SmallInput,
        )
    });
}

fn benchmark_weigh_cert(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("cert::weigh_cert", |b| {
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
                (reg, cert)
            },
            |(reg, cert)| weigh_cert(&reg, &cert),
            criterion::BatchSize::SmallInput,
        )
    });
}

criterion_group!(
    benches,
    benchmark_check_pop,
    benchmark_gen_vote_persistent,
    benchmark_gen_vote_nonpersistent,
    benchmark_verify_vote_persistent,
    benchmark_verify_vote_nonpersistent,
    benchmark_gen_cert,
    benchmark_verify_cert,
    benchmark_weigh_cert,
);

criterion_main!(benches);
