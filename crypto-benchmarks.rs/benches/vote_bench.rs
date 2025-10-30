//! Criterion benchmarks for voting.

use criterion::{criterion_group, criterion_main, Criterion};
use leios_crypto_benchmarks::cert::*;
use leios_crypto_benchmarks::registry::{arbitrary_pools, PersistentId, Registry};
use quickcheck::{Arbitrary, Gen};
use std::env;

use leios_crypto_benchmarks::key::{check_pop, key_gen, SecKey};
use leios_crypto_benchmarks::primitive::{
    arbitrary_poolkeyhash, arbitrary_stake_distribution, EbHash, Eid,
};
use leios_crypto_benchmarks::realism::{
    realistic_pool_count, realistic_total_stake, realistic_voters,
};
use leios_crypto_benchmarks::vote::{
    arbitrary_votes, gen_vote_nonpersistent, gen_vote_persistent, verify_vote,
};

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

fn benchmark_gen_cert_impl(c: &mut Criterion, name: &'static str, n_pools: usize, n_voters: usize) {
    let g = &mut Gen::new(10);
    c.bench_function(name, |b| {
        b.iter_batched(
            || {
                let total = realistic_total_stake(g);
                let n = if n_pools > 0 {
                    n_pools
                } else {
                    realistic_pool_count(g)
                };
                let voters = if n_voters > 0 {
                    n_voters
                } else {
                    realistic_voters(g, n)
                };
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

fn benchmark_gen_cert(c: &mut Criterion) {
    benchmark_gen_cert_impl(c, "cert::gen_cert", 0, 0);
    if env::var("BENCHMARK_CERT_EXTRA").map(|x| x == "1") == Result::Ok(true) {
        benchmark_gen_cert_impl(
            c,
            "cert::gen_cert, n_pools = 2500, n_voters = 500",
            2500,
            500,
        );
        benchmark_gen_cert_impl(
            c,
            "cert::gen_cert, n_pools = 2500, n_voters = 600",
            2500,
            600,
        );
        benchmark_gen_cert_impl(
            c,
            "cert::gen_cert, n_pools = 2500, n_voters = 700",
            2500,
            700,
        );
        benchmark_gen_cert_impl(
            c,
            "cert::gen_cert, n_pools = 2500, n_voters = 800",
            2500,
            800,
        );
        benchmark_gen_cert_impl(
            c,
            "cert::gen_cert, n_pools = 2500, n_voters = 900",
            2500,
            900,
        );
        benchmark_gen_cert_impl(
            c,
            "cert::gen_cert, n_pools = 2500, n_voters = 1000",
            2500,
            1000,
        );
    }
}

fn benchmark_verify_cert_impl(
    c: &mut Criterion,
    name: &'static str,
    n_pools: usize,
    n_voters: usize,
) {
    let g = &mut Gen::new(10);
    c.bench_function(name, |b| {
        b.iter_batched(
            || {
                let total = realistic_total_stake(g);
                let n = if n_pools > 0 {
                    n_pools
                } else {
                    realistic_pool_count(g)
                };
                let voters = if n_voters > 0 {
                    n_voters
                } else {
                    realistic_voters(g, n)
                };
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

fn benchmark_verify_cert(c: &mut Criterion) {
    benchmark_verify_cert_impl(c, "cert::verify_cert", 0, 0);
    if env::var("BENCHMARK_CERT_EXTRA").map(|x| x == "1") == Result::Ok(true) {
        benchmark_verify_cert_impl(
            c,
            "cert::verify_cert, n_pools = 2500, n_voters = 500",
            2500,
            500,
        );
        benchmark_verify_cert_impl(
            c,
            "cert::verify_cert, n_pools = 2500, n_voters = 600",
            2500,
            600,
        );
        benchmark_verify_cert_impl(
            c,
            "cert::verify_cert, n_pools = 2500, n_voters = 700",
            2500,
            700,
        );
        benchmark_verify_cert_impl(
            c,
            "cert::verify_cert, n_pools = 2500, n_voters = 800",
            2500,
            800,
        );
        benchmark_verify_cert_impl(
            c,
            "cert::verify_cert, n_pools = 2500, n_voters = 900",
            2500,
            900,
        );
        benchmark_verify_cert_impl(
            c,
            "cert::verify_cert, n_pools = 2500, n_voters = 1000",
            2500,
            1000,
        );
    }
}

fn benchmark_weigh_cert_impl(
    c: &mut Criterion,
    name: &'static str,
    n_pools: usize,
    n_voters: usize,
) {
    let g = &mut Gen::new(10);
    c.bench_function(name, |b| {
        b.iter_batched(
            || {
                let total = realistic_total_stake(g);
                let n = if n_pools > 0 {
                    n_pools
                } else {
                    realistic_pool_count(g)
                };
                let voters = if n_voters > 0 {
                    n_voters
                } else {
                    realistic_voters(g, n)
                };
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
fn benchmark_weigh_cert(c: &mut Criterion) {
    benchmark_weigh_cert_impl(c, "cert::weigh_cert", 0, 0);
    if env::var("BENCHMARK_CERT_EXTRA").map(|x| x == "1") == Result::Ok(true) {
        benchmark_weigh_cert_impl(
            c,
            "cert::weigh_cert, n_pools = 2500, n_voters = 500",
            2500,
            500,
        );
        benchmark_weigh_cert_impl(
            c,
            "cert::weigh_cert, n_pools = 2500, n_voters = 600",
            2500,
            600,
        );
        benchmark_weigh_cert_impl(
            c,
            "cert::weigh_cert, n_pools = 2500, n_voters = 700",
            2500,
            700,
        );
        benchmark_weigh_cert_impl(
            c,
            "cert::weigh_cert, n_pools = 2500, n_voters = 800",
            2500,
            800,
        );
        benchmark_weigh_cert_impl(
            c,
            "cert::weigh_cert, n_pools = 2500, n_voters = 900",
            2500,
            900,
        );
        benchmark_weigh_cert_impl(
            c,
            "cert::weigh_cert, n_pools = 2500, n_voters = 1000",
            2500,
            1000,
        );
    }
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
