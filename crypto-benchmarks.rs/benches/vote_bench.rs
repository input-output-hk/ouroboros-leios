use blst::min_sig::*;
use criterion::{criterion_group, criterion_main, Criterion};
use leios_crypto_benchmarks::registry::PersistentId;
use quickcheck::{Arbitrary, Gen};

use leios_crypto_benchmarks::bls_vote;
use leios_crypto_benchmarks::key::{check_pop, key_gen, SecKey};
use leios_crypto_benchmarks::primitive::{arbitrary_poolkeyhash, EbHash, Eid};
use leios_crypto_benchmarks::vote::*;

fn benchmark_check_pop(c: &mut Criterion) {
    c.bench_function("check_pop", |b| {
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
    c.bench_function("gen_vote_persistent", |b| {
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
    c.bench_function("gen_vote_nonpersistent", |b| {
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
    c.bench_function("verify_vote_persistent", |b| {
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
    c.bench_function("verify_vote_nonpersistent", |b| {
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
    let sks: Vec<SecretKey> = (0..750).map(|_| bls_vote::gen_key()).collect();
    let eid = b"Election ID";
    let m: [u8; 64] = [0; 64];
    let vss: Vec<(Signature, Signature)> = sks
        .iter()
        .map(|sk| bls_vote::gen_vote(&sk, eid, &m))
        .collect();
    let vs_refs: Vec<&(Signature, Signature)> = vss.iter().map(|vs| vs).collect();
    c.bench_function("GenCert", |b| b.iter(|| bls_vote::gen_cert(&vs_refs)));
}

fn benchmark_verify_cert(c: &mut Criterion) {
    let sks: Vec<SecretKey> = (0..750).map(|_| bls_vote::gen_key()).collect();
    let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.sk_to_pk()).collect();
    let pk_refs: Vec<&PublicKey> = pks.iter().map(|pk| pk).collect();
    let eid = b"Election ID";
    let m: [u8; 64] = [0; 64];
    let vss: Vec<(Signature, Signature)> = sks
        .iter()
        .map(|sk| bls_vote::gen_vote(&sk, eid, &m))
        .collect();
    let vs_refs: Vec<&(Signature, Signature)> = vss.iter().map(|vs| vs).collect();
    let cs: (Signature, Signature) = bls_vote::gen_cert(&vs_refs).unwrap();
    c.bench_function("VerifyCert", |b| {
        //      b.iter(|| if ! bls_vote::verify_cert(&pk_refs, eid, &m, &vs_refs, &cs) {panic!("VERIFY FAILED!");})
        b.iter(|| bls_vote::verify_cert(&pk_refs, eid, &m, &vs_refs, &cs))
    });
}

fn benchmark_verify_cert_fa_pure(c: &mut Criterion) {
    let sks: Vec<SecretKey> = (0..750).map(|_| bls_vote::gen_key()).collect();
    let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.sk_to_pk()).collect();
    let pk_refs: Vec<&PublicKey> = pks.iter().map(|pk| pk).collect();
    let eid = b"Election ID";
    let m: [u8; 64] = [0; 64];
    let vss: Vec<(Signature, Signature)> = sks
        .iter()
        .map(|sk| bls_vote::gen_vote(&sk, eid, &m))
        .collect();
    let vs_refs: Vec<&Signature> = vss.iter().map(|vs| &vs.1).collect();
    let cs: Signature = bls_vote::gen_cert_fa_pure(&vs_refs).unwrap();
    c.bench_function("VerifyCert (pure)", |b| {
        b.iter(|| {
            if !bls_vote::verify_cert_fa_pure(&pk_refs, eid, &m, &cs) {
                panic!("VERIFY FAILED!");
            }
        })
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
    benchmark_verify_cert_fa_pure,
);

criterion_main!(benches);
