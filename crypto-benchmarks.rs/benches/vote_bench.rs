use criterion::{criterion_group, criterion_main, Criterion};
use quickcheck::{Arbitrary, Gen};

use leios_crypto_benchmarks::api::*;

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

fn benchmark_gen_vote(c: &mut Criterion) {
    let mut g = Gen::new(10);
    c.bench_function("gen_vote", |b| {
        b.iter_batched(
            || {
                let eid = Eid::arbitrary(&mut g);
                let m = EbHash::arbitrary(&mut g);
                let sk = SecKey::arbitrary(&mut g);
                (eid, m, sk)
            },
            |(eid, m, sk)| {
                gen_vote(&eid, &m, &sk);
            },
            criterion::BatchSize::SmallInput,
        )
    });
}

fn benchmark_verify_vote(c: &mut Criterion) {
    let mut g = Gen::new(10);
    c.bench_function("verify_vote", |b| {
        b.iter_batched(
            || {
                let eid = Eid::arbitrary(&mut g);
                let m = EbHash::arbitrary(&mut g);
                let sk = SecKey::arbitrary(&mut g);
                let vote = gen_vote(&eid, &m, &sk);
                (eid, m, sk.pub_key(), vote)
            },
            |(eid, m, mvk, vote)| verify_vote(&eid, &m, &mvk, &vote),
            criterion::BatchSize::SmallInput,
        )
    });
}

/*
fn benchmark_gen_cert(c: &mut Criterion) {
    let sks: Vec<SecretKey> = (0..750).map(|_| gen_key()).collect();
    let eid = b"Election ID";
    let m: [u8; 64] = [0; 64];
    let vss: Vec<VoteSignature> = sks.iter().map(|sk| gen_vote(&sk, eid, &m)).collect();
    let vs_refs: Vec<&VoteSignature> = vss.iter().map(|vs| vs).collect();
    c.bench_function("GenCert", |b| b.iter(|| gen_cert(&vs_refs)));
}

fn benchmark_verify_cert(c: &mut Criterion) {
    let sks: Vec<SecretKey> = (0..750).map(|_| gen_key()).collect();
    let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.sk_to_pk()).collect();
    let pk_refs: Vec<&PublicKey> = pks.iter().map(|pk| pk).collect();
    let eid = b"Election ID";
    let m: [u8; 64] = [0; 64];
    let vss: Vec<VoteSignature> = sks.iter().map(|sk| gen_vote(&sk, eid, &m)).collect();
    let vs_refs: Vec<&VoteSignature> = vss.iter().map(|vs| vs).collect();
    let cs: CertSignature = gen_cert(&vs_refs).unwrap();
    c.bench_function("VerifyCert", |b| {
        b.iter(|| verify_cert(&pk_refs, eid, &m, &vs_refs, &cs))
    });
}
*/

criterion_group!(
    benches,
    benchmark_check_pop,
    benchmark_gen_vote,
    benchmark_verify_vote, /*
                           benchmark_gen_cert,
                           benchmark_verify_cert,*/
);

criterion_main!(benches);
