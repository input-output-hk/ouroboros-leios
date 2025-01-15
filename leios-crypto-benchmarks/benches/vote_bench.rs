use blst::{min_sig::PublicKey, min_sig::SecretKey};
use criterion::{criterion_group, criterion_main, Criterion};
use leios_crypto_benchmarks::vote::*;

fn benchmark_gen_vote(c: &mut Criterion) {
  let sk : SecretKey = gen_key();
  let eid = b"Election ID";
  let m : [u8; 500] = [0; 500];
  c.bench_function("GenVote", | b | b.iter(|| gen_vote(&sk, eid, &m)));
}

fn benchmark_verify_vote(c: &mut Criterion) {
  let sk : SecretKey = gen_key();
  let pk: blst::min_sig::PublicKey = sk.sk_to_pk();
  let eid = b"Election ID";
  let m : [u8; 500] = [0; 500];
  let vs : VoteSignature = gen_vote(&sk, eid, &m);
  c.bench_function("VerifyVote", | b | b.iter(|| verify_vote(&pk, eid, &m, &vs)));
}

fn benchmark_gen_cert(c: &mut Criterion) {
  let sks : Vec<SecretKey> = [1..300].iter().map(|_| gen_key()).collect();
  let eid = b"Election ID";
  let m : [u8; 500] = [0; 500];
  let vss : Vec<VoteSignature> = sks.iter().map(|sk| gen_vote(&sk, eid, &m)).collect();
  let vs_refs : Vec<&VoteSignature> = vss.iter().map(|vs| vs).collect();
  c.bench_function("GenCert", | b | b.iter(|| gen_cert(&vs_refs)));
}

fn benchmark_verify_cert(c: &mut Criterion) {
  let sks : Vec<SecretKey> = [1..300].iter().map(|_| gen_key()).collect();
  let pks : Vec<PublicKey> = sks.iter().map(|sk| sk.sk_to_pk()).collect();
  let pk_refs : Vec<&PublicKey> = pks.iter().map(|pk| pk).collect();
  let eid = b"Election ID";
  let m : [u8; 500] = [0; 500];
  let vss : Vec<VoteSignature> = sks.iter().map(|sk| gen_vote(&sk, eid, &m)).collect();
  let vs_refs : Vec<&VoteSignature> = vss.iter().map(|vs| vs).collect();
  let cs: CertSignature = gen_cert(&vs_refs).unwrap();
  c.bench_function("VerifyCert", | b | b.iter(|| verify_cert(&pk_refs, eid, &m, &cs)));
}

criterion_group!(benches,
  benchmark_gen_vote,
  benchmark_verify_vote,
  benchmark_gen_cert,
  benchmark_verify_cert,
);

criterion_main!(benches);