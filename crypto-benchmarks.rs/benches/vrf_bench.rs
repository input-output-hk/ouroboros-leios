use criterion::{criterion_group, criterion_main, Criterion};

use leios_crypto_benchmarks::vrf::{sk_random, sk_to_pk_point, vrf_prove, vrf_verify};

fn benchmark_prove(c: &mut Criterion) {
    let sk = sk_random();
    let input = b"The VRF input: slot, nonce, and other data.";
    let dst = b"Praos RB";
    c.bench_function("vrf::vrf_prove", |b| b.iter(|| vrf_prove(&sk, input, dst)));
}

fn benchmark_verify(cc: &mut Criterion) {
    let sk = sk_random();
    let pk = sk_to_pk_point(&sk);
    let input = b"The VRF input: slot, nonce, and other data.";
    let dst = b"Praos RB";
    let (gamma, c, s) = vrf_prove(&sk, input, dst);
    cc.bench_function("vrf::vrf_verify", |b| {
        b.iter(|| vrf_verify(&pk, input, dst, &gamma, &c, &s))
    });
}

criterion_group!(benches, benchmark_prove, benchmark_verify);
criterion_main!(benches);
