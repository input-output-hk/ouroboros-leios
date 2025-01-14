use criterion::{criterion_group, criterion_main, Criterion};
use leios_crypto_benchmarks::sortition::*;
use rustc_apfloat::ieee::Quad;

fn benchmark_log(c: &mut Criterion) {
  let f : Quad = into_quad(0.05);
  c.bench_function("log (1 - f)", | b | b.iter(|| ln_1_minus(f)));
}

fn benchmark_sortition(c: &mut Criterion) {
  let f : Quad = into_quad(0.05);
  let s : Quad = into_quad(0.001);
  let p : Quad = into_quad(1.0 - (1.0 - 0.05 as f64).powf(0.0001 as f64));
  c.bench_function("leader_check", | b | b.iter(|| leader_check(f, s, p)));
}

criterion_group!(benches, benchmark_log, benchmark_sortition);
criterion_main!(benches);