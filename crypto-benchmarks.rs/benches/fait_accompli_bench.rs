use criterion::{criterion_group, criterion_main, Criterion};
use quickcheck::{Arbitrary, Gen};
use std::collections::BTreeMap;

use leios_crypto_benchmarks::fait_accompli::FaSortition;
use leios_crypto_benchmarks::primitive::{arbitrary_coin, Coin, PoolKeyhash};

fn benchmark_fa(c: &mut Criterion) {
    let g = &mut Gen::new(10);
    c.bench_function("fait_accompli", |b| {
        b.iter_batched(
            || {
                let mut pools: BTreeMap<PoolKeyhash, Coin> = BTreeMap::new();
                for i in 1..3000 {
                    let pool = PoolKeyhash::from([
                        (i >> 8) as u8,
                        (i & 0xFF) as u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                        0u8,
                    ]);
                    pools.insert(pool, arbitrary_coin(g));
                }
                let n = usize::arbitrary(g) % 500 + 500;
                (pools, n)
            },
            |(pools, n)| FaSortition::fait_accompli(&pools, n),
            criterion::BatchSize::SmallInput,
        )
    });
}
criterion_group!(benches, benchmark_fa,);

criterion_main!(benches);
