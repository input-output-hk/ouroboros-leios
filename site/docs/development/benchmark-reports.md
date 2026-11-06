---
sidebar_position: 5
---

# Benchmark reports

The Performance & Tracing team benchmarks the Leios node on the same cluster that benchmarks every cardano-node release. Each run below holds the endorser-block parameters fixed and saturates them with value transactions, so a change between runs is attributable to the parameter that changed.

These reports will move to [Cardano Updates](https://updates.cardano.intersectmbo.org/reports/tags/benchmarking-reports), where the team publishes its release benchmarks. Until then, they are published here.

## Endorser-block reports

Each report follows the endorser blocks of one run through five stages (forging, propagation, acquiring, closures, certifying) and closes with the forks of the ranking-block chain.

Both runs used the Leios node build `w42` and the same transactions, 374 B with two inputs and two outputs, the workload of the team's Praos comparison runs.

| Parameter set (reference cap / closure cap) | Transactions | Run | Report |
| :---- | :---- | :---- | :---- |
| 40 kB / 260 kB | 374 B, 2 inputs 2 outputs | 2026-10-23 | [open](https://leios.cardano-scaling.org/benchmarks/leios-40k260k-374B-2026-10-23.html) |
| 100 kB / 1 MB | 374 B, 2 inputs 2 outputs | 2026-10-21 | [open](https://leios.cardano-scaling.org/benchmarks/leios-100k1m-374B-2026-10-21.html) |
