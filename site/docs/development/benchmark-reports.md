---
sidebar_position: 5
---

# Benchmark reports

The Performance & Tracing team benchmarks the Leios node on the same cluster that benchmarks every cardano-node release. Each run below holds the endorser-block parameters fixed and saturates them with value transactions, so a change between runs is attributable to the parameter that changed.

These reports will move to [Cardano Updates](https://updates.cardano.intersectmbo.org/reports/tags/benchmarking-reports), where the team publishes its release benchmarks. Until then, they are published here.

## Endorser-block reports

Each report follows the endorser blocks of one run through five stages (forging, propagation, acquiring, closures, certifying) and closes with the forks of the ranking-block chain.

All four runs used the Leios node build `w42` and value transactions, in two shapes. Transactions of 200 B, with one input and one output, fill the reference cap first; transactions of 374 B, with two inputs and two outputs, the workload of the team's Praos comparison runs, fill the closure cap first. Each parameter set therefore has a run at each of its two limits, and each report names the other run of its pair as its control.

| Parameter set (reference cap / closure cap) | Transactions | Cap that binds | Run | Report |
| :---- | :---- | :---- | :---- | :---- |
| 40 kB / 260 kB | 200 B, 1 input 1 output | reference cap | 2026-10-22 | [open](pathname:///benchmarks/leios-40k260k-200B-2026-10-22.html) |
| 40 kB / 260 kB | 374 B, 2 inputs 2 outputs | closure cap | 2026-10-23 | [open](pathname:///benchmarks/leios-40k260k-374B-2026-10-23.html) |
| 100 kB / 1 MB | 200 B, 1 input 1 output | reference cap | 2026-10-20 | [open](pathname:///benchmarks/leios-100k1m-200B-2026-10-20.html) |
| 100 kB / 1 MB | 374 B, 2 inputs 2 outputs | closure cap | 2026-10-21 | [open](pathname:///benchmarks/leios-100k1m-374B-2026-10-21.html) |
