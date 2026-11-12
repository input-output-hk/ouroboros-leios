---
sidebar_position: 5
---

# Benchmark reports

The Performance & Tracing team benchmarks the Leios node on the same cluster that benchmarks every cardano-node release. The builds here are release candidates of the Leios node, ahead of its integration into a cardano-node release. Each run below holds the endorser-block parameters fixed and saturates them with value transactions, so a change between runs is attributable to the parameter or the build that changed.

These reports will move to [Cardano Updates](https://updates.cardano.intersectmbo.org/reports/tags/benchmarking-reports), where the team publishes its release benchmarks. Until then, they are published here.

## Endorser-block reports

Each report follows the endorser blocks of one run through five stages (forging, propagation, acquiring, closures, certifying) and closes with the forks of the ranking-block chain.

:::info[Reading the certification rate]

The EB certification rate is the share of announced endorser blocks that were certified. The expected certification rate is the share the protocol's timing allows on average: an endorser block can be certified only if no other ranking block arrives within its 14-slot window, which happens for (1 − 0.05)<sup>14</sup> = 48.8% of them. 🟢 marks a run within 5 points of the expected rate, 🟡 within 15 points, 🔴 further below.

:::

### `w45` and the voting fix

Two runs of the 100 kB / 1 MB parameter set with 374 B transactions (two inputs, two outputs) on 51 nodes: the Leios node build `w45` as released, and `w45` with the voting fix that keeps the input table of an endorser block's transactions outside the ledger state ([ouroboros-consensus #2498](https://github.com/IntersectMBO/ouroboros-consensus/pull/2498)). With the fix, 49.0% of announced endorser blocks were certified, up from 26.0%, and the voters that declined an endorser block as too late fell from 56,472 to 104.

| Build | Parameter set (reference cap / closure cap) | Transactions | Run | EB certification rate / expected certification rate | Report |
| :---- | :---- | :---- | :---- | :---- | :---- |
| `w45` with the voting fix | 100 kB / 1 MB | 374 B, 2 inputs 2 outputs | 2026-11-09 | 🟢 49.0% / 48.8% | [open](pathname:///benchmarks/leios-100k1m-374B-2026-11-09.html) |
| `w45` | 100 kB / 1 MB | 374 B, 2 inputs 2 outputs | 2026-11-06 | 🔴 26.0% / 48.8% | [open](pathname:///benchmarks/leios-100k1m-374B-2026-11-06.html) |

In the run with the voting fix, one node disconnected a couple of hours before the end, so some maximum columns are off.

### `w42`

All four runs used the Leios node build `w42` and value transactions, in two shapes. Transactions of 200 B, with one input and one output, fill the reference cap first; transactions of 374 B, with two inputs and two outputs, the workload of the team's Praos comparison runs, fill the closure cap first. Each parameter set therefore has a run at each of its two limits, and each report names the other run of its pair as its control.

| Build | Parameter set (reference cap / closure cap) | Transactions | Run | EB certification rate / expected certification rate | Report |
| :---- | :---- | :---- | :---- | :---- | :---- |
| `w42` | 40 kB / 260 kB | 200 B, 1 input 1 output | 2026-10-22 | 🟢 49.8% / 48.8% | [open](pathname:///benchmarks/leios-40k260k-200B-2026-10-22.html) |
| `w42` | 40 kB / 260 kB | 374 B, 2 inputs 2 outputs | 2026-10-23 | 🟢 51.8% / 48.8% | [open](pathname:///benchmarks/leios-40k260k-374B-2026-10-23.html) |
| `w42` | 100 kB / 1 MB | 200 B, 1 input 1 output | 2026-10-20 | 🟡 36.6% / 48.8% | [open](pathname:///benchmarks/leios-100k1m-200B-2026-10-20.html) |
| `w42` | 100 kB / 1 MB | 374 B, 2 inputs 2 outputs | 2026-10-21 | 🔴 27.4% / 48.8% | [open](pathname:///benchmarks/leios-100k1m-374B-2026-10-21.html) |
