# Run digest

Extracted from the node and generator logs, which were then discarded.
`sampler.tsv` and `provenance.txt` sit alongside.

## Mempool add path, per node

| node | adds | adds/s | p50 gap | p99 gap | max gap | stalled | peak depth |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bp1 | 252635 | 225.2 | 0.5 ms | 21 ms | 75.4 s | 18% | 32654 |
| bp2 | 255012 | 225.9 | 0.5 ms | 21 ms | 68.0 s | 19% | 32484 |
| bp3 | 285077 | 252.4 | 0.5 ms | 20 ms | 50.8 s | 10% | 30664 |
| relay11 | 252713 | 216.6 | 2.4 ms | 4 ms | 96.1 s | 59% | 33662 |
| relay12 | 291743 | 262.4 | 0.5 ms | 19 ms | 90.0 s | 29% | 34048 |
| relay13 | 296305 | 266.5 | 0.4 ms | 19 ms | 90.2 s | 30% | 34330 |
| relay21 | 253824 | 228.4 | 1.3 ms | 18 ms | 96.7 s | 48% | 33803 |
| relay22 | 296670 | 266.8 | 0.5 ms | 19 ms | 90.2 s | 30% | 34132 |
| relay23 | 296902 | 267.0 | 0.4 ms | 19 ms | 88.1 s | 31% | 34017 |
| relay31 | 278760 | 250.8 | 0.6 ms | 19 ms | 91.4 s | 39% | 33822 |
| relay32 | 286237 | 256.5 | 0.5 ms | 19 ms | 89.5 s | 30% | 34138 |
| relay33 | 298416 | 268.3 | 0.5 ms | 19 ms | 87.6 s | 31% | 33808 |

## Generators

| generator | txs | avg tx/s | busy-second p50 | zero-seconds | max gap |
| --- | --- | --- | --- | --- | --- |
| tx-firehose1.log | 174040 | 149.2 | 388 | 56% | 96.1 s |
| tx-firehose2.log | 101643 | 124.6 | 386 | 61% | 96.7 s |
| tx-firehose3.log | 54608 | 106.5 | 381 | 65% | 91.4 s |

`tx-firehose1.log` ran 1167 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
`tx-firehose2.log` ran 816 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
`tx-firehose3.log` ran 513 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}

## Optimistic forging (no reapplyTxs), load ramped 1 → 2 → 3 generators

Generators added at 300 s and 600 s. Medians per phase, first 60 s of each phase
dropped so the 60 s rate windows have settled.

| phase | confirmed | submitted | block delay | partition-mempool | CPU |
| --- | --- | --- | --- | --- | --- |
| 1 generator | 237.4 tx/s | 204.0 | 0.51 s | 0.101 s | 8% |
| 2 generators | 323.3 tx/s | 251.7 | 0.63 s | 0.171 s | 11% |
| 3 generators | 466.7 tx/s | 280.0 | 0.51 s | 0.182 s | 10% |

Against the previous three-generator run, which had `reapplyTxs`:

| | with `reapplyTxs` | optimistic |
| --- | --- | --- |
| `partition-mempool` p50 | 0.94–1.06 s | **0.10–0.18 s** |
| block delay at peers | 1.73–1.85 s | **0.51–0.63 s** |
| slots missed | 21 / 13 / 12 | **0 / 0 / 4** |
| forks / extensions | 5–9 of 156 | 2 of 59 |
| txs per certified EB | 6,115 (44%) | 5,466 (39%) |

Snapshot cache: **19 hits, 0 misses** — every snapshot request matched the cached
ledger state, which is why the partition cost collapsed. Note the cache is only
consulted on the no-certificate branch, so 19 requests against 62 blocks is
expected, not a shortfall.

Confirmed throughput is measured from `cumulativeTxBytes`, not
`txsProcessedNum` — see the correction in `../../BASELINE.md`.

### Caveat on the 467 tx/s

In phase 3 confirmed (466.7) exceeds submitted (280.0), which means the chain was
draining a backlog built up in the earlier phases rather than keeping pace with
live submission. Mempools sat at ~31k on the entry relay throughout. So 467 tx/s
is a drain rate, not a demonstrated sustainable one; a steady-state figure needs a
run long enough for the mempools to stop shrinking.
