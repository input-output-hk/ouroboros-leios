# Run digest

Extracted from the node and generator logs, which were then discarded.
`sampler.tsv` and `provenance.txt` sit alongside.

## Mempool add path, per node

| node | adds | adds/s | p50 gap | p99 gap | max gap | stalled | peak depth |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bp1 | 285750 | 245.4 | 0.4 ms | 26 ms | 0.8 s | 0% | 64486 |
| bp2 | 363893 | 311.5 | 0.4 ms | 21 ms | 0.3 s | 0% | 96550 |
| bp3 | 365764 | 313.8 | 0.4 ms | 20 ms | 0.3 s | 0% | 95188 |
| relay11 | 220140 | 258.9 | 2.5 ms | 5 ms | 75.2 s | 40% | 107904 |
| relay12 | 387918 | 333.2 | 0.4 ms | 19 ms | 32.6 s | 11% | 107904 |
| relay13 | 387918 | 333.4 | 0.4 ms | 19 ms | 33.1 s | 11% | 107904 |
| relay21 | 348434 | 299.5 | 2.4 ms | 18 ms | 39.2 s | 26% | 107904 |
| relay22 | 387918 | 332.3 | 0.4 ms | 19 ms | 33.1 s | 12% | 107904 |
| relay23 | 387918 | 333.2 | 0.4 ms | 19 ms | 32.8 s | 11% | 107904 |
| relay31 | 387918 | 332.6 | 0.6 ms | 18 ms | 52.3 s | 27% | 107904 |
| relay32 | 374133 | 321.4 | 0.5 ms | 19 ms | 33.3 s | 7% | 107904 |
| relay33 | 387918 | 333.3 | 0.4 ms | 19 ms | 32.5 s | 11% | 107904 |

## Generators

| generator | txs | avg tx/s | busy-second p50 | zero-seconds | max gap |
| --- | --- | --- | --- | --- | --- |
| tx-firehose1.log | 190786 | 224.4 | 393 | 39% | 75.2 s |
| tx-firehose2.log | 195806 | 228.4 | 389 | 34% | 39.2 s |
| tx-firehose3.log | 81853 | 147.8 | 384 | 54% | 52.3 s |

`tx-firehose1.log` ran 850 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
`tx-firehose2.log` ran 857 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
`tx-firehose3.log` ran 554 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
