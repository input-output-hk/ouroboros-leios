# Run digest

Extracted from the node and generator logs, which were then discarded.
`sampler.tsv` and `provenance.txt` sit alongside.

## Mempool add path, per node

| node | adds | adds/s | p50 gap | p99 gap | max gap | stalled | peak depth |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bp1 | 249536 | 261.1 | 0.5 ms | 20 ms | 74.6 s | 18% | 32825 |
| bp2 | 246759 | 258.1 | 0.5 ms | 20 ms | 81.8 s | 15% | 32046 |
| bp3 | 270459 | 282.7 | 0.5 ms | 20 ms | 83.1 s | 13% | 33082 |
| relay11 | 253340 | 250.3 | 1.1 ms | 4 ms | 106.8 s | 65% | 32669 |
| relay12 | 323837 | 338.2 | 0.4 ms | 14 ms | 101.9 s | 39% | 34956 |
| relay13 | 215302 | 320.8 | 0.4 ms | 14 ms | 102.0 s | 45% | 34907 |
| relay21 | 258914 | 265.8 | 1.0 ms | 4 ms | 113.4 s | 65% | 33331 |
| relay22 | 325410 | 339.3 | 0.4 ms | 14 ms | 101.8 s | 39% | 34810 |
| relay23 | 311921 | 325.1 | 0.4 ms | 14 ms | 102.4 s | 40% | 34595 |
| relay31 | 288293 | 295.5 | 0.9 ms | 4 ms | 111.8 s | 62% | 33116 |
| relay32 | 328008 | 341.5 | 0.4 ms | 14 ms | 102.0 s | 39% | 35092 |
| relay33 | 327622 | 340.9 | 0.4 ms | 14 ms | 102.8 s | 39% | 34797 |

## Generators

| generator | txs | avg tx/s | busy-second p50 | zero-seconds | max gap |
| --- | --- | --- | --- | --- | --- |
| tx-firehose1.log | 126873 | 124.8 | 383 | 63% | 106.8 s |
| tx-firehose2.log | 124620 | 127.6 | 384 | 62% | 113.4 s |
| tx-firehose3.log | 134765 | 137.9 | 384 | 59% | 111.8 s |

`tx-firehose1.log` ran 1016 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
`tx-firehose2.log` ran 977 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
`tx-firehose3.log` ran 977 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}

## Run summary (from `sampler.tsv`, 90 samples, slot 75 -> 928)

| | min | median | max |
| --- | --- | --- | --- |
| CPU busy | 0.0 | 10.0 | 61.0 |
| disk free GB | 97.0 | 105.0 | 108.0 |
| on chain tx/s | 0.0 | 235.4 | 608.5 |
| submitted tx/s | 0.0 | 375.8 | 806.2 |

Peak N2N ingest per node, with the one- and two-origin runs for comparison:

| node | 1 origin | 2 origins | 3 origins |
| --- | --- | --- | --- |
| relay13 | 261 | 511.2 | **610.6** |
| relay32 | 261 | 520.0 | **610.1** |
| relay33 | 261 | 511.3 | **609.6** |
| relay23 | 261 | 511.7 | **609.4** |
| relay12 | 261 | 511.5 | **609.1** |
| relay22 | 261 | 511.1 | **607.7** |
| bp1 | 261 | 435.9 | **429.2** |
| bp3 | 261 | 260.7 | **405.3** |
| bp2 | 261 | 383.2 | **404.4** |
| relay11 | 261 | 215.4 | **320.5** |
| relay21 | 261 | 157.9 | **295.8** |
| relay31 | 261 | 519.3 | **293.4** |
