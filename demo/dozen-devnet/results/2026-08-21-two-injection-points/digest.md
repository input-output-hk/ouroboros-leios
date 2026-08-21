# Two-injection-point run — digest

Raw logs discarded; this is what was extracted from them. Sampler TSV and
provenance.txt are kept alongside.

## Mempool add path, per node

| node | adds | adds/s | p50 gap | p99 gap | max gap | stalled | peak depth |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bp1 | 346717 | 285.8 | 0.4 ms | 19 ms | 49.9 s | 16% | 34267 |
| bp2 | 288469 | 237.8 | 0.5 ms | 21 ms | 48.0 s | 13% | 33848 |
| bp3 | 281521 | 232.1 | 0.5 ms | 22 ms | 4.5 s | 1% | 30108 |
| relay11 | 314318 | 249.4 | 2.4 ms | 4 ms | 69.6 s | 56% | 33372 |
| relay12 | 376667 | 310.5 | 0.4 ms | 16 ms | 50.9 s | 31% | 35791 |
| relay13 | 376361 | 310.2 | 0.5 ms | 16 ms | 51.1 s | 30% | 36009 |
| relay21 | 292487 | 236.4 | 2.4 ms | 4 ms | 68.9 s | 58% | 33867 |
| relay22 | 375555 | 309.6 | 0.4 ms | 17 ms | 51.0 s | 30% | 36489 |
| relay23 | 377671 | 311.3 | 0.4 ms | 16 ms | 51.1 s | 30% | 36495 |
| relay31 | 375917 | 309.9 | 0.4 ms | 16 ms | 51.0 s | 30% | 36502 |
| relay32 | 375241 | 309.4 | 0.4 ms | 17 ms | 51.2 s | 30% | 36464 |
| relay33 | 172780 | 337.3 | 0.4 ms | 17 ms | 27.0 s | 25% | 36479 |

## Generators

| generator | txs | avg tx/s | busy-second p50 | zero-seconds | max gap | span |
| --- | --- | --- | --- | --- | --- | --- |
| tx-firehose1.log | 208336 | 165.3 | 392 | 53% | 69.6 s | 1260 s |

`tx-firehose1.log` non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}

| tx-firehose2.log | 190470 | 153.9 | 392 | 55% | 68.9 s | 1237 s |

`tx-firehose2.log` non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}


## Run summary (from `sampler.tsv`, 72 samples, slot 39 → 780)

| | min | median | max |
| --- | --- | --- | --- |
| CPU busy | 3% | 11% | 54% |
| disk free | 11 GB | 15 GB | 17 GB |
| on chain | 0 | 238.1 tx/s | 646.7 |
| submitted | 0 | 297.3 tx/s | 705.5 |

Peak N2N ingest per node, which is the result this run exists for:

```
relay32 520.0  relay31 519.3  relay23 511.7  relay12 511.5
relay33 511.3  relay13 511.2  relay22 511.1              (2 origin neighbours)
bp1     435.9  bp2     383.2                             (1 origin neighbour)
bp3     260.7                                            (0)
relay11 215.4  relay21 157.9                             (are the origins; N2C fed)
```

`blocksForged`: bp1 12, bp2 12, bp3 17 — bp3's shallower mempool is its own
forging draining it, not a failure to keep up.

## Caveats

- The run was at 100% disk by the end. Nodes were still alive when sampling
  finished, but the previous run died mid-write at the same wall, so treat the
  tail with suspicion.
- `submitted` and `on chain` swing hard between fill and drain phases; medians
  are the honest figure, peaks are not sustained rates.
