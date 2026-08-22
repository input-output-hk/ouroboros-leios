# Run digest

Extracted from the node and generator logs, which were then discarded.
`sampler.tsv` and `provenance.txt` sit alongside.

## Mempool add path, per node

| node | adds | adds/s | p50 gap | p99 gap | max gap | stalled | peak depth |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bp1 | 848820 | 214.0 | 0.4 ms | 28 ms | 35.6 s | 2% | 107904 |
| bp2 | 853629 | 215.2 | 0.5 ms | 22 ms | 90.6 s | 24% | 107904 |
| bp3 | 864364 | 218.1 | 0.5 ms | 23 ms | 102.5 s | 16% | 107904 |
| relay11 | 380253 | 250.9 | 2.5 ms | 5 ms | 64.8 s | 41% | 107904 |
| relay12 | 889767 | 224.3 | 0.4 ms | 20 ms | 117.3 s | 37% | 107904 |
| relay13 | 865639 | 227.0 | 0.4 ms | 20 ms | 117.0 s | 37% | 107904 |
| relay21 | 862962 | 217.5 | 1.6 ms | 18 ms | 110.8 s | 51% | 107904 |
| relay22 | 890845 | 224.6 | 0.4 ms | 19 ms | 109.3 s | 38% | 107904 |
| relay23 | 636173 | 235.5 | 0.4 ms | 20 ms | 79.6 s | 33% | 107904 |
| relay31 | 821553 | 207.1 | 1.1 ms | 19 ms | 120.0 s | 48% | 107904 |
| relay32 | 884368 | 222.9 | 0.4 ms | 20 ms | 107.9 s | 36% | 107904 |
| relay33 | 890825 | 224.5 | 0.4 ms | 19 ms | 117.9 s | 39% | 107904 |

## Generators

| generator | txs | avg tx/s | busy-second p50 | zero-seconds | max gap |
| --- | --- | --- | --- | --- | --- |
| tx-firehose1.log | 326038 | 215.1 | 393 | 40% | 64.8 s |
| tx-firehose2.log | 412650 | 126.0 | 384 | 59% | 110.8 s |
| tx-firehose3.log | 251618 | 94.1 | 377 | 68% | 120.0 s |

`tx-firehose1.log` ran 1516 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
`tx-firehose2.log` ran 3275 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
`tx-firehose3.log` ran 2675 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}

## Forge loop, by call stack

A leader slot runs the whole tree; a non-leader slot stops after the
leadership check, so `n` differs between rows by design.

| stack | n | p50 | p95 | max |
| --- | --- | --- | --- | --- |
| &nbsp;&nbsp;&nbsp;&nbsp;forge-block | 189 | 0.406 s | 0.935 s | 1.842 s |
| &nbsp;&nbsp;&nbsp;&nbsp;partition-mempool | 189 | 0.333 s | 7.395 s | 10.293 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;resolve-and-apply-leios-closure | 81 | 0.104 s | 0.158 s | 0.256 s |
| &nbsp;&nbsp;&nbsp;&nbsp;add-block-to-chaindb | 189 | 0.054 s | 0.775 s | 1.079 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;decide-leios-certifiy | 189 | 0.030 s | 0.055 s | 0.103 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;mempool-get-snapshot-for-no-cache | 81 | 0.006 s | 0.009 s | 0.015 s |
| forge | 11876 | 0.001 s | 0.001 s | 10.895 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-is-leader-proof | 11876 | 0.000 s | 0.001 s | 0.047 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-ticked-ledger-state | 189 | 0.000 s | 0.000 s | 0.000 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;mempool-get-snapshot-for | 108 | 0.000 s | 0.133 s | 0.344 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-ledger-view | 11876 | 0.000 s | 0.000 s | 0.007 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-block-context | 11876 | 0.000 s | 0.000 s | 0.003 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-ticked-chain-dep-state | 11876 | 0.000 s | 0.000 s | 0.001 s |

## Endorser blocks

187 EBs forged across the block producers.

| | txs | % of maxTxsPerEb | body bytes |
| --- | --- | --- | --- |
| p50 | 13503 | 97% | 486108 |
| p95 | 13888 | 100% | 499968 |
| max | 13888 | 100% | 499968 |

173/187 over 90% full (maxTxsPerEb = 13888).

### Votes withheld

407 votes cast, 133 withheld — 25% of opportunities.

| reason | n |
| --- | --- |
| `tooLate` | 78 |
| `chainTipDoesNotAnnounce` | 55 |

178 distinct EBs announced, 140 certifying blocks seen — 79%.

Certification cannot reach 100%: an EB is only certifiable by an RB at
least `minCertificationGap` slots after the announcing one, so with
Poisson block arrival a share of announcements never gets a qualifying
slot. That share, not EB fill, is the gap to the full-EB ceiling.
