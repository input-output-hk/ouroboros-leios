# Run digest

Extracted from the node and generator logs, which were then discarded.
`sampler.tsv` and `provenance.txt` sit alongside.

## Mempool add path, per node

| node | adds | adds/s | p50 gap | p99 gap | max gap | stalled | peak depth |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bp1 | 415163 | 230.0 | 0.5 ms | 20 ms | 53.2 s | 15% | 34309 |
| bp2 | 439580 | 243.0 | 0.5 ms | 20 ms | 32.7 s | 13% | 34808 |
| bp3 | 396290 | 219.3 | 0.5 ms | 21 ms | 28.7 s | 5% | 33659 |
| relay11 | 398794 | 224.1 | 2.4 ms | 4 ms | 89.1 s | 55% | 34069 |
| relay12 | 476753 | 263.7 | 0.5 ms | 19 ms | 43.3 s | 21% | 34977 |
| relay13 | 477330 | 263.4 | 0.4 ms | 19 ms | 45.5 s | 24% | 34969 |
| relay21 | 431913 | 238.3 | 1.6 ms | 18 ms | 50.3 s | 40% | 33956 |
| relay22 | 478570 | 263.8 | 0.5 ms | 19 ms | 43.5 s | 23% | 34213 |
| relay23 | 475391 | 262.4 | 0.5 ms | 19 ms | 40.3 s | 18% | 34800 |
| relay31 | 315135 | 245.2 | 0.6 ms | 19 ms | 43.4 s | 23% | 34679 |
| relay32 | 473786 | 261.3 | 0.5 ms | 19 ms | 44.0 s | 20% | 34779 |
| relay33 | 469274 | 258.7 | 0.5 ms | 19 ms | 44.8 s | 22% | 34478 |

## Generators

| generator | txs | avg tx/s | busy-second p50 | zero-seconds | max gap |
| --- | --- | --- | --- | --- | --- |
| tx-firehose1.log | 298439 | 167.7 | 394 | 53% | 89.1 s |
| tx-firehose2.log | 179469 | 146.8 | 391 | 57% | 50.3 s |
| tx-firehose3.log | 17151 | 184.0 | 386 | 45% | 26.1 s |

`tx-firehose1.log` ran 1780 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1, 'TxF': 1}
`tx-firehose2.log` ran 1223 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}
`tx-firehose3.log` ran 93 s; non-Success events: {'TxFirehose.Startup.Query': 1, 'TxFirehose.Startup.Seeded': 1}

## Forge loop, by call stack

A leader slot runs the whole tree; a non-leader slot stops after the
leadership check, so `n` differs between rows by design.

| stack | n | p50 | p95 | max |
| --- | --- | --- | --- | --- |
| &nbsp;&nbsp;&nbsp;&nbsp;add-block-to-chaindb | 90 | 0.391 s | 0.721 s | 1.525 s |
| &nbsp;&nbsp;&nbsp;&nbsp;partition-mempool | 90 | 0.306 s | 1.086 s | 1.745 s |
| &nbsp;&nbsp;&nbsp;&nbsp;forge-block | 90 | 0.279 s | 0.607 s | 1.497 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;resolve-and-apply-leios-closure | 56 | 0.096 s | 0.139 s | 0.435 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;decide-leios-certifiy | 90 | 0.011 s | 0.041 s | 0.119 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;mempool-get-snapshot-for-no-cache | 56 | 0.005 s | 0.006 s | 0.023 s |
| forge | 5634 | 0.000 s | 0.001 s | 2.586 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-is-leader-proof | 5634 | 0.000 s | 0.001 s | 0.016 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-ticked-ledger-state | 90 | 0.000 s | 0.000 s | 0.000 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;mempool-get-snapshot-for | 34 | 0.000 s | 0.026 s | 0.036 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-ledger-view | 5634 | 0.000 s | 0.000 s | 0.003 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-block-context | 5634 | 0.000 s | 0.000 s | 0.001 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-ticked-chain-dep-state | 5634 | 0.000 s | 0.000 s | 0.001 s |

## Endorser blocks

87 EBs forged across the block producers.

| | txs | % of maxTxsPerEb | body bytes |
| --- | --- | --- | --- |
| p50 | 13888 | 100% | 499968 |
| p95 | 13888 | 100% | 499968 |
| max | 13888 | 100% | 499968 |

67/87 over 90% full (maxTxsPerEb = 13888).

### Votes withheld

222 votes cast, 35 withheld — 14% of opportunities.

| reason | n |
| --- | --- |
| `chainTipDoesNotAnnounce` | 35 |

85 distinct EBs announced, 84 certifying blocks seen — 99%.

Certification cannot reach 100%: an EB is only certifiable by an RB at
least `minCertificationGap` slots after the announcing one, so with
Poisson block arrival a share of announcements never gets a qualifying
slot. That share, not EB fill, is the gap to the full-EB ceiling.

## Phase breakdown, and the pair comparison

Derived in-session; `digest.py` reports run totals only. Paired with
`../2026-08-22-phased-depth-unbounded`, which differs in one flag:
`MempoolTimeoutsEnabled`.

| | ingest | on chain | blocks | kB/block | depth | lost |
| --- | --- | --- | --- | --- | --- | --- |
| unbounded, 1 gen | 78.2 | 77.6 | 19 | 1921 | 107,904 | 1 |
| unbounded, 2 gen | 155.5 | 64.1 | 28 | 1281 | 107,904 | 3 |
| unbounded, 3 gen | 196.5 | **51.8** | 27 | 1094 | 107,904 | 3 |
| bounded, 1 gen | 78.2 | 66.6 | 20 | 1866 | 33,872 | 0 |
| bounded, 2 gen | 156.0 | 88.3 | 28 | 1767 | 33,559 | 2 |
| bounded, 3 gen | 186.7 | **96.6** | 29 | 1866 | 33,773 | 2 |

Bounded scales monotonically up, unbounded monotonically down. At three
generators bounded delivers 86% more, and 1.93x the 50 TxkB/s target.

`kB/block` is the clearest line: flat under bound (1866 -> 1767 -> 1866) across a
2.4x load increase, down 43% without it (1921 -> 1094). Block counts are
near-identical, so the same inclusion opportunities deliver constant payload when
critical-path work is bounded and progressively less when it is not.

Why, end to end:

| | unbounded | bounded |
| --- | --- | --- |
| `partition-mempool` p50 | 0.333 s | 0.306 s |
| `partition-mempool` **p95** | **7.395 s** | **1.086 s** |
| votes withheld | 133 / 540 (25%) | 35 / 257 (14%) |
| `tooLate` | **78** | **0** |
| `chainTipDoesNotAnnounce` | 55 | 35 |
| EBs announced -> certified | 78% | **99%** |

Not one late vote in the whole bounded run. The p50s are indistinguishable — the
entire effect is in the tail, so a run reporting only medians would have called
the two configs identical.

An EB is certifiable only by the block succeeding its announcement, so a vote has
one inter-block interval to be produced and diffused. A 7 s forge tail eats that
window; a 1 s tail does not.

Trade, for the record: bounding depth costs 14% at one generator (66.6 vs 77.6)
and pays 86% at three (96.6 vs 51.8).
