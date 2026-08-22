# Run digest

Extracted from the node and generator logs, which were then discarded.
`sampler.tsv` and `provenance.txt` sit alongside.

## Mempool add path, per node

| node | adds | adds/s | p50 gap | p99 gap | max gap | stalled | peak depth |
| --- | --- | --- | --- | --- | --- | --- | --- |
| bp1 | 292563 | 127.9 | 0.6 ms | 19 ms | 950.4 s | 61% | 28031 |
| bp2 | 275388 | 120.4 | 0.6 ms | 19 ms | 950.3 s | 61% | 28717 |
| bp3 | 278818 | 121.9 | 0.6 ms | 19 ms | 950.3 s | 61% | 28562 |
| relay11 | 308739 | 131.7 | 0.9 ms | 3 ms | 1005.6 s | 83% | 29430 |
| relay12 | 371094 | 162.2 | 0.5 ms | 13 ms | 950.4 s | 72% | 30744 |
| relay13 | 370508 | 161.9 | 0.5 ms | 13 ms | 950.4 s | 72% | 30717 |
| relay21 | 290212 | 126.8 | 0.9 ms | 3 ms | 950.4 s | 84% | 30211 |
| relay22 | 370787 | 161.8 | 0.5 ms | 13 ms | 950.4 s | 72% | 30586 |
| relay23 | 371463 | 162.1 | 0.5 ms | 13 ms | 950.4 s | 72% | 30720 |
| relay31 | 302261 | 131.9 | 0.9 ms | 3 ms | 950.4 s | 83% | 30240 |
| relay32 | 372416 | 162.4 | 0.5 ms | 13 ms | 950.4 s | 72% | 30445 |
| relay33 | 372434 | 162.4 | 0.5 ms | 13 ms | 950.3 s | 72% | 30606 |

## Generators

| generator | txs | avg tx/s | busy-second p50 | zero-seconds | max gap |
| --- | --- | --- | --- | --- | --- |


## Forge loop, by call stack

A leader slot runs the whole tree; a non-leader slot stops after the
leadership check, so `n` differs between rows by design.

| stack | n | p50 | p95 | max |
| --- | --- | --- | --- | --- |
| &nbsp;&nbsp;&nbsp;&nbsp;partition-mempool | 112 | 0.603 s | 1.573 s | 3.254 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;resolve-and-apply-leios-closure | 33 | 0.202 s | 0.515 s | 0.820 s |
| &nbsp;&nbsp;&nbsp;&nbsp;forge-block | 112 | 0.129 s | 0.439 s | 0.610 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;mempool-get-snapshot-for-no-cache | 33 | 0.041 s | 0.108 s | 0.113 s |
| &nbsp;&nbsp;&nbsp;&nbsp;add-block-to-chaindb | 112 | 0.017 s | 1.071 s | 1.180 s |
| forge | 7027 | 0.001 s | 0.001 s | 4.455 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-is-leader-proof | 7027 | 0.000 s | 0.001 s | 0.039 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-ticked-ledger-state | 112 | 0.000 s | 0.000 s | 0.001 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-ledger-view | 7027 | 0.000 s | 0.000 s | 0.001 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-block-context | 7027 | 0.000 s | 0.000 s | 0.001 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;mempool-get-snapshot-for | 79 | 0.000 s | 0.000 s | 0.000 s |
| &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;decide-leios-certifiy | 112 | 0.000 s | 0.045 s | 0.061 s |
| &nbsp;&nbsp;&nbsp;&nbsp;get-ticked-chain-dep-state | 7027 | 0.000 s | 0.000 s | 0.001 s |

## Endorser blocks

62 EBs forged across the block producers.

| | txs | % of maxTxsPerEb | body bytes |
| --- | --- | --- | --- |
| p50 | 13679 | 98% | 492444 |
| p95 | 13888 | 100% | 499968 |
| max | 13888 | 100% | 499968 |

38/62 over 90% full (maxTxsPerEb = 13888).

### Votes withheld

172 votes cast, 14 withheld — 8% of opportunities.

| reason | n |
| --- | --- |
| `chainTipDoesNotAnnounce` | 14 |

62 distinct EBs announced, 60 certifying blocks seen — 97%.

Certification cannot reach 100%: an EB is only certifiable by an RB at
least `minCertificationGap` slots after the announcing one, so with
Poisson block arrival a share of announcements never gets a qualifying
slot. That share, not EB fill, is the gap to the full-EB ceiling.

## Run summary: transaction size as a throughput lever

Question: tx/s is capped by `maxTxsPerEb`, which is size-independent — the EB body
holds one (hash, size) pair per tx, 36 B, however big the tx is. So can byte
throughput be raised by making transactions larger instead of more numerous?

Answer: yes, but sub-linearly.

| | 232 B (1 output) | 652 B (5 outputs) | |
| --- | --- | --- | --- |
| on chain, sustained | 96.6 kB/s | **192.2 kB/s** | **1.99x** |
| tx/s | 416 | 295 | 0.71x |
| peak ingest | 187 kB/s | 666 kB/s | 3.6x |
| EB fill, p50 | 13,503 | 13,420 | flat, at the cap |
| inclusion (closures / leader slots) | ~54-60% | 53% (25/47) | flat |
| votes withheld | 14% | 8% | better |
| `tooLate` votes | 0 | 0 | |
| blocks lost | 2 | 0 | |
| block interval | 19.6 s | 21.1 s | |

192.2 kB/s is **3.8x the 50 TxkB/s target**. Naive size-independence predicts
2.81x (652/232); the shortfall is EB fill in *count* — the validation-time
capacity admits fewer expensive transactions, so mean fill drops 13,503 -> 11,285
even though p50 stays at the cap. Inclusion, vote timeliness and block rate are
all unchanged, so nothing about larger transactions stresses certification.

Throughput reconciles directly: 25 closures over 47 leader slots x 11,285 txs x
652 B / 21.1 s = 186 kB/s, against 190 measured.

### The forge path is linear in bytes, not just in depth

The finding worth keeping. Same host (idle, loadavg 3.3/32 cores), same node
build, same bounded mempool — only transaction size changed:

| call, p50 | 232 B | 652 B | |
| --- | --- | --- | --- |
| `partition-mempool` | 0.306 s | **1.183 s** | 3.9x |
| `add-block-to-chaindb` | 0.054 s | **0.416 s** | 7.7x |
| `resolve-and-apply-leios-closure` | 0.096 s | 0.201 s | 2.1x |
| `forge-block` | 0.279 s | 0.243 s | flat |
| sum | ~0.64 s | **~1.84 s** | ~2 slots |

Critical-path work is linear in the *bytes* the forge loop touches, not only in
mempool depth. So capping how many transactions sit in the mempool is not
sufficient — the snapshot walk and the ChainDB write both scale with size.

At ~1.84 s the forge path is back above half a slot. Votes are still on time
(`tooLate` = 0), but that headroom is what larger transactions are spending, and
it is the first thing to watch if size is pushed further.

### Where the remaining headroom is

- **Inclusion, ~53%**, is the biggest multiplier: closing it would roughly double
  throughput at any transaction size. It is the succeeding-block certification
  window, not the mempool.
- **Transaction size** still has room: at 652 B a p50 EB carries 8.8 MB against
  the 12 MB `maxEBClosureSize`, so ~865 B/tx would saturate it. The blocker is
  funding, not the protocol — each output needs min-ada against a fixed fee.
- **EB fill in count** falls as transactions get more expensive to validate,
  which is the validation-time capacity again.
