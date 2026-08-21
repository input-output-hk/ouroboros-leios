# Baseline: dozen-devnet throughput, pre-uncongestion mempool

Reference run for comparing the high-throughput ("uncongested") mempool against
the mempool currently on `leios-prototype`. Recorded 2026-08-21.

Everything here was measured on a devnet that was **not** CPU-bound (median 8%
busy on 32 threads), so the numbers are protocol and implementation limits rather
than host limits. An earlier attempt on a 16-core box ran at loadavg 24 / 90% CPU
and its numbers are not comparable — see [Earlier runs](#earlier-runs).

## Provenance

| | |
| --- | --- |
| host | AMD Ryzen 9 9950X3D, 16 cores / 32 threads, 60 GB |
| `cardano-node` | 11.1.0.164, git rev `d7faa517c581caa54619fb5aab9fc54856be459e` |
| built against | flake pin `ouroboros-consensus?ref=leios-prototype` (**not** the local checkout) |
| binary | `/nix/store/l0si36yq…-cardano-node-exe-cardano-node-11.1.0.164` |
| demo | `demo/dozen-devnet` at `ouroboros-leios` `a7338d2b4` |

> [!IMPORTANT]
> `cardano-node/cabal.project` points `../ouroboros-consensus` at a **local
> package**, so a `cabal` build picks up whatever branch that checkout is on. The
> nix-store binary does not — it uses the flake pin. When comparing, be explicit
> about which binary is on PATH, because the two differ in exactly the code under
> test. The node's own `gitRevision` identifies only `cardano-node` and will look
> identical either way.

## Configuration held constant

Topology: 3 block producers × 3 private relays, the nine relays fully meshed.
Only the block producers forge.

| | |
| --- | --- |
| `DELAY` | `10ms` one way (20 ms RTT), uniform on every edge |
| `RATE` | `50Mbps` per node uplink and downlink |
| `TPS` | `500`, one `tx-firehose` on `relay11` over N2C |
| tx size | 228 B measured on the wire |
| `LedgerDB.Backend` | `V2LSM` |
| `TxSubmissionLogicVersion` | `TxSubmissionLogicV2` |
| `MempoolCapacityBytesOverride` | `25000000` → reported capacity 25,033,728 B |
| `MempoolTimeout{Soft,Hard,Capacity}` | unset → node defaults **1 s / 1.5 s / 5 s** |

## Results

Sampled every 10 s for 15 minutes, slot 43 → 948.

| | min | median | max |
| --- | --- | --- | --- |
| CPU busy | 2% | **8%** | 46% |
| on chain (`txsProcessedNum_counter`) | 0 | **233.9 tx/s** | 490–533 |
| submitted (firehose) | 42 | **246.1 tx/s** | 383 |
| `relay11` mempool | 17,922 | 31,418 | **34,416 txs** |
| every other node's mempool | ~600 | ~9,600 | ~19,200 txs |

On-chain clears ~95% of what is offered. Leios carries the bulk of it: 88% of
confirmed transactions arrived in mempool-removal batches larger than one RB can
hold (395 txs at 90112 B / 228 B), largest observed batch 6,948 txs.

## Two distinct limits — do not conflate them

### 1. Entry-node mempool admission: a *time* budget, not bytes

`relay11` blocks at **34,416 txs / 7,984,512 B**, which is only 32% of the
reported byte capacity. The binding dimension is
`MempoolTimeoutCapacity` — see the third guard in
`Ouroboros/Consensus/Mempool/Update.hs`:

```haskell
| Just toCfg <- mbToCfg
, let MkTxMeasureWithDiffTime _txssz txsdifftime = currentSize
, not $ txsdifftime Measure.<= FiniteDiffTimeMeasure (mempoolTimeoutCapacity toCfg) ->
    NotEnoughSpaceLeft
```

> If the txs in the mempool took longer than this cumulatively to validate when
> each entered the mempool, then the mempool is at capacity.

`Mempool/API.hs` notes the reported capacity **excludes** this component, which
is why `mempoolBytes` and `cardano-cli query tx-mempool info` both look
comfortable while admission blocks.

So the ceiling is a **direct measurement of per-tx validation cost**:

```
per-tx validation time = MempoolTimeoutCapacity / ceiling_txs
                       = 5 s / 34,416 = 145 µs
```

Measured on `relay11` over a 180 s window of steady state. These came from
analysis run while the devnet was live; the run's logs were **not** archived (only
the `db/` trees were), so they cannot be recomputed — keep the `*.log` files next
time.

| | |
| --- | --- |
| adds | 41,802 in 180 s = **232.2/s** |
| add gap | p50 **2.5 ms**, p99 3 ms, max **66.74 s** |
| time in gaps > 0.5 s | **41.0%** of the window |
| `Mempool.Synced` events | 20 in 180 s |

Character of the stall, for recognising it again:

- A **blocking wait**, not a rejection — 180,680 firehose submits with zero
  rejects, and zero `Mempool.RejectedTx` on the node.
- **Node-specific.** Only the node the generators target reaches it. Every other
  node peaks at ~19.2k and never stalls, because their intake is bounded by the
  N2N limit below, not by local submission.
- Begins at a sharply reproducible size (last 8 stalls: 34,087–34,416 txs, 1%
  spread) — never at a time or a Leios event.
- Ends exactly when a block or certified EB frees space: `BlockAcquired` →
  `BlockTxsAcquired` → `RemoveTxs` → `Synced`, in 12 of 12 cases.
- **Not caused by the Leios cycle.** In one 34 s window the identical
  announce/acquire/certify sequence repeated four times with adds continuing
  throughout at 88–398/s.

### 2. Per-node N2N ingest ceiling ≈ 261 tx/s — the binding throughput limit

Peak `rate(txSubmission_txsAccepted_int)` over the run:

```
bp1     261.0    bp2     260.8    bp3     260.3      (3 peers each)
relay12 261.3    relay13 260.7    relay21 261.0
relay31 261.1    relay33 261.1                       (9 peers each)
relay22 251.6    relay23 248.7
```

Offered peaked at 383 tx/s in the same window and **36 of 81 samples exceeded
every node's ingest rate**, so this is a ceiling and not a reflection of demand.

The three-peer block producers reach the *same* number as the nine-peer relays,
which rules out the per-peer tx-submission credit window — that would have given
the BPs a third of the throughput. It is a **per-node** limit. At 145 µs/tx the
add path alone would support ~6,900/s and CPU sat at 8%, so it is neither
validation cost nor the host. Prime suspect: the single tx-submission decision
loop per node in `TxSubmissionLogicV2`.

The generators' target node reads 0 here — it ingests over N2C, which does not go
through tx-submission at all, and is therefore the only node that can exceed 261
and the only one that reaches limit 1.

Two cheap discriminators, each answering a different question:

1. Widen `TxDecisionPolicy` (`maxNumTxIdsToRequest` 6→30, `maxUnacknowledgedTxIds`
   10→30, `interTxSpace` 0.25→0.05). Moves the ceiling if it is
   aggregate-window-bound; does not if it is the decision loop's own throughput.
   Note the policy is hardcoded in `cardano-diffusion`'s `NodeToNode.hs`, not
   exposed in config.
2. `TxSubmissionLogicVersion: TxSubmissionLogicV1`. A different ceiling implicates
   the V2 decision logic specifically.

## Comparing the uncongested mempool against this

Hold everything in [Configuration](#configuration-held-constant) constant and
change only the binary:

```shell
cd ~/code/iog/cardano-node
cabal build cardano-node                     # picks up ../ouroboros-consensus
mkdir -p /tmp/pathshim && ln -sf "$(cabal list-bin cardano-node)" /tmp/pathshim/
cd ~/code/iog/ouroboros-leios/demo/dozen-devnet
PATH=/tmp/pathshim:$PATH ./run.sh            # shadows the nix-store binary
```

Confirm the right binary is live before trusting the run — `command -v
cardano-node` and the `Version.NodeVersion` line in a node log.

**Primary metric: the entry node's ceiling**, which is per-tx validation cost in
disguise. Same 5 s budget, same host, so the ratio of ceilings is the inverse
ratio of validation cost. Report `5 s / ceiling_txs` alongside it.

**Secondary:** whether on-chain throughput actually rises. It may not, and that
would be the interesting result — if the entry node stops being the constraint,
the ~261 tx/s per-node N2N ceiling becomes binding, and one generator at ~330
tx/s would then outrun every remote node. Watch the *gap* on the "Submission vs.
ingest" panel rather than the mempool depth.

**What should not change:** the N2N ceiling. It is not a mempool limit, and if it
moves, something else changed too — check the binary and config before believing
it.

## Earlier runs

Same demo, earlier conditions. Included only to show which knobs moved the
number; not comparable to the baseline above.

| conditions | on chain |
| --- | --- |
| 100 ms one-way, 16 cores, 2 generators, CPU 90% | 33.4 tx/s |
| 20 ms one-way, 16 cores, 1 generator, CPU ~50% | 78 tx/s |
| **10 ms one-way, 16C/32T, 1 generator, CPU 8%** | **233.9 tx/s** |

The 16-core runs were partly host-bound: the entry-node ceiling there was ~13k
txs, i.e. 5 s / 13,354 = 374 µs per tx against 145 µs here. Same code, 2.6× the
validation cost, purely from CPU contention — which is also the reason the
ceiling is only meaningful with a CPU figure beside it.

## Result: uncongested mempool measured against this

Same host, same config, same 15-minute protocol; only the binary differs
(`cabal build` against `ouroboros-consensus` `ch1bo/high-throughput-mempool`
`aa8bbf300` — off-lock sync, delta reapply, removal-generation ratchet).

| | baseline | uncongested |
| --- | --- | --- |
| CPU median | 8% | 8% |
| **on chain, median** | **233.9 tx/s** | **234.8 tx/s** |
| submitted, median | 246.1 tx/s | 235.5 tx/s |
| entry node median / max depth | 31,418 / 34,416 | 29,579 / 33,957 |
| other nodes median / max depth | ~9,600 / ~19,200 | 10,608 / 27,015 |
| entry : others depth ratio | 3.27× | 2.79× |
| peak N2N ingest, per node | ~261 tx/s | ~261 tx/s |
| firehose busy-second rate | ~330 tx/s | 401 tx/s |
| relay11 time in add gaps > 0.5 s | 41.0% | 39.0% |

**End-to-end throughput is unchanged, and that is the expected result.** The
per-node N2N ingest ceiling did not move — it is not a mempool limit — so it
became the binding constraint the moment the entry node stopped being one.
Prediction from the section above, confirmed.

**The remote nodes improved.** Peak depth +41%, the entry-to-remote ratio
narrowed, and during the initial fill all twelve mempools tracked the entry node
*exactly* (all at 25,536 txs), which never happened on the baseline. The mempool
is no longer what holds them back.

**The entry-node ceiling did not move**: 33,957 vs 34,416 txs, i.e. 147 µs vs
145 µs per tx. So the ceiling is the wrong metric for *this* change — it inverts
to per-tx **validation** cost, whereas this work targets lock hold time and sync
behaviour. Expect it to move only for a change that makes applying a transaction
cheaper.

Next: the binding limit is tx-submission, not the mempool. Either discriminator
from [limit 2](#2-per-node-n2n-ingest-ceiling--261-txs--the-binding-throughput-limit)
applies, and a second injection point (`TxFirehose2`, already wired to `relay21`
with `delegator2`, one control-API call) tests whether ~261 caps the network or
only caps diffusion to a given node: two entry nodes each need to pull only the
other's share, so they should cope, while the block producers inject nothing
locally and should stay pinned at ~261 — which would hold on-chain flat while
offered doubles.
