# Report on the double-buffered mempool, and bounding forge-loop work

Scope: the mempool congestion fix — the **double-buffered mempool**, which lets a node ingest and serve transactions while it resyncs against a new ledger state — and a characterization of how much a quick forge loop matters, obtained by bounding the work done there.

Measured on `demo/dozen-devnet`: 3 block producers × 3 private relays, relays fully meshed, 10 ms one-way delay, 50 Mbps per node, `V2LSM`, minimum-size transactions (228 B on the wire). All figures from a 16-core/32-thread host at ~10% CPU, so they are protocol numbers rather than host numbers; earlier attempts on a saturated 16-core box are excluded. Per-run digests in `demo/dozen-devnet/results/`, narrative in `demo/dozen-devnet/BASELINE.md`.

## Results against the issue's targets

| | target | measured | |
| --- | --- | --- | --- |
| end-to-end, on chain | 50 TxkB/s | **106 kB/s** | **2.1×** |
| ingest / mempool | ~100 TxkB/s (speculated sufficient) | **139 kB/s** | **met** |

**Both targets are met**, and the speculation that ~100 TxkB/s of ingest would suffice to sustain 50 TxkB/s end-to-end holds with room to spare — 139 kB/s of ingest produced 106 kB/s on chain, a **76% conversion** rather than the ~50% the speculation implicitly allowed for. Ingest is no longer the binding constraint; §4 shows what is.

## What was measured, and in what order

Four configurations. Only the second is the semantic change; the third is deliberately a hack, and the fourth removes a bound to see what it was worth.

| run | mempool | forge loop |
| --- | --- | --- |
| **baseline** | upstream `leios-prototype` | `reapplyTxs` |
| **double-buffered** | `31bc7e863` on top of `leios-prototype`, [readers/adders decoupled from revalidation](https://github.com/IntersectMBO/ouroboros-consensus/pull/2148) | `reapplyTxs` |
| **forge bounded** | double-buffered | *hack*: [optimistic `getSnapshot`, no `reapplyTxs`](https://github.com/IntersectMBO/ouroboros-consensus/pull/2094) |
| **depth unbounded** | double-buffered, *hack*: `MempoolTimeoutsEnabled: false` | *hack* |

## 1. The double-buffered mempool

### Against the baseline

It does what it is designed to do — readers and adders proceed while the mempool resyncs — and that is directly visible:

| | baseline | double-buffered |
| --- | --- | --- |
| remote node mempool depth, peak | ~19,200 | **27,015** (+41%) |
| entry : remote depth ratio | 3.27× | **2.79×** |
| generator burst rate (busy-second p50) | ~330 tx/s | **401 tx/s** |
| entry relay time in add gaps > 0.5 s | 41.0% | 39.0% |
| entry relay admission ceiling | 34,416 txs | 33,957 |

The clearest single observation: **during the initial fill all twelve mempools tracked the entry node exactly** — every node at 25,536 transactions — which never happened on the baseline, where remotes sawtoothed at a third of the entry node's depth. Remote mempools stopped being the thing that could not keep up.

Deliberately, **no on-chain throughput figure is quoted for this comparison** — for that, see the screenshots posted in the issue. The table above is entirely mempool-side, from logs and depth gauges.

### Ingest scales with injection points

This is the series that establishes the ingest number. Peak N2N accept rate per relay, raising the number of `tx-firehose` entry points, against the speculated ~100 TxkB/s:

| injection points | peak ingest | in target units | vs ~100 TxkB/s |
| --- | --- | --- | --- |
| 1 | 261 tx/s | 60 kB/s | short |
| 2 | 520 tx/s | **119 kB/s** | **met** |
| 3 | 611 tx/s | **139 kB/s** | **met** |

A single entry point cannot reach the target — 60 kB/s is well short — so **the ingest target is met by topology, not by raw per-node speed.** Two entry points are enough; the third adds 20 kB/s, so scaling is clearly sub-linear and a fourth would likely add little.

The 2-point run separates the mechanism cleanly: ingest is governed by a node's **distance from an injection point**. Relays peering with both origins reached 511–520 tx/s, block producers with one origin in their own relay group 436 and 383, and bp3 — the only node with no origin among its peers — sat at 261 until its group got one, then 405. A node that *becomes* an origin sees its N2N ingest fall (relay31 519 → 293), since it is fed over N2C instead.

This also corrects an earlier reading of the same data: per-node ingest is **not** a fixed ceiling. Three-peer producers matching nine-peer relays at 261 tx/s looked like degree-independence; it was a single-origin supply limit, and adding an origin doubled it.

### What it did not move, and correctly so

The entry-node admission ceiling — that is the validation-time capacity, whose placement §3 argues about — and per-node ingest in the single-origin case, which is a supply-side property of the topology rather than a mempool limit.

## 2. Bounding forge-loop work

[PR 2094](https://github.com/IntersectMBO/ouroboros-consensus/pull/2094) (optimistic `getSnapshot`, dropping `reapplyTxs`) is **a hack, not a fix** — it skips revalidation rather than relocating it. Its value is as a bounding experiment: it prices an efficient forge loop.

| | `reapplyTxs` | forge bounded |
| --- | --- | --- |
| `partition-mempool` p50 | 0.94–1.06 s (max 3.19) | **0.10–0.18 s** |
| block delay at peers | 1.73–1.85 s | **0.51–0.63 s** |
| slots missed (3 BPs) | 21 / 13 / 12 | **0 / 0 / 4** |
| forged vs adopted (bp1) | 24 / 22 | no loss |

Network accounts for ~0.02 s of that block delay at 10 ms one-way, so 1.8 s was production cost. **Forge time propagates straight into block delay, and block delay into missed slots and lost blocks.** With the loop bounded, on-chain throughput scaled with offered load for the first time — 54 → 74 → 106 kB/s across one, two and three injection points.

Skipping revalidation is not an option in production, since the ledger state really does move under the mempool. What the ~0.9 s prices is **taking the work off the critical path** (§3).

> [!NOTE]
> **Saving ~0.9 s is not the same as being fast.** There is no established budget, but a clear upper bound: the loop must not consume anything like the whole 1 s slot, because the block still has to be diffused afterwards. At 0.51–0.63 s it is already over half a slot. And once revalidation is gone the composition shifts — `forge-block` becomes the largest component at 0.427 s p50, nearly half a slot on its own, and it is not mempool work. Mempool work is necessary but not sufficient.
>
> `partition-mempool` also shows a p95 of **7.181 s** against a p50 of 0.333 s: the tail survives a healthy median, so any bound has to be stated on the tail.

## 3. The time bound is in the wrong place

The mempool's cumulative validation-time capacity (~5 s, admitting ~34,400 transactions at ~145 µs each) is a **security bound** — an adversary must not be able to make forging arbitrarily slow. That property is necessary, but it is expressed as a limit on *mempool depth*, which only bounds forge cost under the assumption that **the forge loop fully revalidates everything it takes**.

Attack the assumption, not by skipping revalidation but by **moving it off the critical path**: it runs inside the forge loop today, so a leader pays for it in its own slot; done in the background as the mempool syncs, the forge loop takes an already-revalidated snapshot. The security bound then belongs in the loop itself — [a time-capped forge loop](https://github.com/IntersectMBO/ouroboros-consensus/pull/2217) — after which mempool capacity is an ordinary throughput and memory decision rather than a proxy for worst-case forge cost.

Removing the depth limit alone (`MempoolTimeoutsEnabled: false`) shows how tightly the two are coupled today. Mempools grew to 107,904 — exactly the byte capacity, 25,033,728 / 232 — and **throughput did not improve while forge health regressed**: snapshot cache misses appeared (0 → 23%), `partition-mempool` widened to 0.077–0.620 s, slots missed went 0/0/4 → 11/11/9, block interval 19 → 23 s. The mechanism is the cache: a hit is free, a **miss recomputes and is O(mempool depth)**.

Read correctly this does *not* defend the depth limit — it shows the limit is currently the only thing bounding forge cost, which is exactly the coupling a time-capped loop breaks. Two consequences:

1. **Cap the loop first, then relax mempool capacity** — not the reverse, which is what was measured above.
2. **The cap must cover the recompute path.** A cache that is free on a hit and O(depth) on a miss still puts seconds into a leader slot, and the miss is what a time cap has to survive.

Moving revalidation off the critical path is the same move the double buffer already makes for readers and adders (§1). The remaining step is to take the forge loop out of its way too.

## 4. Where the ceiling actually is

With the forge loop bounded, throughput is set by protocol parameters — nothing in the mempool or the network path will move it:

```
maxTxsPerEb = (maxMsgLeiosBlockBytesSize - 5) / minEbItemBytesSize
            = (500000 - 5) / 36                        = 13,888 txs per EB
mean RB interval                              1/f      = 20 s
effective interval between certifying RBs  20 / e^(-(gap+1)·f)

  gap = 10  (LeiosDemoTypes.hs)   34.7 s  ->  401 tx/s   model
  gap = 14  (CIP)                 42.3 s  ->  328 tx/s   model

measured, directly                             106 kB/s
  converted at 259 B/tx                    ->  411 tx/s
```

Note the units: the model is naturally in tx/s (it counts EB slots), the measurement in bytes/s (`cumulativeTxBytes` off the ledger state at the tip). Bridging them needs the **259 B/tx** factor, which is measured but unexplained — so the agreement at `gap = 10` is good to ~3% *if that factor holds*. The 106 kB/s does not depend on it.

Announced EBs are **97% full** (p50 body 486,111 B of 500,000; 90% of 314 announcements above 90%), so there is nothing to win in EB construction.

## Open items

**`minCertificationGap` is 10 in the code, 14 per CIP** — `LeiosDemoTypes.hs:1163`. The ceiling is 401 tx/s with 10 and 328 with 14, an 18% difference; 411 is only reachable with 10, so every figure above is against the code's value, not the spec's.

**Block-producer mempool ingest is marginal for a full EB.** A producer forges every ~60 s (three sharing a 20 s interval), so it must refill 13,888 / 60 = **231 tx/s** into its own mempool between its own announcements. Measured BP mempool adds were **225–282 tx/s** — on the line. Depth is ample (34,400 is 2.5 full EBs); *rate* is the constraint, and it would need to roughly double if `maxTxsPerEb` were raised. This is where further ingest work would pay.

**Larger transactions raise bytes/s, then plateau.** The EB body holds `(hash, size)` pairs at 36 B per transaction regardless of size, so `maxTxsPerEb` — and therefore tx/s — is size-independent. Bytes/s scales linearly until `maxEBClosureSize` (12 MB) takes over at **864 B per transaction**, close to the mainnet median:

| tx size | txs/EB | tx/s | bytes/s | binding limit |
| --- | --- | --- | --- | --- |
| 228 B (measured) | 13,888 | 401 | 104 kB/s | `maxTxsPerEb` |
| 864 B | 13,888 | 401 | **346 kB/s** | crossover |
| 1000 B | 12,000 | 346 | 346 kB/s | `maxEBClosureSize` |
| 2000 B | 6,000 | 173 | 346 kB/s | `maxEBClosureSize` |

At mainnet-median sizes the two EB limits are balanced and byte throughput plateaus at ~346 kB/s — **~7× the 50 TxkB/s target**. Worth running: `tx-firehose --outputs-per-tx` to reach ~900 B exercises `resolveAndApplyLeiosClosure` over a 12 MB closure instead of 3.2 MB, untested at that volume, and puts ~25 Mbit/s of EB fan-out against the 50 Mbps per-node cap.

**Certification rate** is the remaining gap to the full-EB ceiling — not EB fill.

## Measurement caveats

Two conclusions were retracted during this work, both the same error: treating a node-local trace count, or agreement between nodes, as a chain-level quantity. They are kept in `BASELINE.md` with the flawed reasoning named.

- **A "261 tx/s per-node ingest ceiling"** — see §1, corrected by the injection-point series.
- **"EBs are only ~40% full."** The denominator was per-node `Certified` trace lines over a node's whole lifetime against a numerator from a 17-minute window. `ebBodySize` is traced directly and says 97%.
- **`txsProcessedNum` as on-chain throughput.** It counts only *that node's* mempool removals, so a transaction confirmed in an EB the node never fetched is never counted — it read 235 tx/s where the ledger said 341. Any on-chain number in an earlier draft came from it and should be disregarded.

**On-chain throughput here is quoted in bytes/s, deliberately.** The only trustworthy source is `cardano_node_metrics_cumulativeTxBytes_int`, read from the ledger state at the tip and identical across all producers. Converting to tx/s requires the ledger accounting **259 B** per 228 B on-wire transaction; that 31 B discrepancy is unexplained, so every tx/s figure inherits it. Ingest figures are converted at the on-wire 228 B.

Peaks are not sustained rates. Where confirmed exceeds submitted the chain was draining backlog — the 3-generator 106 kB/s in the forge-bounded run is partly that; the 2-generator 106 kB/s in the depth-unbounded run is not.
