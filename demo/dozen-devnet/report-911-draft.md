# Report on the double-buffered mempool, and bounding forge-loop work

Scope: the mempool congestion fix — the **double-buffered mempool**, which lets a node ingest and serve transactions while it resyncs against a new ledger state — and a characterization of how much a quick forge loop matters, obtained by bounding the work done there.

Measured on `demo/dozen-devnet`: 3 block producers × 3 private relays, relays fully meshed, 10 ms one-way delay, 50 Mbps per node, `V2LSM`, minimum-size transactions (228 B on the wire). All figures from a 16-core/32-thread host at ~10% CPU, so they are protocol numbers rather than host numbers; earlier attempts on a saturated 16-core box are excluded. Per-run digests in `demo/dozen-devnet/results/`, narrative in `demo/dozen-devnet/BASELINE.md`.

## Thesis

**Work on the critical path must be constant or logarithmic in mempool depth.** Everything measured here is a consequence of one place where it is linear.

The pattern is already proven in this codebase, twice over. Mempool *sync* is O(depth) — measured at **0.104 ms per transaction**, near-perfectly linear across all twelve nodes, so ~2.9 s at 28k txs and ~11 s at 108k — and it costs nothing, because the double-buffered mempool moved it **off the lock**. Meanwhile the forge loop's snapshot recompute is also O(depth) and is **on** the critical path, so it costs everything: `partition-mempool` runs 0.10–0.18 s at bounded depth and **p95 7.8 s** when depth is unbounded.

That single linear term propagates all the way out. A leader stalled seconds inside a mempool walk publishes late; a voter stalled the same way votes after the certifying block is already made — and an EB is certifiable only by the block *succeeding* its announcement, so a late vote is an EB lost outright. Withheld votes rise 7 → 27 → 91 with load, `tooLate` specifically **0 → 12 → 60**, certificates stop forming, and on-chain throughput falls even though EBs stay 97–98% full and the fork rate stays at 6%.

Seen this way, the mempool's validation-time capacity is not a tuning knob but a **workaround**: it caps depth precisely so that linear critical-path work stays affordable. The 5 s budget corresponds to ~34,400 txs, which is ~3.6 s of sync — just inside one inter-block window. That is why removing it causes congestion collapse rather than merely wasting memory, and why the fix is to make the critical path sublinear rather than to keep depth small on its behalf.

Concretely, the take itself is *already* cheap: `splitAfterTxSize` is O(log n) on the finger tree and materializes at most `maxTxsPerEb` transactions. The linear cost is the **snapshot recompute on a cache miss**, which revalidates the whole mempool inside the forge loop. Moving that off the critical path — the same move the double buffer made for readers and adders — is the remaining work, and §2 prices it at ~0.9 s per forge.

## What was measured, and in what order

Four configurations. Only the second is the semantic change; the third is deliberately a hack, and the fourth removes a bound to see what it was worth.

| run                 | mempool                                                | forge loop                                                    |
|---------------------|--------------------------------------------------------|---------------------------------------------------------------|
| **baseline**        | upstream `leios-prototype`                             | `reapplyTxs`                                                  |
| **double-buffered** | `31bc7e863` readers/adders decoupled from revalidation | `reapplyTxs`                                                  |
| **forge bounded**   | double-buffered                                        | *hack*: `506875bfe` optimistic `getSnapshot`, no `reapplyTxs` |
| **depth unbounded** | double-buffered, `MempoolTimeoutsEnabled: false`       | *hack*                                                        |

## 1. The double-buffered mempool
    
It does what it is designed to do — readers and adders proceed while the mempool resyncs — and that is directly visible:

| | baseline | double-buffered |
| --- | --- | --- |
| remote node mempool depth, peak | ~19,200 | **27,015** (+41%) |
| entry : remote depth ratio | 3.27× | **2.79×** |
| generator burst rate (busy-second p50) | ~330 tx/s | **401 tx/s** |
| entry relay time in add gaps > 0.5 s | 41.0% | 39.0% |
| entry relay admission ceiling | 34,416 txs | 33,957 |
| peak N2N ingest per node | ~261 tx/s | ~261 |

The clearest single observation: **during the initial fill all twelve mempools tracked the entry node exactly** — every node at 25,536 transactions — which never happened on the baseline, where remotes sawtoothed at a third of the entry node's depth. Remote mempools stopped being the thing that could not keep up.

What it did **not** move, and correctly so: the entry-node admission ceiling (that is the validation-time capacity, see §3) and per-node N2N ingest (not a mempool limit — it is a supply-side effect of how many injection points exist).

> [!IMPORTANT] **The end-to-end effect of the double buffer was not measured cleanly.** Both the baseline and double-buffered runs recorded on-chain throughput with `txsProcessedNum`, which counts *that node's mempool removals* and therefore misses any transaction confirmed in an EB the node never fetched — it read 235 tx/s where the ledger said 341. Prometheus is wiped on each re-init, so the corrected figure cannot be recovered for those two runs. Use `cardano_node_metrics_cumulativeTxBytes_int` (read from the ledger state at the tip, identical across all producers) if this comparison needs redoing.
>
> The mempool-side effects above are unaffected — they come from logs and depth gauges, not from that counter.

## 2. Bounding forge-loop work: the potential

`506875bfe` (optimistic `getSnapshot`, dropping `reapplyTxs`) is **a hack, not a fix** — it skips revalidation rather than making it cheap or concurrent. Its value here is as a bounding experiment: it shows what an efficient forge loop is worth, and the answer is a lot.

The forge loop's own call traces localize the cost. `partition-mempool` is the parent of the Leios and snapshot calls, whose durations sum to 0.12 s, so the remainder is the two `snapshotTake` walks over the mempool:

| | `reapplyTxs` | forge bounded |
| --- | --- | --- |
| `partition-mempool` p50 | 0.94–1.06 s (max 3.19) | **0.10–0.18 s** |
| `mempool-get-snapshot-for` | 0.008 s | 0.008 s |
| block delay at peers | 1.73–1.85 s | **0.51–0.63 s** |
| slots missed (3 BPs) | 21 / 13 / 12 | **0 / 0 / 4** |
| forged vs adopted (bp1) | 24 / 22 | no loss |
| snapshot cache | — | 19 hits, **0 misses** |

Network accounts for ~0.02 s of that block delay at 10 ms one-way, so 1.8 s was production cost. **Forge time propagates straight into block delay, and block delay into missed slots and lost blocks** — at 1.6 s of forge path the three producers missed 46 slots between them and bp1 lost 2 of the 24 blocks it forged; at 0.15 s they missed 4 and lost none.

With the forge loop bounded, throughput scaled with offered load for the first time — 54 → 74 → 106 kB/s of ledger transaction bytes across one, two and three injection points — and reached the protocol ceiling (§4).

**So this is the case for doing the work properly.** The measured prize is ~0.9 s per forge, and the mechanism that delivers it here is not acceptable in production; a real fix has to bound or parallelize the revalidation rather than omit it.

> [!CAUTION] **~0.9 s saved is not the same as fast — the bounded forge loop still misses the target.** Against a ~0.2 s end-to-end forge budget, the bounded run's block delay of 0.51–0.63 s is roughly **3× over**, and with the depth bound also removed the top-level phases sum to 0.813 s at p50, **4.1× over**:
>
> | call (depth-unbounded run) | p50 | p95 | | --- | --- | --- | | `forge-block` | **0.427 s** | 1.142 s | | `partition-mempool` | 0.333 s | **7.181 s** | | `resolve-and-apply-leios-closure` | 0.103 s | 0.182 s | | `add-block-to-chaindb` | 0.053 s | 0.799 s | | `decide-leios-certifiy` | 0.036 s | 0.108 s |
>
> Two things follow. **The composition shifts once revalidation is gone**: `forge-block` becomes the single largest component at 0.427 s — more than twice the entire budget on its own — and it is not mempool work. Reaching 0.2 s needs attention there as well, so mempool work is necessary but not sufficient.
>
> And `partition-mempool`'s p95 of **7.181 s** against a p50 of 0.333 s shows the tail survives a healthy median. A budget stated as an average can be met while individual leader slots are still lost, so the bound has to be on the tail.

## 3. The bound has to cover the recompute path too

`MempoolTimeoutsEnabled: false` disables the mempool's cumulative validation-time capacity (~5 s, which admits ~34,400 transactions at the measured ~145 µs each). Mempools then grew to **107,904** — exactly the byte capacity, 25,033,728 / 232 — and **throughput did not improve while forge health regressed**:

| | depth bounded (~34k) | unbounded (~108k) |
| --- | --- | --- |
| snapshot cache | 19 hits, **0 misses** | 17 hits, **5 misses (23%)** |
| `partition-mempool` | 0.10–0.18 s | **0.077–0.620 s** |
| slots missed | 0 / 0 / 4 | **11 / 11 / 9** |
| block interval | ~19 s | **23.0 s** |
| best-phase throughput | 106 kB/s | 106 kB/s |

The mechanism is the snapshot cache. A hit returns the cached snapshot untouched; a **miss recomputes it, and the recompute is O(mempool depth)**. Deeper mempools make misses both more likely and three times more expensive — so the optimistic snapshot's cost is not depth-independent, it is merely *zero on the happy path*.

Two consequences for the issue's "time and size-bound revalidation work in the Forge loop" item:

1. The bound must apply to the **recompute path**, not just the happy path. A cache that is fast when it hits and unbounded when it misses still puts seconds into a leader slot.
2. The mempool's validation-time capacity is a **governor, not an obstacle**. It was bounding the cost of a cache miss, and removing it cost forge health for no throughput gain. It should stay on.

## 4. Where the ceiling actually is

With the forge loop bounded, throughput is set by protocol parameters — nothing in the mempool or the network path will move it:

```
maxTxsPerEb = (maxMsgLeiosBlockBytesSize - 5) / minEbItemBytesSize
            = (500000 - 5) / 36                        = 13,888 txs per EB
mean RB interval                              1/f      = 20 s
effective interval between certifying RBs  20 / e^(-(gap+1)·f)

  gap = 10  (LeiosDemoTypes.hs)   34.7 s  ->  401 tx/s  (104 kB/s)
  gap = 14  (CIP)                 42.3 s  ->  328 tx/s  ( 85 kB/s)

measured                                       411 tx/s  (106 kB/s)
```

Announced EBs are **97% full** (p50 body 486,111 B of 500,000; 90% of 314 announcements above 90%), so there is nothing to win in EB construction. Against the issue's target of 50 TxkB/s, the measured 106 kB/s is **2.1×**.

## Open items

**`minCertificationGap` is 10 in the code, 14 per CIP** — `LeiosDemoTypes.hs:1163`. The ceiling is 401 tx/s with 10 and 328 with 14, an 18% difference; 411 is only reachable with 10, so every figure above is against the code's value, not the spec's.

**Block-producer mempool ingest is marginal for a full EB.** A producer forges every ~60 s (three sharing a 20 s interval), so it must refill 13,888 / 60 = **231 tx/s** into its own mempool between its own announcements. Measured BP mempool adds were **225–282 tx/s** — on the line. Depth is ample (34,400 is 2.5 full EBs); *rate* is the constraint, and it would need to roughly double if `maxTxsPerEb` were raised. This is where further mempool ingest work would pay.

**Larger transactions raise bytes/s, then plateau.** The EB body holds `(hash, size)` pairs at 36 B per transaction regardless of size, so `maxTxsPerEb` — and therefore tx/s — is size-independent. Bytes/s scales linearly until `maxEBClosureSize` (12 MB) takes over at **864 B per transaction**, close to the mainnet median:

| tx size | txs/EB | tx/s | bytes/s | binding limit |
| --- | --- | --- | --- | --- |
| 228 B (measured) | 13,888 | 401 | 104 kB/s | `maxTxsPerEb` |
| 864 B | 13,888 | 401 | **346 kB/s** | crossover |
| 1000 B | 12,000 | 346 | 346 kB/s | `maxEBClosureSize` |
| 2000 B | 6,000 | 173 | 346 kB/s | `maxEBClosureSize` |

Worth running: `tx-firehose --outputs-per-tx` to reach ~900 B exercises `resolveAndApplyLeiosClosure` over a 12 MB closure instead of 3.2 MB, untested at that volume, and puts ~25 Mbit/s of EB fan-out against the 50 Mbps per-node cap.

**Certification rate** is the remaining gap to the full-EB ceiling — not EB fill.

## Measurement caveats

Three conclusions were retracted during this work, all the same error: treating a node-local trace count, or agreement between nodes, as a chain-level quantity. They are kept in `BASELINE.md` with the flawed reasoning named.

- **A "261 tx/s per-node ingest ceiling."** Three-peer producers matching nine-peer relays looked like degree-independence; it was a single-origin supply limit, and a second injection point doubled it (261 → 520 → 611).
- **`txsProcessedNum` as confirmed throughput** — see the note in §1.
- **"EBs are only ~40% full."** The denominator was per-node `Certified` trace lines over a node's whole lifetime against a numerator from a 17-minute window. `ebBodySize` is traced directly and says 97%.

Also: the ledger accounts **259 B** per 228 B on-wire transaction (measured as `cumulativeTxBytes / submitted_total` over a whole run). tx/s figures here use 259; the discrepancy is unexplained and worth confirming before quoting tx/s rather than bytes/s.

Peaks are not sustained rates. Where confirmed exceeds submitted the chain was draining backlog — the 3-generator 106 kB/s in the forge-bounded run is partly that; the 2-generator 106 kB/s in the depth-unbounded run is not.
