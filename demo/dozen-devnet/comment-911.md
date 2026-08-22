## Where the mempool work stands

Putting numbers behind the graphs above, and recording what the paired experiments say. Treating this as an early validation rather than a conclusion: the prototype still has gaps — several Leios parameters are hardcoded rather than parameterized, and the forge loop still owes validation work — so what follows says more about shape and direction than about achievable limits.

Setup: `demo/dozen-devnet`, 3 block producers × 3 private relays with the nine relays fully meshed, 10 ms one-way delay, 50 Mbps per node, `TxSubmissionV2`, UTxO-HD `V2LSM`, minimum-size (228 B) transactions, on the 32-core machine at ~10% CPU. Digests and sampler output in `demo/dozen-devnet/results/2026-08-22-*`.

### Against the targets

| | target | measured | |
| --- | --- | --- | --- |
| consensus, on chain | 50 TxkB/s | **96.6 kB/s** | 1.9× |
| " , with ~652 B transactions | | **192.2 kB/s** | 3.8× |
| mempool / ingest | ~100 TxkB/s | **666 kB/s** | 6.7× |

Both targets are met. The ~100 TxkB/s ingest figure looks roughly 2× conservative — a single injection point already sustains 77.6 kB/s on chain at 99% conversion, so ingest stopped being the limiting term earlier than expected. With forge-loop validation still outstanding, read these as an upper bound on the current prototype rather than settled figures.

### The double buffer does what it is designed to do

This quantifies [the "more in sync" observation above](https://github.com/input-output-hk/ouroboros-leios/issues/911#issuecomment-5372640504), against [the baseline](https://github.com/input-output-hk/ouroboros-leios/issues/911#issuecomment-5370677604):

| | baseline | double-buffered |
| --- | --- | --- |
| remote mempool depth, peak | ~19,200 | **27,015** (+41%) |
| entry : remote depth ratio | 3.27× | **2.79×** |
| generator burst rate (busy-second p50) | ~330 tx/s | **401 tx/s** |
| entry relay time in add gaps > 0.5 s | 41.0% | 39.0% |

The sharpest single observation, matching "mempools coming more in sync": during the initial fill **all twelve mempools tracked the entry node exactly** — every node at 25,536 transactions — which never happened on the baseline, where remotes sawtoothed at a third of the entry node's depth. That is the same thing the baseline panel shows as "mempool throughput often at 0 despite capacity left": remote mempools were the thing that could not keep up, and they no longer are.

For on-chain throughput of that comparison, the graphs above are the record. My own numbers for it came from `txsProcessedNum`, which counts only *that node's* mempool removals and so misses any transaction confirmed in an EB the node never fetched — it understated by about a third. `cardano_node_metrics_cumulativeTxBytes_int`, read from the ledger state at the tip, is identical across producers and is the one to use.

Ingest scaling also matches "this does not give as much of a bump anymore" for the third entry point — peak N2N accept per relay went **261 → 520 → 611 tx/s** for one, two and three injection points. Worth noting *why*: ingest is governed by a node's distance from an injection point, not by peer count. In the two-point run, relays peering with both origins reached 511–520 tx/s while bp3 — the only node with no origin among its peers — sat at 261 until its group got one, then 405. So the ingest target is met by topology rather than by per-node speed. (This also corrects an earlier reading of mine: 261 tx/s was not a per-node ceiling, it was single-origin supply.)

### Bounding critical-path work is what actually moves throughput

Two paired runs, one flag apart (`MempoolTimeoutsEnabled`), three phases each of one/two/three injection points. `MempoolCapacityBytesOverride` = 25 MB, so with timeouts off the byte dimension binds at ~107,900 transactions instead of the ~34,400 the 5 s validation-time budget allows:

| | ingest | on chain | kB/block | depth | blocks lost |
| --- | --- | --- | --- | --- | --- |
| unbounded, 1 gen | 78.2 | 77.6 | 1921 | 107,904 | 1 |
| unbounded, 2 gen | 155.5 | 64.1 | 1281 | 107,904 | 3 |
| unbounded, 3 gen | 196.5 | **51.8** | 1094 | 107,904 | 3 |
| bounded, 1 gen | 78.2 | 66.6 | 1866 | 33,872 | 0 |
| bounded, 2 gen | 156.0 | 88.3 | 1767 | 33,559 | 2 |
| bounded, 3 gen | 186.7 | **96.6** | 1866 | 33,773 | 2 |

**Bounded scales monotonically up; unbounded monotonically down.** At three generators bounded delivers 86% more. Unbounded is not merely wasteful — it is congestion collapse: 2.5× the offered ingest produces a third *less* on chain.

`kB/block` is the cleanest line in the table. Block counts are near-identical between the two runs, so the same number of inclusion opportunities deliver constant payload when critical-path work is bounded (1866 → 1767 → 1866) and progressively less when it is not (1921 → 1094, −43%).

Note the trade: bounding depth *costs* 14% at one generator (66.6 vs 77.6) and pays 86% at three. Deeper mempools do produce slightly fuller EBs; that stops mattering as soon as load rises.

### The mechanism, end to end

| | unbounded | bounded |
| --- | --- | --- |
| `partition-mempool` p50 | 0.333 s | 0.306 s |
| `partition-mempool` **p95** | **7.395 s** | **1.086 s** |
| votes withheld | 133 / 540 (25%) | 35 / 257 (14%) |
| **`tooLate` votes** | **78** | **0** |

An EB is certifiable only by the block *succeeding* its announcement, so a vote gets one inter-block interval to be produced and diffused. A 7 s forge tail eats that window; a 1 s tail does not — bound the tail and `tooLate` goes to zero.

**The p50s are indistinguishable — the entire effect lives in the tail.** A run reporting only medians would have concluded the two configurations were identical, so any budget for the forge loop needs stating on the tail rather than the average.

Worth separating out: the *inclusion* rate — EBs whose certificate actually lands, ~52–53% of leader slots — is **not** what the forge work moves, and is best treated as near a structural ceiling rather than headroom. An EB needs its succeeding block to fall more than `minCertificationGap` slots later, so with Poisson block arrival the achievable rate is roughly `e^(-gap × f)`: 61% at the current gap of 10, 50% at the CIP's 14. Measured 52–53% sits between those. Since 10 is if anything already too low, there is no tightening available here. What bounding the forge loop recovers is the votes lost *on top of* that structural rate.

Three explanations this rules out, each of which I chased first: EB fill (EBs are 97% full and get *fuller* under load), forks (6.0% — 21 switches against 329 extensions), and EB overlap (re-endorsing the same transactions across producers is expected protocol behaviour, not waste).

### Where this leaves the issue

**On "time and size-bound revalidation work in the Forge loop":** the bound has to cover the *recompute* path, not just the happy path. `getSnapshot` is free on a cache hit and O(mempool depth) on a miss — with depth unbounded, misses appeared at 23% while `partition-mempool` widened to 0.62 s. A cache that is fast when it hits and unbounded when it misses still puts seconds into a leader slot.

**On the mempool's validation-time capacity:** best read as a *workaround*, not a tuning knob. 5 s admits ~34,400 transactions ≈ 3.6 s of sync — just inside one inter-block window. It caps depth precisely so that linear critical-path work stays affordable, which is why removing it collapses throughput rather than merely wasting memory.

**The direction this points:** critical-path consensus work wants to be constant, or at worst logarithmic, in mempool depth — and per #845, in *bytes* too, since holding everything else fixed and only raising transaction size took `partition-mempool` from 0.306 s to 1.183 s and `add-block-to-chaindb` from 0.054 s to 0.416 s. On this evidence linear work there does not degrade gracefully; it inverts the load-throughput relationship.

Encouragingly, the pattern already works in this codebase. Mempool *sync* is O(depth) — measured at 0.104 ms per transaction, near-perfectly linear across all twelve nodes, so ~2.9 s at 28k — and it costs nothing, because the double buffer moved it off the lock. The remaining linear term on the critical path is specifically the **snapshot recompute on cache miss**, which revalidates the whole mempool inside the forge loop; the take itself is already O(log n) plus bounded output. Moving that recompute off the critical path is the same move the double buffer made for readers and adders, and it is worth ~0.9 s per forge.

The optimistic `getSnapshot` is a hack rather than a fix — it skips revalidation instead of relocating it — but it prices the prize.

### Measurement notes worth reusing

- **On-chain throughput:** `cardano_node_metrics_cumulativeTxBytes_int` only. It is read from the ledger state at the tip and identical across producers. Difference it across samples rather than taking a median — it only moves when a block is applied, so with 20 s blocks and 10 s samples the median of a rate column is zero.
- **Byte accounting:** 232 B per transaction on chain against 228 B on the wire, confirmed two independent ways. An earlier 259 B figure came from a denominator that undercounted submissions.
- **EB fill:** read `BlockForged.numTxs` directly. Inferring it from confirmed throughput divided by a trace count gave a figure three times too low.
- **General:** a node-local trace count is not a chain quantity. That single mistake produced three retracted conclusions here; `scripts/digest.py` now extracts the forge-loop call tree, EB fill and `NotVoted`-by-reason so the diagnostic path is the default one.
