## Where the mempool work stands

Putting numbers behind the graphs above, and recording what the paired experiments say. Treating this as an early validation rather than a conclusion: the prototype still has gaps — several Leios parameters are hardcoded rather than parameterized, and the forge loop still owes validation work — so what follows says more about shape and direction than about achievable limits.

Setup: `demo/dozen-devnet`, 3 block producers × 3 private relays with the nine relays fully meshed, 10 ms one-way delay, 50 Mbps per node, `TxSubmissionV2`, UTxO-HD `V2LSM`, minimum-size (228 B) transactions, on the 32-core machine at ~10% CPU. Digests and sampler output in `demo/dozen-devnet/results/2026-08-22-*`.

### Against the targets

|                              | target      | measured       |      |
|------------------------------|-------------|----------------|------|
| consensus, on chain          | 50 TxkB/s   | **96.6 kB/s**  | 1.9× |
| " , with ~652 B transactions |             | **192.2 kB/s** | 3.8× |
| mempool / ingest             | ~100 TxkB/s | **666 kB/s**   | 6.7× |

Both targets are met. The ~100 TxkB/s ingest figure looks roughly 2× conservative — a single injection point already sustains 77.6 kB/s on chain at 99% conversion, so ingest stopped being the limiting term earlier than expected. With forge-loop validation still outstanding, read these as an upper bound on the current prototype rather than settled figures.

### The double buffer does what it is designed to do

Numbers behind the screenshots above:

|                                        | baseline  | double-buffered   |
|----------------------------------------|-----------|-------------------|
| remote mempool depth, peak             | ~19,200   | **27,015** (+41%) |
| entry : remote depth ratio             | 3.27×     | **2.79×**         |
| generator burst rate (busy-second p50) | ~330 tx/s | **401 tx/s**      |
| entry relay time in add gaps > 0.5 s   | 41.0%     | 39.0%             |

Sharpest of these: during the initial fill **all twelve mempools tracked the entry node exactly** — every node at 25,536 transactions — where on the baseline remotes sawtoothed at a third of the entry node's depth.

Peak N2N accept per relay across the injection-point series was **261 → 520 → 611 tx/s**. The mechanism behind the diminishing third step is distance from an injection point rather than peer count: in the two-point run, relays peering with both origins reached 511–520 tx/s while bp3 — the only node with no origin among its peers — sat at 261 until its group got one, then 405. So the ingest target is met by topology, not by per-node speed.

### Bounding critical-path work is what actually moves throughput

Two paired runs differing only in **effective mempool capacity** — about 34,000 transactions against about 108,000 — with three phases each of one/two/three injection points. We reached those two depths by toggling `MempoolTimeoutsEnabled` (with it on, the 5 s validation-time budget admits ~34,400; with it off the 25 MB byte override binds at ~107,900), but the flag is incidental: setting the byte cap directly would give the same two points, and any other pair of caps would probe the same axis.

|                  | ingest | on chain | kB/block | depth   | blocks lost |
|------------------|--------|----------|----------|---------|-------------|
| unbounded, 1 gen | 78.2   | 77.6     | 1921     | 107,904 | 1           |
| unbounded, 2 gen | 155.5  | 64.1     | 1281     | 107,904 | 3           |
| unbounded, 3 gen | 196.5  | **51.8** | 1094     | 107,904 | 3           |
| bounded, 1 gen   | 78.2   | 66.6     | 1866     | 33,872  | 0           |
| bounded, 2 gen   | 156.0  | 88.3     | 1767     | 33,559  | 2           |
| bounded, 3 gen   | 186.7  | **96.6** | 1866     | 33,773  | 2           |

**The shallower mempool scales monotonically up; the deeper one monotonically down.** At three generators the shallow configuration delivers 86% more — 2.5× the offered ingest producing a third *less* on chain is congestion collapse.

To be clear about what that does and does not say: a large mempool is not a problem in itself, and nothing in the protocol makes it one. It hurts here purely because our implementation still does work proportional to mempool depth on the critical path, so depth converts into forge latency. Holding more transactions is desirable — it is what fills EBs, and the shallow configuration pays for that with 14% at low load. The right fix is to make the deep mempool cheap, not to keep the mempool small.

`kB/block` is the cleanest line in the table. Block counts are near-identical between the two runs, so the same number of inclusion opportunities deliver constant payload when critical-path work is bounded (1866 → 1767 → 1866) and progressively less when it is not (1921 → 1094, −43%).

That trade is visible in the table: the shallower mempool *costs* 14% at one generator (66.6 vs 77.6, where depth buys fuller EBs) and pays 86% at three, once forge latency dominates.

### The mechanism, end to end

|                             | unbounded       | bounded        |
|-----------------------------|-----------------|----------------|
| `partition-mempool` p50     | 0.333 s         | 0.306 s        |
| `partition-mempool` **p95** | **7.395 s**     | **1.086 s**    |
| votes withheld              | 133 / 540 (25%) | 35 / 257 (14%) |
| **`tooLate` votes**         | **78**          | **0**          |

An EB is certifiable only by the block *succeeding* its announcement, so a vote gets one inter-block interval to be produced and diffused. A 7 s forge tail eats that window; a 1 s tail does not — bound the tail and `tooLate` goes to zero.

**The p50s are indistinguishable — the entire effect lives in the tail.** A run reporting only medians would have concluded the two configurations were identical, so any budget for the forge loop needs stating on the tail rather than the average.

Worth separating out: the *inclusion* rate — EBs whose certificate actually lands, ~52–53% of leader slots — is **not** what the forge work moves. It is set by the certification window: an EB needs its succeeding block to fall more than `minCertificationGap` slots later, so with Poisson block arrival the achievable rate is roughly `e^(-gap × f)`, which at the gap and `f` used here puts it in the 50–60% range. Measured 52–53% sits there, so it reads as the window doing what it does rather than as headroom. What bounding the forge loop recovers is the votes lost *on top of* that structural rate — which is the part we can act on.

Where exactly that ceiling falls is a parameter question, and one this topology cannot settle on its own; it wants proper sweeps of the Leios parameters across several topologies.

Three explanations this rules out, each of which I chased first: EB fill (EBs are 97% full and get *fuller* under load), forks (6.0% — 21 switches against 329 extensions), and EB overlap (re-endorsing the same transactions across producers is expected protocol behaviour, not waste).

### Where this leaves the issue

**On "time and size-bound revalidation work in the Forge loop":** the bound has to cover the *recompute* path, not just the happy path. `getSnapshot` is free on a cache hit and O(mempool depth) on a miss — with depth unbounded, misses appeared at 23% while `partition-mempool` widened to 0.62 s. A cache that is fast when it hits and unbounded when it misses still puts seconds into a leader slot.

**On bounding mempool depth:** the cap is load-bearing today, and that is a statement about our implementation rather than about the design. A ~34,000-transaction depth is about 3.6 s of sync — just inside one inter-block window — so the cap is currently compensating for critical-path work that scales with depth. Relaxing it collapses throughput for that reason alone, not because deep mempools are inherently costly. Once the critical path is sublinear the cap should stop being load-bearing, and the depth it happens to be set to — today a consequence of the 5 s validation-time budget — should stop mattering.

**The direction this points:** critical-path consensus work wants to be constant, or at worst logarithmic, in mempool depth — and per #845, in *bytes* too, since holding everything else fixed and only raising transaction size took `partition-mempool` from 0.306 s to 1.183 s and `add-block-to-chaindb` from 0.054 s to 0.416 s. On this evidence linear work there does not degrade gracefully; it inverts the load-throughput relationship.

Encouragingly, the pattern already works in this codebase. Mempool *sync* is O(depth) — measured at 0.104 ms per transaction, near-perfectly linear across all twelve nodes, so ~2.9 s at 28k — and it costs nothing, because the double buffer moved it off the lock. The remaining linear term on the critical path is specifically the **snapshot recompute on cache miss**, which revalidates the whole mempool inside the forge loop; the take itself is already O(log n) plus bounded output. Moving that recompute off the critical path is the same move the double buffer made for readers and adders, and it is worth ~0.9 s per forge.

The optimistic `getSnapshot` is a hack rather than a fix — it skips revalidation instead of relocating it — but it prices the prize.

### Measurement notes worth reusing

- **On-chain throughput:** `cardano_node_metrics_cumulativeTxBytes_int`, read from the ledger state at the tip and identical across producers. Difference it across samples rather than taking a median — it only moves when a block is applied, so with 20 s blocks and 10 s samples the median of a rate column is zero. Node-local counters such as `txsProcessedNum` are not chain quantities: they miss any transaction confirmed in an EB that node never fetched.
- **Byte accounting:** 232 B per transaction on chain against 228 B on the wire.
- **EB fill:** read `BlockForged.numTxs` directly rather than inferring it from throughput.
- `scripts/digest.py` now extracts the forge-loop call tree, EB fill and `NotVoted`-by-reason, so the diagnostic path above is the default one.
