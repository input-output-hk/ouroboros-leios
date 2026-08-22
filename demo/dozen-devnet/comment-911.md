## Where the mempool work stands

Numbers behind the graphs above. Early validation only: several Leios parameters are still hardcoded and the forge loop still owes validation work, so these say more about shape than about achievable limits.

Setup: `demo/dozen-devnet`, 3 block producers x 3 private relays with the nine relays fully meshed, 10 ms one-way delay, 50 Mbps per node, `TxSubmissionV2`, UTxO-HD `V2LSM`, 228 B transactions, 32-core machine at ~10% CPU. Digests in `demo/dozen-devnet/results/2026-08-22-*`.

### Against the targets

|                              | target      | measured       |      |
|------------------------------|-------------|----------------|------|
| consensus, on chain          | 50 TxkB/s   | **96.6 kB/s**  | 1.9x |
| " , with ~652 B transactions |             | **192.2 kB/s** | 3.8x |
| mempool / ingest             | ~100 TxkB/s | **666 kB/s**   | 6.7x |

Both met. The ~100 TxkB/s ingest figure looks about 2x conservative: a single injection point already sustains 77.6 kB/s on chain at 99% conversion. With forge-loop validation outstanding, treat these as an upper bound on the current prototype.

### The double buffer does what it is designed to do

|                                        | baseline  | double-buffered   |
|----------------------------------------|-----------|-------------------|
| remote mempool depth, peak             | ~19,200   | **27,015** (+41%) |
| entry : remote depth ratio             | 3.27x     | **2.79x**         |
| generator burst rate (busy-second p50) | ~330 tx/s | **401 tx/s**      |
| entry relay time in add gaps > 0.5 s   | 41.0%     | 39.0%             |

Sharpest of these: during the initial fill **all twelve mempools tracked the entry node exactly**, every node at 25,536 transactions, where on the baseline remotes sawtoothed at a third of the entry node's depth.

Peak N2N accept per relay across the injection-point series was **261 -> 520 -> 611 tx/s**. The diminishing third step is about distance from an injection point, not peer count: in the two-point run, relays peering with both origins reached 511-520 tx/s while bp3, the only node with no origin among its peers, sat at 261 until its group got one, then 405. So the ingest target is met by topology rather than per-node speed.

### Mempool depth turns into forge latency

Two paired runs differing only in effective mempool capacity, about 34,000 transactions against about 108,000, three phases each of one/two/three injection points. We reached those depths by toggling `MempoolTimeoutsEnabled`, but the flag is incidental: setting the byte cap directly gives the same two points.

|                  | ingest | on chain | kB/block | depth   | blocks lost |
|------------------|--------|----------|----------|---------|-------------|
| unbounded, 1 gen | 78.2   | 77.6     | 1921     | 107,904 | 1           |
| unbounded, 2 gen | 155.5  | 64.1     | 1281     | 107,904 | 3           |
| unbounded, 3 gen | 196.5  | **51.8** | 1094     | 107,904 | 3           |
| bounded, 1 gen   | 78.2   | 66.6     | 1866     | 33,872  | 0           |
| bounded, 2 gen   | 156.0  | 88.3     | 1767     | 33,559  | 2           |
| bounded, 3 gen   | 186.7  | **96.6** | 1866     | 33,773  | 2           |

**The shallower mempool scales up, the deeper one down.** At three generators the shallow configuration delivers 86% more, and 2.5x the offered ingest producing a third less on chain is congestion collapse.

`kB/block` is the clearest line: block counts are near-identical, so the same inclusion opportunities deliver constant payload at bounded depth (1866, 1767, 1866) and progressively less at unbounded (1921 down to 1094). The trade shows too, since the shallower mempool costs 14% at one generator, where depth buys fuller EBs, and pays 86% at three once forge latency dominates.

This is not an argument against large mempools. Nothing in the protocol makes depth expensive; it costs us because our implementation still does work proportional to depth on the critical path. Holding more transactions is what fills EBs, and the shallow configuration pays 14% at low load for not doing it. So the cap is currently compensating for our own inefficiency: ~34,000 transactions is about 3.6 s of sync, just inside one inter-block window. What we want is a bound chosen for memory and fairness, which every mempool needs, rather than one falling out of a validation-time budget and quietly keeping forging affordable. If the critical path does not go sublinear far enough, an explicit governor is reasonable; better deliberate than a depth limit doing the job by accident.

### Why depth costs: votes miss their window

Both runs already use the optimistic `getSnapshot` from [ouroboros-consensus#2094](https://github.com/IntersectMBO/ouroboros-consensus/pull/2094), so revalidation is skipped whenever the cache hits. What follows is the cost that remains after that, not the cost of revalidating in the forge loop.

|                             | unbounded       | bounded        |
|-----------------------------|-----------------|----------------|
| `partition-mempool` p50     | 0.333 s         | 0.306 s        |
| `partition-mempool` **p95** | **7.395 s**     | **1.086 s**    |
| votes withheld              | 133 / 540 (25%) | 35 / 257 (14%) |
| **`tooLate` votes**         | **78**          | **0**          |

An EB is certifiable only by the block succeeding its announcement, so a vote has one inter-block interval to be produced and diffused. A 7 s forge tail eats that window, a 1 s tail does not.

**The p50s are indistinguishable, so the whole effect is in the tail.** A run reporting medians would have called the two configurations identical. Same for the bound itself: `getSnapshot` is free on a cache hit and O(depth) on a miss, and at unbounded depth misses appeared at 23% while `partition-mempool` widened to 0.62 s. So a time bound has to cover the recompute path, not just the happy path.

Separately, the inclusion rate, EBs whose certificate lands, at ~52-53% of leader slots, is not what the forge work moves. It follows from the certification window: `e^(-gap x f)` puts it in the 50-60% range at the gap and `f` used here, and 52-53% sits there. What bounding the forge loop recovers is the votes lost on top of that. Where the ceiling actually falls wants proper parameter sweeps across several topologies.

Ruled out as explanations: EB fill (EBs are 97% full and get fuller under load), forks (6.0%, 21 switches against 329 extensions), and EB overlap (re-endorsing the same transactions across producers is expected, not waste).

### What to improve next

The result here is the de-congestion. Sync is O(depth), 0.104 ms per transaction and near-perfectly linear across all twelve nodes, so ~2.9 s at 28k, and moving it off the lock made it free. That was the congestion this issue set out to remove.

The paired runs then give a reason to keep going. The remaining depth-dependent cost is the snapshot recompute on a cache miss; the take itself is already O(log n) plus bounded output. Running with an optimistic `getSnapshot` is not a serious mechanism, it just skips the revalidation, but it sizes the opportunity at roughly 0.9 s per forge.

Roughly in order: prepare the work ahead of the leader slot rather than inside it, so a miss does not revalidate the whole mempool synchronously; extend the revalidation result incrementally instead of recomputing it; and watch the byte dimension, since #845 shows the same calls growing with transaction size as well as depth (`partition-mempool` 0.306 to 1.183 s, `add-block-to-chaindb` 0.054 to 0.416 s at 652 B). None of it is needed for the targets above. It buys headroom for the next ones.
