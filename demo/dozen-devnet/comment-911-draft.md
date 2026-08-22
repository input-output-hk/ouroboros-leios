## Where the mempool work stands — early validation

Measured on `demo/dozen-devnet` — 3 block producers × 3 private relays, relays fully meshed, 10 ms one-way, 50 Mbps per node, `V2LSM`, minimum-size (228 B) transactions on a 16-core/32-thread host at ~10% CPU. Digests in `demo/dozen-devnet/results/2026-08-22-phased-depth-{bounded,unbounded}/`.

Treating this as an early validation rather than a conclusion: the prototype still has gaps — several Leios parameters are hardcoded rather than parameterized, and the forge loop still owes validation work — so what follows says more about shape and direction than about achievable limits.

### Against the 50 TxkB/s target

**96.6 kB/s** of on-chain transaction bytes with minimum-size transactions, and **192.2 kB/s** once transactions are ~652 B (see #845). Ingest reaches **666 kB/s**, so the speculation that ~100 TxkB/s of ingest would suffice looks about 2× conservative — a single injection point already delivers 77.6 kB/s at 99% conversion. With the forge-loop validation still outstanding, read these as an upper bound on the current prototype rather than a settled figure.

### The double buffer does what it is designed to do

Readers and adders proceed while the mempool resyncs, and that is directly visible:

| | baseline | double-buffered |
| --- | --- | --- |
| remote mempool depth, peak | ~19,200 | **27,015** (+41%) |
| entry : remote depth ratio | 3.27× | **2.79×** |
| generator burst rate (busy-second p50) | ~330 tx/s | **401 tx/s** |

The clearest single observation: during the initial fill **all twelve mempools tracked the entry node exactly** — every node at 25,536 transactions — which never happened on the baseline, where remotes sawtoothed at a third of the entry node's depth. Remote mempools stopped being the thing that could not keep up.

For on-chain throughput of that comparison, please read the graphs posted above rather than any figure I quote: my own numbers for it came from `txsProcessedNum`, which counts only *that node's* mempool removals and so misses any transaction confirmed in an EB the node never fetched (it understated by about a third). Use `cardano_node_metrics_cumulativeTxBytes_int`, read from the ledger state at the tip and identical across producers.

### Bounding critical-path work is what actually moves throughput

Two paired runs, one flag apart (`MempoolTimeoutsEnabled`), three phases each of 1/2/3 injection points:

| | ingest | on chain | kB/block | depth | lost |
| --- | --- | --- | --- | --- | --- |
| unbounded, 1 gen | 78.2 | 77.6 | 1921 | 107,904 | 1 |
| unbounded, 2 gen | 155.5 | 64.1 | 1281 | 107,904 | 3 |
| unbounded, 3 gen | 196.5 | **51.8** | 1094 | 107,904 | 3 |
| bounded, 1 gen | 78.2 | 66.6 | 1866 | 33,872 | 0 |
| bounded, 2 gen | 156.0 | 88.3 | 1767 | 33,559 | 2 |
| bounded, 3 gen | 186.7 | **96.6** | 1866 | 33,773 | 2 |

**Bounded scales monotonically up; unbounded monotonically down.** At three generators bounded delivers 86% more. Unbounded is not merely wasteful — it is congestion collapse: 2.5× the ingest produces a third less on chain.

`kB/block` is the cleanest line. Block counts are near-identical, so the same inclusion opportunities deliver constant payload when critical-path work is bounded (1866 → 1767 → 1866) and progressively less when it is not (1921 → 1094, −43%).

### The mechanism, end to end

| | unbounded | bounded |
| --- | --- | --- |
| `partition-mempool` p50 | 0.333 s | 0.306 s |
| `partition-mempool` **p95** | **7.395 s** | **1.086 s** |
| votes withheld | 133 / 540 (25%) | 35 / 257 (14%) |
| **`tooLate` votes** | **78** | **0** |

An EB is certifiable only by the block *succeeding* its announcement, so a vote gets one inter-block interval to be produced and diffused. A 7 s forge tail eats that window; a 1 s tail does not — bound the tail and `tooLate` goes to zero.

Worth separating from this: the *inclusion* rate — EBs whose certificate actually lands, ~52-53% of leader slots — is not what the forge work moves. That figure is close to what the certification window structurally allows (`e^(-gap x f)` is 61% at the current gap of 10, 50% at the CIP's 14), so it is best treated as near a ceiling rather than as headroom. What bounding the forge loop recovers is the votes that were being lost *on top of* that structural rate.

Note the p50s are indistinguishable. **The entire effect lives in the tail** — a run reporting only medians would have concluded the two configurations were identical, so any budget for the forge loop needs stating on the tail.

Three things this rules out as explanations, each of which we chased first: EB fill (EBs are 97% full and get *fuller* under load), forks (6.0% — 21 switches against 329 extensions), and EB overlap (re-endorsing the same transactions across producers is expected protocol behaviour, not waste).

### Where this leaves the issue

**On "time and size-bound revalidation work in the Forge loop":** the bound has to cover the *recompute* path, not just the happy path. `getSnapshot` is free on a cache hit and O(mempool depth) on a miss, and with depth unbounded misses appeared at 23% while `partition-mempool` widened to 0.62 s. A cache that is fast when it hits and unbounded when it misses still puts seconds into a leader slot.

**On the mempool's validation-time capacity:** it is best read as a *workaround*, not a tuning knob. 5 s admits ~34,400 transactions ≈ 3.6 s of sync — just inside one inter-block window. It caps depth precisely so that linear critical-path work stays affordable, which is why removing it collapses throughput.

**The direction this points:** critical-path consensus work wants to be constant or at worst logarithmic in mempool depth. On this evidence linear work there does not degrade gracefully — it inverts the load-throughput relationship. Encouragingly the pattern already works in this codebase: mempool *sync* is O(depth) at 0.104 ms/tx (near-perfectly linear across all twelve nodes, ~2.9 s at 28k) and costs nothing, because #2148 moved it off the lock. The remaining linear term is specifically the **snapshot recompute on cache miss**, which revalidates the whole mempool inside the forge loop — the take itself is already O(log n) plus bounded output. Moving that recompute off the critical path is the same move the double buffer made for readers and adders, and it is worth ~0.9 s per forge.

The optimistic `getSnapshot` in #2094 is a hack, not a fix — it skips revalidation rather than relocating it — but it prices the prize. And since #845 shows critical-path cost is linear in *bytes* too, not just in depth, this work looks like a prerequisite for spending throughput headroom elsewhere rather than a follow-up to it.
