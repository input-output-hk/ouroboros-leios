## Where 200 TxkB/s stands

Same setup and caveats as the mempool findings in #911, which cover the forge loop and mempool side. This adds only what is specific to the throughput target.

The issue asks for ~200 B transactions at a high rate, and that is what most of the runs used. But since the target is stated in bytes, we also ran with larger transactions: `tx-firehose` now takes `--outputs-per-tx`, and 5 outputs gives 652 B instead of 228 B.

| transaction size      | bytes on chain | transactions |
|-----------------------|----------------|--------------|
| 228 B (1 output)      | 96.6 kB/s      | 416 tx/s     |
| **652 B (5 outputs)** | **192.2 kB/s** | 295 tx/s     |
| target                | 200 TxkB/s     | 1000 tx/s    |

Larger transactions essentially reach the byte target, and leave transaction count well short of 1k TPS. That split is structural rather than incidental: the EB body holds one `(hash, size)` pair per transaction, 36 B, whatever the transaction's own size. So `maxTxsPerEb` caps transaction *count*, while byte throughput is free to grow with transaction size. Doubling the bytes cost us relatively little count.

Not quite as much as pure size-independence would give, because EB fill in count also drops: the mempool's validation-time capacity admits fewer transactions once each is more expensive to validate. Nothing else moved. Inclusion, vote timeliness (`tooLate` stayed at zero) and block rate were all unchanged, so larger transactions do not stress certification.

### The critical path is linear in bytes too

The characterization worth adding. Holding everything else fixed and raising only transaction size, on an idle host:

| call, p50                         | 228 B   | 652 B       |          |
|-----------------------------------|---------|-------------|----------|
| `partition-mempool`               | 0.306 s | **1.183 s** | 3.9x     |
| `add-block-to-chaindb`            | 0.054 s | **0.416 s** | 7.7x     |
| `resolve-and-apply-leios-closure` | 0.096 s | 0.201 s     | 2.1x     |
| sum                               | ~0.64 s | **~1.84 s** | ~2 slots |

So the depth-dependence described in #911 is really a *bytes* dependence: the snapshot walk and the ChainDB write both scale with what they touch, and capping how many transactions sit in the mempool does not bound that on its own. The forge path is now well over half a slot. Votes are still on time, but that is headroom being spent, and it is the first thing to watch if transaction size is pushed further.

### Knobs, before any protocol question

- **Transaction size**, the largest gain so far, and not exhausted. At 652 B an EB is still comfortably inside `maxEBClosureSize`, so there is room to keep going. What blocks that today is generator funding, since each output needs its own min-ada against a fixed fee, not the protocol.
- **EB fill in count**, which the mempool's validation-time capacity currently limits.
- **The Leios constants**, hardcoded in `LeiosDemoTypes.hs`. Parameterizing `maxTxsPerEb`, `maxMsgLeiosBlockBytesSize`, `maxEBClosureSize` and `minCertificationGap` is a prototype gap in its own right, and would let us sweep this space instead of inferring it.

Inclusion is not in that list. It sits where the certification window puts it, and since an EB is only certifiable by the block succeeding its announcement, there is nothing to tighten.

Which locates the remaining distance to 1k TPS in the count dimension, and specifically in EB size rather than in certification. Closing it would need `maxTxsPerEb` several times larger than today's value. That is not a limit, just what the current constants imply, and a reason to make them sweepable.
