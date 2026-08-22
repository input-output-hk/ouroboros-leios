## Where 200 TxkB/s stands

Same setup and caveats as the mempool findings in #911, which cover the forge loop and mempool side. This adds only what is specific to the throughput target.

The issue asks for ~200 B transactions at a high rate, and that is what most of the runs used. But since the target is stated in bytes, we also ran with larger transactions: `tx-firehose` now takes `--outputs-per-tx`, and 5 outputs gives 652 B instead of 228 B. That turns out to be the difference between missing and meeting the byte target:

| transaction size | bytes on chain | transactions |
| --- | --- | --- |
| 228 B (1 output) | 96.6 kB/s | 416 tx/s |
| **652 B (5 outputs)** | **192.2 kB/s** | 295 tx/s |
| target | 200 TxkB/s | 1000 tx/s |

So the larger transactions take us to **96% of 200 TxkB/s**, while transaction count stays at 30% of 1k TPS. The two diverge because the EB body holds one `(hash, size)` pair per transaction, 36 B, whatever the transaction's own size. So `maxTxsPerEb` caps transaction *count* while byte throughput is free to scale with transaction size, and 228 -> 652 B buys a 1.99x gain in bytes for only a 416 -> 295 tx/s fall in count.

That is short of the 2.81x pure size-independence would predict, and the shortfall is EB fill in count: mean fill drops 13,503 -> 11,285 because the validation-time capacity admits fewer transactions once each is more expensive to validate. Inclusion (~53%), vote timeliness (`tooLate` = 0) and block rate are all unchanged, so larger transactions do not stress certification. Throughput reconciles directly: 25 closures over 47 leader slots x 11,285 transactions x 652 B / 21.1 s = 186 kB/s against 190 measured.

### The critical path is linear in bytes too

The characterization worth adding. Holding everything else fixed and raising only transaction size, on an idle host (loadavg 3.3 of 32 cores):

| call, p50                         | 228 B   | 652 B       |          |
|-----------------------------------|---------|-------------|----------|
| `partition-mempool`               | 0.306 s | **1.183 s** | 3.9x     |
| `add-block-to-chaindb`            | 0.054 s | **0.416 s** | 7.7x     |
| `resolve-and-apply-leios-closure` | 0.096 s | 0.201 s     | 2.1x     |
| sum                               | ~0.64 s | **~1.84 s** | ~2 slots |

So the depth-dependence described in #911 is really a *bytes* dependence: the snapshot walk and the ChainDB write both scale with what they touch, and capping how many transactions sit in the mempool does not bound that on its own. At ~1.84 s the forge path is above half a slot. Votes are still on time, but that is headroom being spent, and it is the first thing to watch if size is pushed further.

### Knobs, before any protocol question

- **Transaction size**, the largest gain so far, and not exhausted: at 652 B a p50 EB carries 8.8 MB against `maxEBClosureSize` of 12 MB, so roughly 865 B per transaction would saturate the closure and give ~370 kB/s. What blocks that today is generator funding, since each output needs its own min-ada against a fixed fee, not the protocol.
- **EB fill in count**, which the mempool's validation-time capacity currently limits.
- **The Leios constants**, which are hardcoded in `LeiosDemoTypes.hs`. Parameterizing `maxTxsPerEb`, `maxMsgLeiosBlockBytesSize`, `maxEBClosureSize` and `minCertificationGap` is a prototype gap in its own right, and would let us sweep this space instead of inferring it.

Inclusion is not in that list. At ~52-53% it sits where the certification window puts it (`e^(-gap x f)`, 50-60% at the gap and `f` here), and an EB is only certifiable by the block succeeding its announcement, so there is nothing to tighten.

For scale, taking inclusion as fixed near 50%, 1000 tx/s at ~204 B needs EB fill around 40,000 transactions, a 1.44 MB announcement, about 2.9x today's `maxTxsPerEb` of 13,888. Not a limit, just what the current constants imply. But it does say the distance is in the count dimension, and that EB size rather than certification is the term with room in it.
