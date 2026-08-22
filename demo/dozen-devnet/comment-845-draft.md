## Where we stand on 200 TxkB/s — early validation

Measured on `demo/dozen-devnet` (3 BPs × 3 private relays, fully meshed, 10 ms one-way, 50 Mbps, 16-core host at ~10% CPU). Digests in `demo/dozen-devnet/results/2026-08-22-*`. Related work in #911.

Treating this as an early validation rather than an answer: the prototype still has gaps — several Leios parameters are hardcoded rather than parameterized, and the forge loop still owes validation work — so the numbers below say more about *shape* than about achievable limits.

### The measurement

| | measured | target | |
| --- | --- | --- | --- |
| **bytes** | **192.2 kB/s** | 200 TxkB/s | 96% |
| **tx/s** | 295 | 1000 | 30% |

Byte throughput is close to target; transaction count is not, and the two diverge because the EB body holds one `(hash, size)` pair per transaction — 36 B — however large the transaction is. So `maxTxsPerEb` binds on *count* and byte throughput scales with transaction size. At 652 B (`--outputs-per-tx 5`) we get 192.2 kB/s against 96.6 at 232 B, a 1.99× gain with tx/s falling only 416 → 295.

Getting even this far needed the forge-loop work in #911. With mempool depth unbounded the system shows congestion collapse — 2.5× the ingest yields a third *less* on chain (77.6 → 64.1 → 51.8 kB/s) — while bounded it scales monotonically (66.6 → 88.3 → 96.6). The chain of causation is that `partition-mempool` p95 of 7.4 s eats the one inter-block interval a vote has, so `tooLate` votes climb and certificates stop forming; bounding the tail to 1.1 s takes `tooLate` to zero.

### The arithmetic, and the knobs

Throughput in transaction count decomposes cleanly, and the model is validated against the runs:

```
tx/s = EB fill × inclusion ÷ block interval      (13,420 × 0.53 ÷ 21.1 = 337, measured 295–337)
```

Which is useful mainly because every term is something we can currently turn, **without touching the protocol**:

- **Transaction size** — already exercised, and the largest single gain so far (1.99×). Not yet at its limit: at 652 B a p50 EB carries 8.8 MB against `maxEBClosureSize` of 12 MB, so ~865 B/tx would saturate the closure and give ~370 kB/s. The current blocker is generator funding (each output needs min-ada against a fixed fee), not the protocol.
- **EB fill** — mean fill drops 13,503 → 11,285 as transactions get more expensive to validate, because the mempool's validation-time capacity admits fewer of them. Both that budget and `MempoolCapacityBytesOverride` are configuration.
- **The Leios constants themselves** — `maxTxsPerEb`, `maxMsgLeiosBlockBytesSize`, `maxEBClosureSize` and `minCertificationGap` are hardcoded in `LeiosDemoTypes.hs`. Parameterizing them is a prototype gap in its own right, and would let us explore this space rather than infer it.

**Inclusion, on the other hand, does not look like a knob.** An EB is certifiable only by the block succeeding its announcement, and only if that block falls more than `minCertificationGap` slots later — so with Poisson block arrival the achievable rate is roughly `e^(-gap x f)`: 61% at the current gap of 10, 50% at the CIP's 14. Measured inclusion is **52-53%**, sitting between those, i.e. already about what the window allows. Since 10 is if anything too low already, there is no tightening available here, and moving to 14 would lower it. Planning on ~40-50% seems the honest assumption rather than treating the gap to 100% as headroom.

For scale, if one wanted 1000 tx/s at ~204 B, and taking inclusion as fixed near 50%, the same arithmetic puts EB fill at ~40,000 transactions — a 1.44 MB announcement, about 2.9x the current `maxTxsPerEb` of 13,888. I would not read that as a limit; it is what today's hardcoded constants imply, and they have not been explored. But it does say the count dimension is where the distance is, and that EB size rather than certification is the term with room in it.

### One caution before spending EB-size headroom

Critical-path cost turns out to be linear in the **bytes** the forge loop touches, not only in mempool depth. Holding everything fixed and only raising transaction size:

| call, p50 | 232 B | 652 B | |
| --- | --- | --- | --- |
| `partition-mempool` | 0.306 s | **1.183 s** | 3.9× |
| `add-block-to-chaindb` | 0.054 s | **0.416 s** | 7.7× |
| `resolve-and-apply-leios-closure` | 0.096 s | 0.201 s | 2.1× |
| sum | ~0.64 s | **~1.84 s** | ~2 slots |

On an idle host (loadavg 3.3 / 32 cores), so not host saturation. At ~1.84 s the forge path is above half a slot and votes are on time only because headroom remains. Raising EB size, and adding the validation the forge loop still owes, both push that same number up — so the critical-path work looks like a prerequisite for spending the other knobs rather than a follow-up.

### Measurement notes worth reusing

- On-chain throughput: `cardano_node_metrics_cumulativeTxBytes_int`, read from the ledger state at the tip and identical across producers. `txsProcessedNum` counts only that node's mempool removals and understated us by about a third.
- Byte accounting: **232 B** per transaction on chain against 228 B on the wire, confirmed two independent ways.
- EB fill is best read from `BlockForged.numTxs` directly; inferring it from confirmed throughput divided by a trace count gave a figure three times too low.
