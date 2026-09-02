# Front-Running Attack Cost Model

| Adversary % | FR Rate (2 ms delay) | Throughput | Fee Revenue/mo | Exploitable Yield/mo | Est. Infra Cost/mo | Profitable? |
|------------:|---------------------:|------------|---------------:|---------------------:|-------------------:|-------------|
| 5% | ~1.0% | Praos (~4.5 TxkB/s) | $436K | ~$110 | $25K-$75K | No |
| 25% | ~5.0% | Praos (~4.5 TxkB/s) | $436K | ~$570 | $125K-$375K | No |
| 5% | ~1.0% | Leios (~140 TxkB/s) | $13.6M | ~$3.5K | $40K-$140K | No |
| 25% | ~5.0% | Leios (~140 TxkB/s) | $13.6M | ~$17.7K | $200K-$700K | No |
| 5% | ~1.0% | Leios (~300 TxkB/s) | $29.1M | ~$7.6K | $40K-$140K | No |
| 25% | ~5.0% | Leios (~300 TxkB/s) | $29.1M | ~$37.8K | $200K-$700K | No |

**Fee Revenue** is total network fee revenue per the [cost estimate](../cost-estimate/README.md)
fee model: fee = 0.155381 + 0.0000440576 × size, i.e. 0.221467 ADA at the assumed
1,500-byte average transaction, over a 30.42-day month at $0.25/ADA. For example,
300 TxkB/s = 200 tx/s → 525.6M tx/mo → 116.4M ADA ≈ $29.1M.

**Exploitable Yield** = Fee Revenue × FR Rate × ~2.6% exploitable fraction.

The ~2.6% exploitable fraction reflects compounding attrition:

1. Only ~32% of [top-100 script redeemers](./script-mapping.md) are DEX order validators (order submission scripts, not pool or batching validators).
2. ~84% of DEX volume runs through FIFO batchers (Minswap, SundaeSwap, WingRiders), where mempool ordering manipulation has limited impact on final execution order.
3. Of the remaining ~16% on non-FIFO DEXes, we assume ~50% of orders carry sufficient value and slippage tolerance to be profitably exploited. This factor is a modeling assumption, not a measured quantity. Yield is linear in it, so the sensitivity is bounded: at the assumed 50%, yields fall short of infrastructure cost by 5x (300 TxkB/s against the cheapest hosting) to 220x (Praos). Doubling the factor to 100% halves those margins, leaving the tightest case ~2.7x short, so no scenario becomes profitable.
4. Combined: 32% × 16% × 50% ≈ 2.6%.
5. The front-running success rate depends on crafting speed: the adversary must observe, construct, and propagate a competing transaction faster than normal gossip. The 2 ms delay in the simulation already captures this race.

**Est. Infra Cost** assumes a 10K-node network, with per-node cost of ~$50-$150/mo (Hetzner to AWS) at Praos throughput, rising to ~$80-$280/mo at Leios throughput. Adversary % is the fraction of total network nodes. FR Rate scales linearly (~1% per 5% adversary at 2 ms delay; steepens to ~1% per 1-2% at -2 ms). All USD figures assume ADA at $0.25; scale linearly with price. See [simulation model docs](../../post-cip/mempool-sim-web/ReadMe.md) for simplifications and [cost estimates](../cost-estimate/README.md) for per-node breakdowns.
