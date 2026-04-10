# Front-Running Attack Cost Model

| Adversary % | FR Rate (2 ms delay) | Throughput | Fee Revenue/mo | Exploitable Yield/mo | Est. Infra Cost/mo | Profitable? |
|------------:|---------------------:|------------|---------------:|---------------------:|-------------------:|-------------|
| 5% | ~1.0% | Praos (~4.5 TxkB/s) | $492K | ~$130 | $25K-$75K | No |
| 25% | ~5.0% | Praos (~4.5 TxkB/s) | $492K | ~$650 | $125K-$375K | No |
| 5% | ~1.0% | Leios (~140 TxkB/s) | $9.8M | ~$2.6K | $40K-$140K | No |
| 25% | ~5.0% | Leios (~140 TxkB/s) | $9.8M | ~$13K | $200K-$700K | No |
| 5% | ~1.0% | Leios (~300 TxkB/s) | $49.2M | ~$13K | $40K-$140K | No |
| 25% | ~5.0% | Leios (~300 TxkB/s) | $49.2M | ~$65K | $200K-$700K | No |

**Exploitable Yield** = Fee Revenue × FR Rate × ~2.6% exploitable fraction.

The ~2.6% exploitable fraction reflects compounding attrition:

1. Only ~32% of [top-100 script redeemers](./script-mapping.md) are DEX order validators.
2. ~84% of DEX volume runs through FIFO batchers (Minswap, SundaeSwap, WingRiders), where mempool ordering manipulation has limited impact on final execution order.
3. Of the remaining ~16% on non-FIFO DEXes, only ~25% of orders carry sufficient value and slippage tolerance to be profitably exploited.
4. The front-running success rate depends on crafting speed: the adversary must observe, construct, and propagate a competing transaction faster than normal gossip. The 2 ms delay in the simulation already captures this race.

**Est. Infra Cost** assumes a 10K-node network, with per-node cost of ~$50-$150/mo (Hetzner to AWS) at Praos throughput, rising to ~$80-$280/mo at Leios throughput. Adversary % is the fraction of total network nodes. FR Rate scales linearly (~1% per 5% adversary at 2 ms delay; steepens to ~1% per 1-2% at -2 ms). All USD figures assume ADA at $0.25; scale linearly with price. See [simulation model docs](../../post-cip/mempool-sim-web/ReadMe.md) for simplifications and [cost estimates](../cost-estimate/README.md) for per-node breakdowns.
