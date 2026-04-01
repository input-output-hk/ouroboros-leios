# Front-Running Attack Cost Model

| Adversary % | FR Rate (2 ms delay) | Throughput | Infra Cost/mo | Fee Revenue/mo | Exploitable Yield/mo | Profitable? |
|------------:|---------------------:|------------|---------------|---------------:|---------------------:|-------------|
| 5% | ~1.0% | Praos (~3.5 TPS) | $50-$150 per node | $492K | ~$130 | No |
| 25% | ~5.0% | Praos (~3.5 TPS) | $50-$150 per node | $492K | ~$650 | No |
| 5% | ~1.0% | Leios (~70 TPS) | $80-$280 per node | $9.8M | ~$2.6K | No |
| 25% | ~5.0% | Leios (~70 TPS) | $80-$280 per node | $9.8M | ~$13K | No |
| 5% | ~1.0% | Leios (~350 TPS) | $80-$280 per node | $49.2M | ~$13K | No |
| 25% | ~5.0% | Leios (~350 TPS) | $80-$280 per node | $49.2M | ~$65K | No |

**Exploitable Yield** = Fee Revenue × FR Rate × ~2.6% exploitable fraction.

The ~2.6% exploitable fraction reflects compounding attrition:

1. Only ~32% of [top-100 script redeemers](./script-mapping.md) are DEX order validators.
2. ~84% of DEX volume runs through FIFO batchers (Minswap, SundaeSwap, WingRiders), where mempool ordering manipulation has limited impact on final execution order.
3. Of the remaining ~16% on non-FIFO DEXes, only ~25% of orders carry sufficient value and slippage tolerance to be profitably exploited.
4. The front-running success rate itself depends on crafting speed: the adversary must observe, construct, and propagate a competing transaction faster than normal gossip. The 2 ms delay in the simulation already captures this race.

Infra cost is per adversary node (Hetzner to AWS range); multiply by node count to get total (e.g., 25% of a 10K network = 2,500 nodes × $80-$280 = $200K-$700K/mo). FR Rate scales linearly (~1% per 5% adversary at 2 ms delay; steepens to ~1% per 1-2% at -2 ms). All USD figures assume ADA at $0.25; scale linearly with price. See [simulation model docs](../../post-cip/mempool-sim-web/ReadMe.md) for simplifications and [cost estimates](../cost-estimate/README.md) for per-node breakdowns.
