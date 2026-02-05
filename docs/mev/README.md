# MEV Research for Linear Leios

Research and analysis of MEV vulnerabilities in the Linear Leios protocol.

| Version | Date       | Changes       |
|---------|------------|---------------|
| 0.3     | 2026-02-05 | Consolidated attack behaviors, added mempool analysis and script mapping |
| 0.2     | 2026-01-16 | Added nested transactions (CIP-0118) analysis |
| 0.1     | 2025-12-11 | Initial draft |

## 1. Attack Behaviors

MEV attacks group into three observable behaviors:

| Behavior | Mechanism | Attack Vectors | Primary Actor |
|----------|-----------|----------------|---------------|
| **Network Racing** | Observe mempool, submit faster | [Front-running](./attack-vectors/front-running.md), [Sandwich](./attack-vectors/sandwich.md) | Searchers, Batchers |
| **Competitive Arbitrage** | Profit from price moves after trades | [Back-running](./attack-vectors/back-running.md) | Searchers |
| **Stake-Based Control** | Use block production power | [Censorship](./attack-vectors/censorship.md), [Time-Bandit](./attack-vectors/time-bandit.md) | Block Producers |

Block producer attacks map to [T16-T18](../threat-model.md). On Cardano, DEX batchers are the primary MEV vector (infrastructure-level control over tx ordering).

→ [Detailed classification](./classification.md) | [Attack vectors](./attack-vectors/)

### The Mempool as Observation Surface

The mempool is the design component that enables adversaries to observe opportunities:

```
User tx → Mempool (visible ~20s) → Block Producer → Chain
              │
        Observation window
```

Mempool behavior under load analyzed via simulation:

| Tool | Purpose | Location | Live |
|------|---------|----------|------|
| **mempool-sim-web** | CLI with realistic topology | [post-cip/mempool-sim-web](../../post-cip/mempool-sim-web) | — |
| **mempool-sim-viz** | Interactive web UI | [post-cip/mempool-sim-viz](../../post-cip/mempool-sim-viz) | [leios.cardano-scaling.org](https://leios.cardano-scaling.org/mempool-viz/) |

**Key findings:**
- Synchronization degrades with load (at 2x capacity, only 50% tx overlap between nodes)
- Fragmentation creates asymmetric information
- Front-running scales linearly with adversarial nodes (~3% nodes → ~3% txs front-run)

## 2. Vulnerable Transactions

**Finding:** DEX batchers are the primary MEV surface on Cardano.

| DEX | Ordering | MEV Exposure |
|-----|----------|--------------|
| SundaeSwap | FIFO | Lower |
| Minswap | FIFO | Lower |
| WingRiders | FIFO + DAO-enforced | Lower |
| MuesliSwap | Profit-maximizing | Higher |
| Splash | Execution Engine + reputation | Variable |

Other patterns: liquidation races (Liqwid), oracle front-running, auction displacement.

### On-Chain Activity

| Category | Redeemers | % of Top 100 | MEV Risk |
|----------|-----------|--------------|----------|
| DEX | 21.0M | 61% | HIGH |
| NFT | 8.0M | 23% | MEDIUM |
| Unknown | 5.4M | 16% | Variable |

Top DEX by volume: Minswap (62%), WingRiders (13%), SundaeSwap (9%).

→ [Script mapping](./script-mapping.md)

## 3. Leios Considerations

**Finding:** L<sub>vote</sub> creates an observation window where EB contents are visible before finality.

```
EB announced ──── L_vote ──── certified
                    │
              attack window
```

Implications:
- Searchers observe pending txs before settlement
- Counter-transactions can target announced EBs
- High-value txs may route via RB ([T19](../threat-model.md))

eUTxO protections remain effective—classic sandwich attacks still prevented.

## 4. Nested Transactions

**Finding:** [CIP-0118](https://github.com/cardano-foundation/CIPs/pull/862) shifts MEV extraction to the assembler layer.

```
Users ──(sub-txs)──> Assembler ──(batch)──> Mempool/EB
                          │
                    MEV extraction point
```

Assemblers control composition and ordering, paralleling current DEX batchers.

→ [Detailed analysis](./nested-transactions.md)
