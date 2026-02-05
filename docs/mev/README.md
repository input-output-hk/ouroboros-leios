# MEV Research for Linear Leios

Research and analysis of MEV vulnerabilities in the Linear Leios protocol.

| Version | Date       | Changes       |
|---------|------------|---------------|
| 0.3     | 2026-02-05 | Added behavior-based attack grouping, mempool analysis links |
| 0.2     | 2026-01-16 | Added nested transactions (CIP-0118) analysis |
| 0.1     | 2025-12-11 | Initial draft |

## 1. Attack Behaviors

MEV attacks group into three observable behaviors, each mapping to specific attack vectors:

| Behavior | Mechanism | Attack Vectors |
|----------|-----------|----------------|
| **Network Racing** | Observe mempool, submit faster | [Front-running](./attack-vectors/front-running.md), [Sandwich](./attack-vectors/sandwich.md) |
| **Competitive Arbitrage** | Profit from price moves after trades | [Back-running](./attack-vectors/back-running.md) |
| **Stake-Based Control** | Use block production power | [Censorship](./attack-vectors/censorship.md), [Time-Bandit](./attack-vectors/time-bandit.md) |

### The Mempool as Observation Surface

The mempool is the first design component that enables adversaries to observe opportunities:

```
User tx → Mempool (visible ~20s) → Block Producer → Chain
              │
        Observation window for attackers
```

**Key insight:** All network racing attacks require mempool visibility. Fragmentation and consistency of mempool state determine attack feasibility.

### Mempool Simulation Work

Mempool behavior under load has been analyzed via discrete-event simulation:

| Tool | Purpose | Location |
|------|---------|----------|
| **mempool-sim-web** | CLI simulator with realistic topology | [post-cip/mempool-sim-web](../../post-cip/mempool-sim-web) |
| **mempool-sim-viz** | Interactive web UI | [post-cip/mempool-sim-viz](../../post-cip/mempool-sim-viz) |

**Key findings:**
- Mempool synchronization degrades rapidly with load (at 2x capacity, only 50% tx overlap between nodes)
- Fragmentation creates asymmetric information (some nodes see txs others don't)
- Front-running success scales linearly with adversarial node count (~3% txs front-run with 3% adversarial nodes)

## 2. Actor Classification

**Finding:** MEV attacks divide into three actor categories with distinct resource requirements.

| Actor | Attacks | Leios Impact |
|-------|---------|--------------|
| **Block Producer** | Reordering, insertion, censorship | Larger EBs extend advantage |
| **Searcher** | Arbitrage, liquidation | Competitive, often beneficial |
| **Infrastructure** | Batcher sandwich | Primary Cardano MEV vector |

Block producer attacks map to [T16-T18](../threat-model.md). Searcher attacks are mempool races—competitive but not extractive on Cardano due to eUTxO.

→ [Detailed classification](./classification.md) | [Attack vectors](./attack-vectors/) | [Script mapping](./script-mapping.md)

## 3. On-Chain Vulnerability Surface

**Finding:** 61% of top script activity is DEX-related (HIGH MEV risk).

| Category | Redeemers | % of Top 100 | MEV Risk |
|----------|-----------|--------------|----------|
| DEX | 21.0M | 61% | HIGH |
| NFT | 8.0M | 23% | MEDIUM |
| Unknown | 5.4M | 16% | Variable |

Top protocols by activity: Minswap (62% of DEX), WingRiders (13%), SundaeSwap (9%), Splash (8%).

→ [Full script mapping](./script-mapping.md)

## 2. Vulnerable Transaction Types

**Finding:** DEX batchers are the primary MEV surface on Cardano.

| DEX | Ordering | MEV Exposure |
|-----|----------|--------------|
| SundaeSwap | FIFO | Lower |
| Minswap | FIFO | Lower |
| WingRiders | FIFO + DAO-enforced compliance | Lower |
| MuesliSwap | Profit-maximizing | Higher |
| Splash | Execution Engine Operators + reputation | Variable |

Slippage tolerance directly impacts extraction room: 1-10% standard, up to 100% for volatile tokens.

Other vulnerable patterns:
- **Lending protocols** - liquidation races (Liqwid)
- **Oracle-dependent apps** - front-running price updates
- **Auction contracts** - displacement attacks on bids

### Attack Targets: Honest vs Conflicting Transactions

MEV attacks target transactions at two distinct points:

| Target | Attack | Mechanism |
|--------|--------|-----------|
| **Honest tx in mempool** | Insertion, sandwich | Attacker observes victim's tx and positions around it |
| **Attacker-created conflicting tx** | Displacement | Attacker creates tx consuming same UTxO as victim |

On Cardano, displacement is particularly relevant due to eUTxO contention - only one transaction can consume a given UTxO. See [front-running attacks](./attack-vectors/front-running.md) for details.

## 3. Leios-Specific Considerations

**Finding:** [L<sub>vote</sub>](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#protocol-parameters) creates an observation window where EB contents are visible before finality.

```
EB announced ──── L_vote ──── certified
                    │
              attack window
```

Implications:
- Searchers observe pending txs before settlement
- Counter-transactions can target announced EBs
- High-value txs may route via RB ([T19](../threat-model.md))

eUTxO protections remain effective - classic sandwich attacks still prevented.

## 4. Nested Transactions

**Finding:** [CIP-0118](https://github.com/cardano-foundation/CIPs/pull/862) nested transactions shift MEV extraction to the assembler layer—off-chain coordinators who batch sub-transactions. This creates infrastructure MEV similar to current DEX batchers.

```
Users ──(sub-txs)──> Assembler ──(batch)──> Mempool/EB
                          │
                    MEV extraction point
```

**Key Concerns:**
- **Assembler sandwich**: Like [batcher-level attacks](./attack-vectors/sandwich.md), assemblers control composition and ordering
- **Leios certification complexity**: Batch dependencies increase L<sub>vote</sub> validation burden
- **Private distribution trade-off**: Reduces public mempool exposure but concentrates information at assemblers
- **Guard scripts**: User protection mechanism but requires expertise

**Overall assessment:** ↓ Creates new infrastructure attack vector without eliminating existing MEV. Assembler role parallels current DEX batchers (primary Cardano MEV vector).

→ [Detailed analysis](./nested-transactions.md)
