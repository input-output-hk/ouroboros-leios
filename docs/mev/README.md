# MEV Research for Linear Leios

Research and analysis of MEV vulnerabilities in the Linear Leios protocol.

| Version | Date       | Changes       |
|---------|------------|---------------|
| 0.2     | 2026-01-16 | Added nested transactions (CIP-0118) analysis |
| 0.1     | 2025-12-11 | Initial draft |

## 1. Attack Classification

**Finding:** MEV attacks divide into three actor categories with distinct resource requirements.

| Actor | Attacks | Leios Impact |
|-------|---------|--------------|
| **Block Producer** | Reordering, insertion, censorship | ↑ Larger EBs extend advantage |
| **Searcher** | Arbitrage, liquidation | = Competitive, often beneficial |
| **Infrastructure** | Batcher sandwich | ↑ Primary Cardano MEV vector |

Block producer attacks map to [T16-T18](../threat-model.md). Searcher attacks are mempool races - competitive but not extractive on Cardano due to eUTxO.

→ [Detailed classification](./classification.md) | [Attack vectors](./attack-vectors/)

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
