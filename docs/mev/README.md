# MEV Research for Linear Leios

Research and analysis of MEV vulnerabilities in the Linear Leios protocol.

| Version | Date       | Changes       |
|---------|------------|---------------|
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
| MuesliSwap | Profit-maximizing | Higher |
| Splash | Execution Engine Operators + reputation | Variable |

Slippage tolerance directly impacts extraction room: 1-10% standard, up to 100% for volatile tokens.

Other vulnerable patterns:
- **Lending protocols** - liquidation races (Liqwid)
- **Oracle-dependent apps** - front-running price updates
- **Auction contracts** - displacement attacks on bids

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

*Research pending.*

## References

- [CIP-0164](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md) - Leios specification
- [Threat Model](../threat-model.md) - T16-T19
- [SundaeSwap](https://docs.sundaeswap.finance/), [Minswap](https://docs.minswap.org/), [Splash](https://docs.splash.trade/), [Liqwid](https://docs.liqwid.finance/)
