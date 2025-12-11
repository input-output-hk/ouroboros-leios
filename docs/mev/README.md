# MEV Analysis for Linear Leios

Analysis of Maximal Extractable Value (MEV) and front-running vulnerabilities in the Linear Leios protocol ([CIP-0164](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md)).

| Version | Date       | Changes       |
|---------|------------|---------------|
| 0.1     | 2025-12-11 | Initial draft |

## What is MEV?

Maximal Extractable Value refers to profit that block producers can extract by including, excluding, or reordering transactions within blocks. Originally termed "Miner Extractable Value" in proof-of-work systems, MEV represents a fundamental tension between transaction ordering fairness and economic incentives of block producers.

### MEV in the Cardano Context

Cardano's Extended UTxO (eUTxO) model differs from account-based chains like Ethereum:

| Property | MEV Impact |
|----------|------------|
| **Transaction determinism** | Outcomes fixed at submission - no state manipulation between submission and execution |
| **No global state reads** | Scripts can't read arbitrary state, limiting some attack vectors |
| **UTxO contention** | Competing txs for same UTxO are mutually exclusive - natural serialization |

These properties provide structural protection against some attacks (notably classic sandwich attacks), but MEV still exists via:

- **DEX batcher ordering** - batchers control order sequencing within their transactions
- **Oracle update front-running** - positioning before known price changes
- **Liquidation opportunities** - racing to liquidate undercollateralized positions
- **Script-spending visibility** - transaction intent visible in mempool

For comparison, ~95% of Ethereum DEX volume now routes through private mempools to avoid MEV extraction.

## How Leios Changes the MEV Landscape

Linear Leios introduces several changes affecting MEV dynamics:

1. **Endorser Blocks (EBs)**: Larger blocks (~512 kB) giving producers more transaction selection capacity
2. **Coupled RB/EB Production**: Same producer controls both Ranking Blocks and EBs
3. **Extended Observation Window**: The voting period [L<sub>vote</sub>](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#protocol-parameters) exposes EB contents to the network before certification and finality
4. **RB-Only Option**: High-value transactions may bypass EBs entirely to reduce exposure ([T19](../threat-model.md#t19))

The eUTxO model continues providing structural protection, but larger blocks and extended observation windows slightly increase some risks.

## Attack Vector Summary

| Attack | Description | Praos | Leios Δ | Details |
|--------|-------------|-------|---------|---------|
| [Skip-the-Line](./attack-vectors/front-running.md#skip-the-line) | Higher-fee tx jumps queue | Moderate | ↑ | Larger EB selection |
| [Displacement](./attack-vectors/front-running.md#displacement) | Attacker consumes victim's UTxO | High | = | UTxO contention unchanged |
| [Insertion](./attack-vectors/front-running.md#insertion) | Tx inserted before victim's | Low | ↑ | EB construction opaque |
| [Arbitrage Back-Run](./attack-vectors/back-running.md#arbitrage) | Profit from cross-DEX price lag | Moderate | = | Volume may increase |
| [Liquidation Snipe](./attack-vectors/back-running.md#liquidation) | Race to liquidate positions | High | = | Protocol-dependent |
| [Classic Sandwich](./attack-vectors/sandwich.md#classic) | Front+back-run around victim | Very Low | = | eUTxO prevents |
| [Batcher Sandwich](./attack-vectors/sandwich.md#batcher-level) | Exploit order within batch | Moderate | ↑ | Larger batches |
| [Time-Bandit](./attack-vectors/time-bandit.md) | Reorg chain to steal MEV | Very Low | = | Praos settlement |
| [Competitive Censorship](./attack-vectors/censorship.md#competitive) | Omit competitor txs | Low | ↑ | Larger block window |
| [Targeted Censorship](./attack-vectors/censorship.md#targeted) | Sustained omission for bribes | Very Low | = | Needs majority stake |

**Legend**: ↑ increased risk, = unchanged

## References

### Protocol Specifications
- [CIP-0164: Leios](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md) - Linear Leios protocol specification
- [Leios Threat Model](../threat-model.md) - Threats T16-T19 cover MEV at high level

### Cardano DEX Documentation
- [SundaeSwap](https://docs.sundaeswap.finance/)
- [Minswap](https://docs.minswap.org/)
- [Splash](https://docs.splash.trade/concepts/protocol-concepts/temporal-liquidity-book)
- [Liqwid](https://docs.liqwid.finance/)
