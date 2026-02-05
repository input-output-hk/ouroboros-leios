# Attack Requirements & Detection

Operational analysis: what attacks require and what traces they leave.

## Requirements by Behavior

### Network Racing

Observe mempool, submit faster. Primary actors: Searchers, Batchers.

| Attack | Requirements |
|--------|--------------|
| [Front-running](./attack-vectors/front-running.md) | Mempool visibility, fast tx construction |
| [Sandwich](./attack-vectors/sandwich.md) | Batcher role (classic sandwich not feasible—eUTxO contention) |

### Competitive Arbitrage

Profit from price moves after trades. Primary actors: Searchers.

| Attack | Requirements |
|--------|--------------|
| [Arbitrage](./attack-vectors/back-running.md#arbitrage) | Trading capital, cross-DEX price monitoring |
| [Liquidation](./attack-vectors/back-running.md#liquidation) | Liquidation capital, position monitoring |

### Stake-Based Control

Use block production power. Primary actors: Block Producers (SPOs).

| Attack | Requirements |
|--------|--------------|
| [Censorship](./attack-vectors/censorship.md) | Slot leadership; sustained attack needs consecutive slots |
| [Time-bandit](./attack-vectors/time-bandit.md) | Substantial stake for sustained fork |

---

## Observable Artifacts

| Artifact | On-chain | Collection |
|----------|----------|------------|
| Batcher ordering | Yes | Easy (DB-Sync) |
| Script failures (phase-2) | Yes | Easy (DB-Sync) |
| Volume/fee patterns | Yes | Easy (DB-Sync) |
| UTxO contention losers | No | Hard (node logs) |
| Tx submission timing | No | Hard (live monitoring) |

**Best candidates for MEV analysis:** Batcher ordering patterns, phase-2 failures with collateral loss, fee anomalies around oracle updates.

---

## Leios Considerations

| Factor | Impact |
|--------|--------|
| EB capacity (512kB vs 90kB) | More txs per block = more reordering opportunity |
| L<sub>vote</sub> window | Extended observation time before finality |
| RB bypass | High-value txs can skip EB exposure ([T19](../threat-model.md)) |
