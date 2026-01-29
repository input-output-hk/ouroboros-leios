# Attack Requirements & Detection

Operational analysis: what attacks require and what traces they leave.

## Requirements by Actor

### Block Producer Attacks

Requires winning slot leadership election.

| Attack | Additional Requirements |
|--------|------------------------|
| [Skip-the-line](./attack-vectors/front-running.md#skip-the-line) | Mempool visibility, own MEV-extracting tx ready |
| [Displacement](./attack-vectors/front-running.md#displacement) | Mempool visibility, competing tx for same UTxO |
| [Insertion](./attack-vectors/front-running.md#insertion) | Mempool visibility, knowledge of victim's intent |
| [Censorship](./attack-vectors/censorship.md) | Sustained attack needs multiple consecutive slots |

### Searcher Attacks

No stake required - anyone with mempool access can compete.

| Attack | Requirements |
|--------|-------------|
| [Arbitrage](./attack-vectors/back-running.md#arbitrage) | Trading capital, price monitoring across DEXes |
| [Liquidation](./attack-vectors/back-running.md#liquidation) | Liquidation capital, position monitoring |
| [Classic sandwich](./attack-vectors/sandwich.md#classic) | *Not feasible on Cardano - eUTxO contention* |

### Infrastructure Attacks

Requires privileged off-chain position.

| Attack | Position Required |
|--------|------------------|
| [Batcher sandwich](./attack-vectors/sandwich.md#batcher-level) | DEX batcher operator role |
| [Time-bandit](./attack-vectors/time-bandit.md) | Substantial stake for sustained fork |

---

## Observable Artifacts

| Artifact | On-chain | Collection Difficulty | Current Availability |
|----------|----------|----------------------|---------------------|
| **Script failures (phase-2)** | Yes - for winning tx only | Easy | Queryable via DB-Sync |
| **Batcher ordering** | Yes - batch internals visible | Easy | Queryable via DB-Sync |
| **Volume/fee patterns** | Yes | Easy | Queryable via DB-Sync |
| **UTxO contention losers** | No - rejected at mempool; only in node logs | Hard | Requires live monitoring |
| **Tx ordering vs submission time** | No - submission time not stored | Hard | Requires live monitoring |
| **Orphan blocks / slot battles** | No | Hard | Requires live monitoring |

**Hard = no historical data exists.** Would require contacting SPOs who may have stored node logs, or setting up dedicated monitoring infrastructure going forward.

**Note on phase-2 visibility:** Phase-2 validation results (whether the script succeeded or failed, with collateral consumed on failure) are only recorded for the transaction that "won" inclusion in a block. When multiple parties race to spend the same UTxO, losing transactions are rejected when they attempt to enter a node's mempool - these rejections are only recorded in node logs, not on-chain.

**Best candidates for historical MEV analysis:**
- Batcher ordering patterns (fully on-chain)
- Phase-2 script failures with collateral loss
- Fee/volume anomalies around oracle updates, liquidations

---

## Leios-Specific Considerations

### Block Capacity Scaling

Leios EBs (~512 kB) are larger than Praos blocks (~90 kB). This is a **proportional increase** in MEV attack surface - more transactions per block means more selection/reordering opportunities - but does not introduce fundamentally new attack vectors.

### Extended Observation Window

Leios introduces additional time between EB announcement and finality (see [protocol parameters](https://github.com/cardano-scaling/CIPs/blob/leios/CIP-0164/README.md#protocol-parameters): L<sub>hdr</sub>, L<sub>vote</sub>, L<sub>diff</sub>). During this window, EB contents are visible to the network, giving searchers more time to identify MEV opportunities and construct counter-transactions for subsequent EBs.

### RB-Only Bypass

High-value transactions can be included directly in RBs, bypassing EB exposure ([T19](../threat-model.md)). This reduces MEV exposure but is self-limiting - RB capacity constraints prevent widespread use.
