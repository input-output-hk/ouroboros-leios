# Censorship as MEV

Deliberate transaction omission for economic gain.

## Competitive

**Description**: Block producer omits competitor transactions to ensure their own transactions capture MEV opportunities.

**Mechanism**:
1. Block producer observes MEV opportunity O
2. Block producer omits all competing transactions targeting O
3. Block producer includes own transaction capturing O

```mermaid
sequenceDiagram
    participant C as Competitors
    participant BP as Block Producer
    participant M as Mempool

    Note over M: Opportunity O
    C->>M: T_c1, T_c2
    BP->>M: Observes
    BP->>BP: Creates T_bp
    BP->>BP: Includes only T_bp
    Note over M: T_c1, T_c2 pending
```

**Cardano Applicability**: Low - limited by mempool persistence.

Omitted transactions remain in mempools and will be included by subsequent honest block producers. This limits censorship to single-block opportunities.

**Leios Impact**: ↑ EB production gives each block producer a larger block to fill, potentially increasing short-term censorship effectiveness. However, the distributed nature of block production means censorship remains temporary.

**Threat Model Reference**: T16 - Omit transactions from EB

---

## Targeted

**Description**: Sustained censorship of specific addresses or transaction types to extract value.

**Mechanism**:
1. Attacker with significant stake coordinates censorship
2. Target transactions are delayed, creating time pressure
3. Victim forced to pay premium (bribe) for inclusion

```mermaid
sequenceDiagram
    participant V as Victim
    participant BP1 as BP1 (colluding)
    participant BP2 as BP2 (colluding)
    participant BP3 as BP3 (honest)

    V->>BP1: T_v
    BP1->>BP1: Omits T_v
    BP2->>BP2: Omits T_v
    Note over V: Time pressure
    V->>BP3: T_v + bribe
    BP3->>BP3: Includes T_v
```

**Cardano Applicability**: Very Low - requires substantial coordinated stake.

With current stake distribution, sustained censorship is difficult:
- Would require coordination among multiple large stake pools
- Easily detectable via on-chain analysis
- Reputation and delegation risk for participating pools

**Leios Impact**: = The 75% voting quorum for EB certification in Leios further distributes power, making coordinated censorship harder rather than easier.
