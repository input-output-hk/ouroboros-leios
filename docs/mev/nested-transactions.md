# Nested Transactions (CIP-0118) and MEV

[CIP-0118](https://github.com/cardano-foundation/CIPs/pull/862) enables batching sub-transactions via off-chain assemblers.

## Core Finding

Assemblers become the MEV extraction point—same dynamics as current DEX batchers.

```
Users ──(sub-txs)──> Assembler ──(batch)──> Mempool/EB
                          │
                    observes all, controls ordering
```

## Assembler vs Batcher Comparison

| Aspect | DEX Batchers | Nested Tx Assemblers |
|--------|--------------|----------------------|
| Control | Order selection | Sub-tx selection + ordering |
| Observation | Submitted orders | Submitted sub-txs |
| Strategy | FIFO vs profit-max | Same spectrum |
| Protection | Slippage tolerance | Guard scripts |

## Attack Vectors

**Same as batchers:** Front-running, sandwich (within batch), back-running, censorship.

**New:** Dependency griefing—consume UTxOs that victim sub-txs depend on.

**Still prevented:** Classic sandwich across batches (eUTxO contention).

## Leios Impact

- L<sub>vote</sub> window applies to complete batches
- Certification blocked if batch depends on uncertified EBs
- RB bypass viable for small batches (<90kB)

## Protections

**Guard scripts:** Top-level scripts can enforce batch constraints. Requires expertise; most users won't deploy effective guards without app support.

**Private distribution:** Reduces mempool exposure but concentrates info at assemblers.

## Assessment

| Factor | Effect |
|--------|--------|
| Mempool observation | Mixed (private but assembler sees all) |
| Attack surface | Worse (new infra vector) |
| Infrastructure | Worse (centralizing tendency) |

**Bottom line:** Shifts MEV from mempool to assembler layer. Doesn't eliminate extraction—relocates it.
