# Full Sharding - Leios

This directory contains CDDL specifications for the **full sharding** approach to Leios ledger design.

## Sharding Approaches

The full sharding design provides two complementary mechanisms for fee payment in sharded transactions:

### 1. UTxO Sharding ([Spec](./utxo.md))

- **Mechanism**: Explicit `shard_label` field in transaction outputs
- **Use Case**: Ongoing operations and precise shard control
- **Network Overhead**: +2 bytes per labeled output

### 2. Reward Account Sharding ([Spec](./reward-account.md))

- **Mechanism**: Implicit shard assignment via hash function: $\text{shard\_id} = \text{hash}(\text{reward\_account}) \bmod \text{total\_shards}$
- **Use Case**: Bootstrapping and immediate fee payment capability  
- **Network Overhead**: 0 bytes (computed on-demand)
- **Compatibility**: Uses existing Conway `reward_account = bytes` structure unchanged

## Comparison

| Aspect | UTxO Sharding | Reward Account Sharding |
|--------|---------------|------------------------|
| **Explicitness** | Explicit `shard_label` field | Implicit hash-based |
| **Network Overhead** | +2 bytes per output | 0 bytes |
| **Flexibility** | Can choose shard | Deterministic shard |
| **Bootstrapping** | Requires labeled UTxOs | Immediate availability |
| **Use Case** | Ongoing operations | Initial bootstrapping |

> [!Note]
> **Design Rationale**: These approaches serve different purposes and can be used together or independently. Reward account sharding enables immediate onboarding while UTxO sharding provides operational control.
