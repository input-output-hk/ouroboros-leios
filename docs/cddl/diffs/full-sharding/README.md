# Full Sharding - Leios

This directory contains CDDL specifications for the **full sharding** approach to Leios ledger design.

## Sharding Approaches

The full sharding design provides two complementary mechanisms that **prevent transaction conflicts and duplicates** by ensuring potentially conflicting transactions are processed sequentially within the same shard rather than concurrently across different shards:

### 1. UTxO Sharding ([Spec](./utxo.md))

- **Mechanism**: Explicit `shard_label` field in transaction outputs
- **Use Case**: Ongoing operations and precise shard control
- **Network Overhead**: +2 bytes per labeled output

### 2. Reward Account Sharding ([Spec](./reward-account.md))

- **Mechanism**: Implicit shard assignment via hash function:
  
  $$\text{shardId} = \text{hash}(\text{rewardAccount}) \bmod \text{totalShards}$$
- **Use Case**: Bootstrapping and immediate fee payment capability  
- **Network Overhead**: 0 bytes (computed on-demand)
- **Compatibility**: Uses existing Conway `reward_account = bytes` structure unchanged
- **Scope**: Enables immediate onboarding without pre-labeling UTxOs, while broader sharding approach handles conflicts/duplicates through mempool segmentation

## Sharding Benefits

Both mechanisms contribute to the broader sharding strategy that:
- **Prevents conflicts** by processing potentially conflicting transactions sequentially within the same shard
- **Reduces duplicates** through per-shard mempool segmentation  
- **Maintains throughput** while ensuring transaction validity

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
