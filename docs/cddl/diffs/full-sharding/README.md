# Full Sharding - Leios

This directory contains CDDL specifications for the **full sharding** approach to Leios ledger design.

## Sharding Approaches

The full sharding design provides two complementary mechanisms that **prevent transaction conflicts and duplicates** by ensuring potentially conflicting transactions are processed sequentially within the same shard rather than concurrently across different shards:

### 1. UTxO Sharding ([Spec](./utxo.md))

- **Mechanism**: Explicit `shard_label` field in transaction outputs matches implicit IB `shard` derived by its VRF proof
- **Shard Assignment**: IB shard derived from VRF proof:
  
  $$\text{shardId} = \text{vrf\_value} \bmod \text{totalShards}$$
- **Network Overhead**: +2 bytes per labeled output

### 2. Reward Account Sharding ([Spec](./reward-account.md))

- **Mechanism**: Implicit shard assignment where transactions using reward accounts for collateral/withdrawals must match the IB's shard
- **Shard Assignment**: Reward account shard derived from hash function:
  
  $$\text{shardId} = \text{hash}(\text{rewardAccount}) \bmod \text{totalShards}$$
- **Network Overhead**: 0 bytes (computed on-demand)

## Sharding Benefits

Both mechanisms contribute to the broader sharding strategy that:
- **Prevents conflicts** by processing potentially conflicting transactions sequentially within the same shard
- **Reduces duplicates** through per-shard mempool segmentation  

## Comparison

| Aspect | UTxO Sharding | Reward Account Sharding |
|--------|---------------|------------------------|
| **Explicitness** | Explicit `shard_label` field | Implicit hash-based |
| **Network Overhead** | +2 bytes per output | 0 bytes |
| **Flexibility** | Can choose shard | Deterministic shard |
| **Bootstrapping** | Requires labeled UTxOs | Immediate availability |

> [!Note]
> **Design Rationale**: These approaches serve different purposes and can be used together or independently. Reward account sharding enables immediate onboarding while UTxO sharding provides operational control.
