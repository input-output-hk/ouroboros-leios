# Reward Account Sharding Analysis

The reward account sharding scheme leverages Conway's existing structure without modifications for network transfer, using **implicit hash-based shard assignment**.

## Supporting CDDL Definitions

```cddl
; Conway structure remains unchanged
reward_account = bytes
withdrawals = {+ reward_account => coin}
```
Sources: [Conway Reward Account](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L382), [Conway Withdrawals](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L421)

## Shard Assignment Algorithm

The shard assignment for reward accounts is computed implicitly:

$$\text{shardId} = \text{hash}(\text{rewardAccount}) \bmod \text{totalShards}$$

**Where**:
- `hash()` uses the same hash function as Cardano address derivation
- `total_shards` is a protocol parameter
- Ensures deterministic shard assignment across all nodes

## Fee Payment Validation

For fee payment validation, transactions must ensure:

$$
\text{hash}(\text{rewardAccount}) \bmod \text{totalShards} = \text{ibShardId}
$$

> [!Note]
> This enables bootstrapping: users can immediately use reward accounts for fee payment without setup overhead.