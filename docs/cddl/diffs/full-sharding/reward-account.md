# Reward Account Sharding Analysis

The reward account sharding scheme leverages Conway's existing structure without modifications for network transfer, using **implicit hash-based shard assignment**.

## Supporting CDDL Definitions

```cddl
; Conway structure remains unchanged
reward_account = bytes
withdrawals = {+ reward_account => coin}
```
Sources: [Conway Reward Account](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L382), [Conway Withdrawals](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L421)

## Transaction Body Extensions

```diff
; Conway transaction body extended with reward account collateral field
 transaction_body =
   { 0  : set<transaction_input>         ; inputs
   , 1  : [* transaction_output]         ; outputs
   , 2  : coin                           ; fee
   , ? 3  : slot_no                      ; ttl
   , ? 4  : certificates                 ; certificates
   , ? 5  : withdrawals                  ; withdrawals
   , ? 7  : auxiliary_data_hash          ; auxiliary_data_hash
   , ? 8  : slot_no                      ; validity_interval_start
   , ? 9  : mint                         ; mint
   , ? 11 : script_data_hash             ; script_data_hash
   , ? 13 : nonempty_set<transaction_input> ; collateral_inputs (Conway - for script failures)
   , ? 14 : required_signers             ; required_signers
   , ? 15 : network_id                   ; network_id
   , ? 16 : transaction_output           ; collateral_return (Conway - for script failures)
   , ? 17 : coin                         ; total_collateral (Conway - for script failures)
   , ? 18 : nonempty_set<transaction_input> ; reference_inputs
   , ? 19 : voting_procedures            ; voting_procedures
   , ? 20 : proposal_procedures          ; proposal_procedures
   , ? 21 : coin                         ; current_treasury_value
   , ? 22 : positive_coin                ; donation
+  , ? 25 : reward_account               ; Reward account for collateral posting
   }
```
Sources: [Conway Transaction Body](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L130-L151), [Conway Reward Account](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L382)

**Field Selection Rationale**: Field 25 is allocated for reward account collateral specification. Fields 23-24 are reserved for future Conway extensions, making 25 the next available field for Leios reward account sharding extensions.

> [!Note]
> **Design Rationale**: The explicit reward account field allows transactions to specify which reward account should be used for collateral posting, enabling deterministic shard assignment for fee payment validation.

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