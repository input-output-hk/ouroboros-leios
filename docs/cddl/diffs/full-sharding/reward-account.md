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
; Conway transaction body extended with Leios collateral field
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
+  , ? 25 : leios_collateral             ; Leios collateral from reward accounts
   }
```

## Leios Collateral Structure

```diff
+; Leios collateral using reward accounts (same type as withdrawals)
+leios_collateral = {+ reward_account => coin}
```
Sources: [Conway Transaction Body](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L130-L151), [Conway Withdrawals](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L421)

**Field Selection Rationale**: Field 25 is allocated for Leios collateral specification using the same type as Conway withdrawals. Fields 23-24 are reserved for future Conway extensions, making 25 the next available field for Leios reward account sharding extensions.

> [!Note]
> **Design Rationale**: The explicit reward account field allows transactions to specify which reward account should be used for collateral posting, enabling deterministic shard assignment for fee payment validation.

## Shard Assignment Algorithm

The shard assignment for reward accounts is computed implicitly:

$$\text{shardId} = \text{hash}(\text{rewardAccount}) \bmod \text{totalShards}$$

**Where**:
- `hash()` uses the same hash function as Cardano address derivation
- `total_shards` is a protocol parameter
- Ensures deterministic shard assignment across all nodes

## Shard Assignment Validation

For all VKey reward accounts in both `withdrawals` and `leios_collateral` fields, transactions must ensure:

$$
\text{hash}(\text{rewardAccount}) \bmod \text{totalShards} = \text{ibShardId}
$$

**Where this validation applies to**:
- All VKey reward accounts in the `withdrawals` field 
- All VKey reward accounts in the `leios_collateral` field 
- Script reward accounts are exempt from this restriction

> [!Important]
> **Implications**: This creates significant constraints where VKey reward accounts can only withdraw staking rewards or post collateral in transactions belonging to their assigned shard, preventing cross-shard conflicts and ensuring collateral integrity. Script reward accounts remain unrestricted.