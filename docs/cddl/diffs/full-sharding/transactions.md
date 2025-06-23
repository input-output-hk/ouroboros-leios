# Sharded Transactions - CDDL

The full sharding approach extends Conway transactions with shard assignment and fee payment mechanisms to ensure compatibility with the sharded ledger design.

## Core Sharding Principles

The transaction extensions implement the following design principles from Ledger v0.2:
- **Shard Assignment**: Transactions are assigned to shards based on their fee-paying UTxOs
- **Fee Payment**: "Any tx submitted to Leios must pay its fees through labelled UTxOs or reward accounts"
- **UTxO Labeling**: "UTxOs can be explicitly labelled with a shard id"
- **Reward Account Sharding**: "Reward accounts are implicitly assigned a shard id based on their hash"

## UTxO Shard Labeling

```diff
; Conway transaction output from conway.cddl
 transaction_output = 
   [ address
   , amount : value
   , ? datum_option : datum_option
   , ? script_ref : script_ref
+  , ? shard_label : shard_id                                      ; Optional explicit shard labeling
   ]
```
Sources: [Conway CDDL](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#162), Ledger v0.2: "UTxOs can be explicitly labelled with a shard id"

## Reward Account Sharding

Sources: Ledger v0.2: "Reward accounts are implicitly assigned a shard id based on their hash"

> [!Important]
> **TODO**: Missing details.

## Supporting Types

```cddl
; Base Cardano types (referenced from Conway)
transaction_input = [transaction_id, uint32]                                 ; Conway transaction input
transaction_output = shelley_transaction_output / babbage_transaction_output ; Conway transaction output  
transaction_id = hash32                                                      ; Conway transaction ID
reward_account = bytes                                                       ; Conway reward account
coin = uint64                                                                ; Coin amount
certificates = nonempty_set<certificate>                                     ; Conway certificates
withdrawals = {+ reward_account => coin}                                     ; Conway withdrawals

; Sharding-specific types
shard_id = uint .size 2                                                      ; 16-bit shard identifier (0-65535)
slot_no = uint64                                                             ; Slot number
hash32 = bytes .size 32                                                      ; 32-byte hash
hash28 = bytes .size 28                                                      ; 28-byte hash
uint64 = uint .size 8                                                        ; 64-bit unsigned integer
```
Sources: [Conway CDDL](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L156) 