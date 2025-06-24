# Transactions - Over-Collateralization CDDL

The over-collateralization approach extends Conway transactions with Leios-specific collateral mechanisms for conflict resolution in concurrent Input Blocks.

> [!Note]
> **Design Rationale**: Leios requires a separate collateral system for conflict resolution in concurrent Input Blocks, distinct from Conway's existing collateral mechanism which handles Plutus script execution failures.
>
> **TODO:** Check if both collateral system could be merged.

## Transaction Body Extensions

```diff
; Conway transaction body extended with Leios collateral fields
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
+  , ? 25 : leios_collateral_inputs      ; Leios-specific collateral for conflict resolution
+  , ? 26 : leios_collateral_return      ; Return output for unused Leios collateral
   }
```
Sources: [Conway Transaction Body](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L130-L151), [Formal Spec - Abstract Tx](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Abstract.agda#L16)

**Field Selection Rationale**: Fields 23-24 are reserved for future Conway extensions. Fields 25-26 are allocated for Leios collateral to avoid conflicts with Conway's roadmap.

## Leios Collateral Structure

```diff
+; Leios collateral inputs for conflict resolution in concurrent IBs
+leios_collateral_inputs = nonempty_set<transaction_input>
+
+; Return output for unused Leios collateral
+leios_collateral_return = transaction_output
```
Sources: [Conway Collateral Pattern](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L108-L120), [Conway Transaction Types](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L137-L145)

> [!Note]
> **Design Rationale**: Users post collateral proportional to the concurrency level of the protocol to cover wasted resources when conflicts occur.

## Supporting Types

```diff
; Reused Conway types
transaction_input = [transaction_id : transaction_id, index : uint .size 2]
transaction_output = shelley_transaction_output / babbage_transaction_output
nonempty_set<a0> = #6.258([+ a0]) / [+ a0]
transaction_id = hash32
hash32 = bytes .size 32
```
Sources: [Conway Transaction Input](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L156), [Conway Transaction Output](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L162)