# Ranking Blocks - Leios CDDL

Ranking Blocks (RBs) are extended Praos blocks that include optional Leios certificates.

## Block Structure - (Conway) Extension

```diff
 ranking_block =
   [ header                   : block_header
   , transaction_bodies       : [* transaction_body]
   , transaction_witness_sets : [* transaction_witness_set]
   , auxiliary_data_set       : {* transaction_index => auxiliary_data}
   , invalid_transactions     : [* transaction_index]
+  , ? leios_cert             : leios_certificate
   ]
```
Sources: [Conway Base](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L8-L14), [Leios Base](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Base.agda#L21-L22)

## Next
**→ [Votes and Certificates - CDDL](votes-certificates.md)**
