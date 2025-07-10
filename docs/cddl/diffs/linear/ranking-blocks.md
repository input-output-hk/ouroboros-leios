# Ranking Blocks - Linear Leios

In Linear Leios, Ranking Blocks (RBs) serve as the anchor point for EBs. RBs can announce a new EB and certify a previously announced EB, creating a tight coupling between the Praos chain and EB processing.

## Linear Leios RB Extensions

Linear Leios extends the common ranking block structure from [Common Ranking Blocks](../common/ranking-blocks.md):

```diff
 ranking_block =
   [ header                   : block_header
   , transaction_bodies       : [* transaction_body]
   , transaction_witness_sets : [* transaction_witness_set]
   , auxiliary_data_set       : {* transaction_index => auxiliary_data}
   , invalid_transactions     : [* transaction_index]
   , ? leios_cert             : leios_certificate
+  , ? announced_eb           : eb_reference          ; EB announcement details
+  , ? eb_certificate         : leios_certificate     ; EB certificate and reference from previously announced ranking block
   ]
```

## Endorser Block Reference Structure

```diff
+ ; References to input blocks within endorser blocks
+ eb_reference             = hash32                                               ; Hash identifier of the endorser block
```