# Ranking Blocks - Linear Leios

In Linear Leios, Ranking Blocks (RBs) serve as the anchor point for EBs. RBs can announce a new EB and certify a previously announced EB through their header and body respectively, creating a tight coupling between the Praos chain and EB processing.

## Linear Leios RB Extensions

Linear Leios extends the common ranking block structure from [Common Ranking Blocks](../common/ranking-blocks.md):

### Block Structure

```diff
 ranking_block =
   [ header                   : block_header
   , transaction_bodies       : [* transaction_body]
   , transaction_witness_sets : [* transaction_witness_set]
   , auxiliary_data_set       : {* transaction_index => auxiliary_data}
   , invalid_transactions     : [* transaction_index]
+  , ? eb_certificate         : leios_certificate     ; Certificate for previously announced EB
   ]
```

### Header Extensions

```diff
block_header =
   [
     header_body              : block_header_body
   , body_signature           : kes_signature
   ]

 block_header_body =
   [ block_number             : uint
   , slot                     : slot_no
   , prev_hash                : hash32
   , issuer_vkey              : vkey
   , vrf_vkey                 : vrf_vkey
   , vrf_result               : vrf_cert
   , block_body_size          : uint
   , block_body_hash          : hash32
+  , ? announced_eb           : hash32                 ; EB announcement (hash of announced EB)
+  , ? certified_eb           : hash32                 ; Reference to EB being certified
   ]
```

## Reference Structures

```cddl
; Hash identifier of the endorser block
eb_reference = hash32

; Transaction reference structure  
tx_reference = hash32
```

