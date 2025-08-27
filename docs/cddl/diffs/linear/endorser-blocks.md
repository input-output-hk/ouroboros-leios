# Endorser Blocks - Linear Leios

This file specifies the CDDL modifications for Endorser Blocks in Linear Leios, which contain transaction references and conflicting transaction information. EBs have no header/body separation and are announced through RB headers.

## Overview

In Linear Leios, Endorser Blocks (EBs) are announced by Ranking Blocks through the `announced_eb` field in the RB header. EBs contain transaction references rather than full transactions and include information about conflicting transactions from previous RBs.

## Linear EB Structure

Linear Leios completely replaces the common endorser block structure:

```diff
- endorser_block =
-   [ eb_header                : eb_header
-   , eb_body                  : eb_body
-   ]
-
- eb_header =
-   [ eb_header_body           : eb_header_body
-   , body_signature           : kes_signature
-   ]
-
- eb_header_body =
-   [ slot                     : slot_no
-   , producer                 : pool_id
-   , ? vrf_proof              : vrf_cert
-   ]
-
- eb_body =
-   [ 
-     input_blocks         : [* ib_reference]                         ; References to input blocks
-   , ? endorser_blocks    : [* eb_reference]                        ; References to earlier endorser blocks (Full Leios)
-   ]

+ endorser_block =
+   [ conflicting_txs          : [* transaction_index]              ; Indices of conflicting txs in previous RBs
+   , transaction_references   : [* tx_reference]                   ; Transaction references
+   ]
```

## Reference Structures

```cddl
; Transaction reference structure  
tx_reference = hash32                                               ; Transaction ID (hash)

; Transaction index in a block
transaction_index = uint
```
