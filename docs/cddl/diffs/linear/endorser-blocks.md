# Endorser Blocks - Linear Leios

This file specifies the CDDL modifications for Endorser Blocks in Linear Leios, which contain transaction references and are tightly coupled to Ranking Block announcements.

## Overview

In Linear Leios, Endorser Blocks (EBs) are announced by Ranking Blocks and contain transaction references rather than full transactions.

## Linear EB Extensions

Linear Leios extends the common endorser block structure from [Common Endorser Blocks](../common/endorser-blocks.md):

```diff
 eb_body =
   [ 
-    input_blocks         : [* ib_reference]                         ; References to input blocks
-   , ? endorser_blocks    : [* eb_reference]                        ; References to earlier endorser blocks (Full Leios)
+  , transaction_references: [* tx_reference]                        ; Transaction references instead of full transactions
   ]
```

## Transaction Reference Structure

```cddl
tx_reference = bytes .size 32,                                       ; Transaction ID (hash)
```
