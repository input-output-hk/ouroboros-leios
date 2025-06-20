# Input Blocks - Full Sharding CDDL

The common [`input_block`](../common/input-blocks.md#block-structure) structure is used with shard assignment in the IB header.

## Sharded IB Header

```diff
; Common IB header body from leios-common.cddl
 ib_header_body =
   [ slot                  : slot_no
   , producer              : node_id
   , ib_certificate        : ib_cert
   , ? vrf_proof           : vrf_cert
+  , shard                 : shard_id                              ; Shard assignment from VRF
   ]
```
<sub>[1] [Common CDDL](../common/input-blocks.md#block-structure), [2] [Rust simulation](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L130)</sub>

## Shard Assignment

```cddl
; Shard identifier (16-bit allows up to 65,536 shards)
; Current simulation configs use 1-900 shards
shard_id = uint .size 2

; Shard assignment based on VRF value
; Implementation: shard = vrf_value mod total_shards
```
<sub>[1] Ledger v0.2: "each IB has a shard id (determined through its VRF value)", [2] [Rust Shard Assignment](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/sim/node.rs#L599-L604)</sub>

## Supporting Types

```cddl
; Basic types
shard_id = uint .size 2                                             ; 16-bit shard identifier (current range: 1-900)
slot_no = uint64                                                    ; Slot number
```

## Next

**→ [Sharded Transactions - CDDL](transactions.md)** 