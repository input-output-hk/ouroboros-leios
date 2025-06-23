# Endorser Blocks - Leios CDDL

Endorser Blocks (EBs) are new block types in Leios that aggregate multiple Input Blocks from the current pipeline.

## Endorser Block Sortition

**Single EB Limit**: Each producer can generate **at most one Endorser Block per pipeline**, following the crypto-benchmarks implementation approach rather than the full Poisson sortition used in simulations.

**VRF Lottery**: Eligibility uses the simplified probability model:

$$P = 1 - e^{-f_{EB} \cdot \sigma}$$

Where $f_{EB}$ is the per-pipeline EB generation rate and $\sigma$ is the producer's stake fraction.

Sources: [Crypto-benchmarks Sortition](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/Specification.md#L63-L65), [Rust Simulation EB Generation](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/sim/node.rs#L606-L641)

## Block Structure

```diff
+ endorser_block =
+   [ eb_header         : eb_header
+   , ib_references     : [* ib_reference]                            ; References to input blocks
+   ]
```

## Header Structure

```diff
+ eb_header =
+   [ eb_header_body       : eb_header_body
+   , body_signature       : kes_signature
+   ]
+ 
+ eb_header_body =
+   [ slot                 : slot_no                                  ; Slot when EB was created
+   , producer             : node_id                                  ; Block producer identifier
+   , input_blocks         : [* ib_reference]                         ; References to input blocks
+   , ? endorser_blocks    : [* eb_reference]                         ; References to earlier endorser blocks (Full Leios)
+   , ? vrf_proof          : vrf_cert                                 ; VRF proof of eligibility to produce EB
+   ]
```
Sources: [Haskell Simulation EndorserBlock](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/src/LeiosProtocol/Common.hs#L160-L171), [Rust Simulation EndorserBlock](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L167-L176), [Formal Spec EndorserBlockOSig](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L97-L106)

## Input Block Reference Structure

```diff
+ ; References to input blocks within endorser blocks
+ ib_reference = [
+   ib_id               : ib_id,                                      ; Hash identifier of the input block
+   slot                : slot_no,                                    ; Slot when IB was created
+   producer            : node_id                                     ; IB producer identifier
+ ]
+ 
+ ; Supporting types
+ ib_id                 = hash32                                      ; Input block identifier
```
Sources: [Haskell Simulation - InputBlockId](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/src/LeiosProtocol/Common.hs#L100-L105), [Rust Simulation - InputBlockId](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L98-L105), [Formal Spec - IBRef](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L33), [Formal Spec - ibRefs](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L101)

## Endorser Block Reference Structure

```diff
+ ; References to earlier endorser blocks (for Full Leios)
+ eb_reference = [
+   eb_id               : eb_id,                                      ; Hash identifier of the endorser block  
+   slot                : slot_no,                                    ; Slot when EB was created
+   producer            : node_id                                     ; EB producer identifier
+ ]
+ 
+ ; Supporting types
+ eb_id                 = hash32                                      ; Endorser block identifier
```
Sources: [Haskell Simulation](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/src/LeiosProtocol/Common.hs#L161-L163), [Rust Simulation](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L148-L152), [Formal Spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L34)

## Supporting Types

```diff
+ node_id               = uint32                                      ; Node identifier (simulation)
+ slot_no               = uint64                                      ; Slot number
+ hash32                = bytes .size 32                              ; 32-byte hash
```

## Next
**→ [Input Block - CDDL](input-blocks.md)**