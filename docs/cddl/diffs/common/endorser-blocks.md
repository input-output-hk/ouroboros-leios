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
+   , eb_body           : eb_body
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
+   , producer             : pool_id                                  ; Block producer identifier
+   , ? vrf_proof          : vrf_cert                                 ; VRF proof of eligibility to produce EB
+   ]
```
Sources: [Haskell Simulation EndorserBlock](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/src/LeiosProtocol/Common.hs#L160-L171), [Rust Simulation EndorserBlock](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L167-L176), [Formal Spec EndorserBlockOSig](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L97-L106)

## Body Structure

**Design Rationale**: The block references are separated into the body to align with the network protocol design. At high TPS, the combined size of IB and EB references could exceed TCP MTU, making separate header/body transmission essential for efficient network diffusion.

```diff
+ eb_body =
+   [ input_blocks         : [* ib_reference]                         ; References to input blocks
+   , ? endorser_blocks    : [* eb_reference]                         ; References to earlier endorser blocks (Full Leios)
+   ]
```
Sources: [Network Specification - Relay Protocol](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-2.md#relay-mini-protocol), [Network Specification - Fetch Protocol](https://github.com/input-output-hk/ouroboros-leios/blob/main/docs/technical-report-2.md#fetch-mini-protocol)

## Input Block Reference Structure

```diff
+ ; References to input blocks within endorser blocks
+ ib_reference             = hash32                                               ; Hash identifier of the input block
```

**Design Rationale**: IB references contain only the hash identifier, following the principle that references should include only what's needed for unique identification. Producer and slot information can be obtained by fetching the block header when needed. This aligns with the formal specification's `IBRef = Hash` approach.

Sources: [Haskell Simulation - InputBlockId](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/src/LeiosProtocol/Common.hs#L100-L105), [Rust Simulation - InputBlockId](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L98-L105), [Formal Spec - IBRef](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L33), [Formal Spec - ibRefs](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L101)

## Endorser Block Reference Structure

```diff
+ ; References to earlier endorser blocks (for Full Leios)
+ eb_reference             = hash32                                               ; Hash identifier of the endorser block
```
Sources: [Haskell Simulation](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/src/LeiosProtocol/Common.hs#L161-L163), [Rust Simulation](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L148-L152), [Formal Spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L34)

## Supporting Types

```diff
+ pool_id               = bytes .size 28                              ; Stake pool identifier (28 bytes)
+ slot_no               = uint64                                      ; Slot number
+ hash32                = bytes .size 32                              ; 32-byte hash
+ vrf_cert              = bytes                                       ; VRF certificate/proof
+ kes_signature         = bytes                                       ; KES signature
```

## Next
**→ [Input Block - CDDL](input-blocks.md)**