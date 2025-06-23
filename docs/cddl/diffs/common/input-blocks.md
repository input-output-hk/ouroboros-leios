# Input Blocks - Leios CDDL

**Single IB Limit**: Each producer can generate **at most one Input Block per slot**, following the crypto-benchmarks implementation approach rather than the full Poisson sortition used in simulations.

**VRF Lottery**: Eligibility uses the simplified probability model:

$$P = 1 - e^{-f_{IB} \cdot \sigma}$$

Where $f_{IB}$ is the per-slot IB generation rate and $\sigma$ is the producer's stake fraction.

Sources: [Crypto-benchmarks Sortition](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/Specification.md?plain=1#L64), [Rust Simulation IB Generation](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/sim/node.rs#L561-L597)

## Block Structure

```diff
+ input_block =
+   [ ib_header                  : ib_header
+   , transaction_bodies         : [* transaction_body]
+   , transaction_witness_sets   : [* transaction_witness_set]
+   , auxiliary_data_set         : {* transaction_index => auxiliary_data}
+   , invalid_transactions       : [* transaction_index]
+   ]
```
Sources: [Formal Spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L40-L57), [Haskell Simulation](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/src/LeiosProtocol/Common.hs#L138-L142), [Rust Simulation](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L136-L141)

## Header Structure

```diff
+ ib_header =
+   [ ib_header_body       : ib_header_body
+   , body_signature       : kes_signature
+   ]
+ 
+ ib_header_body =
+   [ slot                 : slot_no                                  ; Slot when IB was created
+   , producer_id          : pool_id                                  ; Block producer identifier
+   , vrf_proof            : vrf_cert                                 ; VRF proof of eligibility to produce IB
+   , block_body_hash      : hash32                                   ; Hash of the block body
+   , ranking_block_ref    : hash32                                   ; Reference to ranking block for ledger state
+   ]
```
Sources: [Formal Spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Blocks.agda#L40-L45), [Haskell Simulation](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/src/LeiosProtocol/Common.hs#L114-L124), [Rust Simulation](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L127-L133)

## Supporting Types

```diff
+ ; Block identifiers
+ ib_id = hash32                                                      ; Input block identifier (hash)
+ 
+ ; Basic types
+ pool_id = bytes                                                     ; Pool/producer identifier
+ slot_no = uint64                                                    ; Slot number
+ hash32 = bytes .size 32                                             ; 32-byte hash
+ vrf_cert = bytes                                                    ; VRF certificate/proof
+ kes_signature = bytes                                               ; KES signature
``` 