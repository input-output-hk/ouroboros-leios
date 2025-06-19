# Ranking Blocks - Leios CDDL Changes

Ranking Blocks (RBs) are extended Praos blocks that include optional Leios certificates.

## Base Block Structure Extension

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
<sub>[1] [Conway Base](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L8-L14), [2] [Leios Base](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Base.agda#L21-L22)</sub>

## Leios Certificate Definition

The `leios_certificate` referenced above is the BLS certificate structure from the crypto-benchmarks implementation:

```cddl
leios_certificate = [
  election_id            : election_id,                              ; 8-byte election identifier (EID)
  endorser_block_hash    : hash32,                                   ; Hash of the endorsed block (EB)
  persistent_voters      : [* persistent_voter_id],                  ; Set of persistent voter IDs
  nonpersistent_voters   : {* pool_id => bls_signature},             ; Non-persistent voters with eligibility proofs
  ? aggregate_elig_sig   : bls_signature,                            ; Optional aggregate eligibility signature (when non-persistent voters present)
  aggregate_vote_sig     : bls_signature                             ; Aggregate BLS signature on (election_id || endorser_block_hash)
]
```
<sub>[1] [Reference Implementation](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/cert.rs#L13-L20), [2] [Formal Spec](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Base.agda#L24-L28)</sub>

## Operational Certificate Extension

```diff
 operational_cert = 
   [ hot_vkey          : kes_vkey    
   , sequence_number   : uint .size 8
   , kes_period        : uint        
   , sigma             : signature   
+  , ? bls_key_reg     : bls_key_registration                          ; LEIOS EXTENSION: BLS key registration
   ]
```
<sub>[1] [Conway Base](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L114-L119)</sub>

## BLS Key Registration

```cddl
; BLS key registration for voting (included in operational certificates)
bls_key_registration = [
  pool_id               : pool_id,                                    ; Pool identifier (28 bytes)
  bls_public_key        : bls_vkey,                                   ; BLS12-381 G2 public key (96 bytes)
  proof_of_possession   : bls_proof_of_possession,                    ; Proof of secret key possession (96 bytes)
  kes_signature         : kes_signature                               ; KES signature over the registration (448 bytes)
]

; Total size: 28 + 96 + 96 + 448 = 668 bytes
```
<sub>[1] [Registration Struct](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/key.rs#L156-L162), [2] [Proof Generation](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/bls_vote.rs#L19-L23), [3] [Specification - Key Registration](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/Specification.md#key-registration)</sub>

## Supporting Types

```cddl
; Types used in Leios certificates
election_id         = bytes .size 8                                   ; Slot-based election identifier
persistent_voter_id = uint .size 2                                    ; Epoch-specific voter identifier (0-65535)
pool_id             = bytes .size 28                                  ; Stake pool identifier
bls_signature       = bytes .size 48                                  ; BLS12-381 signature (compressed)
bls_vkey            = bytes .size 96                                  ; BLS12-381 public key (compressed)

; BLS proof of possession (dual signature)
bls_proof_of_possession = [
  mu1 : bls_signature,                                                ; Signature on public key
  mu2 : bls_signature                                                 ; Signature on empty message
]
```
<sub>[1] [Eid](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/primitive.rs#L76), [2] [PersistentId](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/registry.rs#L14), [3] [PoolKeyhash](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/primitive.rs#L14), [4] [Sig](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/key.rs#L100), [5] [PubKey](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/key.rs#L62), [6] [PoP](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/key.rs#L139-L143)</sub>
