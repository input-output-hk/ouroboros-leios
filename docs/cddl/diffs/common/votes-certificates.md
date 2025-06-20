# Votes and Certificates - Leios CDDL

Leios introduces a new BLS-based voting system with certificates for endorser block validation.

## Certificate Structure

Leios certificates are embedded in Ranking Blocks as described in [Ranking Blocks - CDDL Changes](ranking-blocks.md). These certificates attest to the validity of Endorser Blocks as described in [Endorser Blocks - CDDL Changes](endorser-blocks.md). Here is the complete certificate structure:

```cddl
; Complete Leios certificate structure (from crypto-benchmarks implementation)
leios_certificate =
  [ election_id            : election_id                             ; 8-byte election identifier (EID)
  , endorser_block_hash    : hash32                                  ; Hash of the endorsed block (EB)  
  , persistent_voters      : [* persistent_voter_id]                 ; Set of persistent voter IDs
  , nonpersistent_voters   : {* pool_id => bls_signature}            ; Non-persistent voters with eligibility proofs
  , ? aggregate_elig_sig   : bls_signature                           ; Aggregate eligibility signature (present when non-persistent voters exist)
  , aggregate_vote_sig     : bls_signature                           ; Aggregate BLS signature on (election_id || endorser_block_hash)
  ]
```
<sub>[1] [Certificate Reference Implementation](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/cert.rs#L13-L21), [2] [Certificate Abstract Interface](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Base.agda#L24-L28)</sub>

## Vote Structure

The Leios voting system supports two types of voters: persistent voters (selected per epoch) and non-persistent voters (selected per election via local sortition).

> [!Note]
> Individual votes are ephemeral data structures used during the voting process. They are aggregated into certificates and do not appear on the ledger or persistent storage. Only the resulting certificates are stored permanently.

```cddl
; Vote bundle containing votes for multiple endorser blocks from same voter
leios_vote_bundle = persistent_vote_bundle / non_persistent_vote_bundle

persistent_vote_bundle =
  [ 0                        ; Vote type identifier for persistent voter
  , election_id              ; 8-byte election identifier  
  , persistent_voter_id      ; 2-byte epoch-specific pool identifier
  , vote_entries             ; Map of endorser blocks to signatures
  ]

non_persistent_vote_bundle =
  [ 1                        ; Vote type identifier for non-persistent voter
  , election_id              ; 8-byte election identifier
  , pool_id                  ; 28-byte pool identifier
  , eligibility_signature    ; 48-byte BLS signature proving eligibility
  , vote_entries             ; Map of endorser blocks to signatures
  ]

vote_entries = {* endorser_block_hash => vote_signature}
```
<sub>[1] [Vote Reference Implementation](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/vote.rs#L13-L27), [2] [Formal Specification - Vote Abstract Interface](https://github.com/input-output-hk/ouroboros-leios-formal-spec/blob/main/formal-spec/Leios/Abstract.agda#L24-L27), [3] [Haskell Bundle Usage](https://github.com/input-output-hk/ouroboros-leios/blob/main/simulation/src/LeiosProtocol/Short.hs#L231-L234), [4] [Rust Vote Bundle](https://github.com/input-output-hk/ouroboros-leios/blob/main/sim-rs/sim-core/src/model.rs#L208-L212)</sub>

## BLS Key Registration

For pools to participate in Leios voting, they must register BLS keys in their operational certificates:

```diff
 operational_cert = 
   [ hot_vkey          : kes_vkey    
   , sequence_number   : uint .size 8
   , kes_period        : uint        
   , sigma             : signature   
+  , ? bls_key_reg     : bls_key_registration
   ]
```
<sub>[1] [Conway Base](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl#L114-L119)</sub>

```cddl
; BLS key registration for voting (included in operational certificates)
bls_key_registration =
  [ pool_id               : pool_id                                    ; Pool identifier (28 bytes)
  , bls_public_key        : bls_vkey                                   ; BLS12-381 G2 public key (96 bytes)
  , proof_of_possession   : bls_proof_of_possession                    ; Proof of secret key possession (96 bytes)
  , kes_signature         : kes_signature                              ; KES signature over the registration (448 bytes)
  ]

; Total size: 28 + 96 + 96 + 448 = 668 bytes
```
<sub>[1] [Registration Struct](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/key.rs#L156-L162), [2] [Proof Generation](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/bls_vote.rs#L19-L23)</sub>

## Cryptographic Types

```cddl
; Core BLS cryptographic primitives
bls_signature           = bytes .size 48                             ; BLS12-381 G1 signature (compressed)
bls_vkey                = bytes .size 96                             ; BLS12-381 G2 public key (compressed)  
bls_proof_of_possession =
  [ mu1                 : bls_signature                              ; Signature on public key
  , mu2                 : bls_signature                              ; Signature on empty message  
  ]

; Leios-specific identifiers  
election_id             = bytes .size 8                              ; Slot-based election identifier
persistent_voter_id     = uint .size 2                               ; Epoch-specific voter identifier (0-65535)
pool_id                 = bytes .size 28                             ; Stake pool identifier
endorser_block_hash     = bytes .size 32                             ; Hash of endorser block

; Additional Cardano types used
kes_signature           = bytes .size 448                            ; KES signature
hash32                  = bytes .size 32                             ; 32-byte hash (used for endorser_block_hash)
```
<sub>[1] [Sig](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/key.rs#L100), [2] [PubKey](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/key.rs#L62), [3] [PoP](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/key.rs#L139-L143), [4] [Eid](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/primitive.rs#L76), [5] [PersistentId](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/registry.rs#L14), [6] [PoolKeyhash](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/primitive.rs#L14), [7] [EbHash](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/primitive.rs#L117), [8] [KesSig](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/primitive.rs#L170)</sub>

## Committee Selection

The Fait Accompli algorithm determines persistent voters for each epoch, while local sortition selects non-persistent voters for each election.

```cddl
; Result of Fait Accompli committee selection for an epoch
fait_accompli_result =
  [ epoch                 : epoch                                     ; Epoch this applies to
  , persistent_voters     : [* persistent_voter_designation]          ; Designated persistent voters  
  , total_persistent_stake : stake_weight                             ; Total stake of persistent voters
  , non_persistent_stake  : stake_weight                              ; Remaining stake for local sortition
  ]

; Persistent voter designation
persistent_voter_designation =
  [ pool_id               : pool_id                                   ; Pool identifier  
  , persistent_voter_id   : persistent_voter_id                       ; Epoch-specific short identifier
  , stake_weight          : stake_weight                              ; Stake weight of this voter
  ]

; Local sortition result for non-persistent voters
local_sortition_result =
  [ pool_id               : pool_id                                   ; Pool identifier
  , election_id           : election_id                               ; Election identifier  
  , vrf_proof             : vrf_cert                                  ; VRF proof of eligibility
  , vote_count            : vote_count                                ; Number of votes awarded (usually 0 or 1)
  , stake_weight          : stake_weight                              ; Stake weight for this election
  ]

; Supporting types
epoch                     = uint64                                    ; Epoch number
stake_weight              = uint64                                    ; Stake amount in lovelace
vrf_cert                  = bytes                                     ; VRF certificate from existing Cardano types
vote_count                = uint8                                     ; Number of votes (typically 0 or 1)
```
<sub>[1] [FaSortition](https://github.com/input-output-hk/ouroboros-leios/blob/main/crypto-benchmarks.rs/src/fait_accompli.rs#L9-L17)</sub>

## Next
**→ [Endorser Blocks - Detailed CDDL Specification](endorser-blocks.md)**