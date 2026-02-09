# Non-normative formal specifications for Leios sortition, votes, and certificates in Lean4

See [the read-me in the parent folder](../ReadMe.md) for context and further references.


## Status

This formal specification is a **non-normative** attempt to disambiguate and clarify concepts and relationships in [the original normative specifications](../ReadMe.md).


## Type relationships

```mermaid
classDiagram
    %% --- Core Election Structures ---
    class Election {
        +Epoch epoch
        +Slot slot
        +ElectionId electionId
        +BlockHash ebHash
    }

    class Epoch {
        +LeiosParameters protocol
        +Registry registry
        +Nat number
        +StakeDistribution stakes
        +SlotRange slot_range
        +PraosNonce nonce
        +FaitAccompli fa
    }

    class LeiosParameters {
        +Rat τ
        +Nat n
    }

    class FaitAccompli {
        +StakeDistribution stakes
        +Nat seats
        +Rat ρStar
        +Nat n₁
        +Nat n₂
    }

    %% --- Identity and Stakes ---
    class StakeDistribution {
        +List~PoolKeyHash, Coin~ pools
    }

    class Registry {
        %% Registry is defined as List Registration
        +List~Registration~ entries
    }

    class Registration {
        +Pool pool
        +Nat issueCounter
        +ColdKeySignature signature
    }

    class Pool {
        +PoolKeyHash poolId
        +PublicKey mvk
        +ProofOfPossession μ
    }

    %% --- Certificates and Votes ---
    class Certificate {
        +ElectionId electionId
        +BlockHash ebHash
        +List~PoolIndex~ persistentVotes
        +List~PoolKeyHash, Signature~ nonpersistentVotes
        +Option~Signature~ σ_tilde_eid
        +Signature σ_tilde_m
    }

    class Vote {
        <<Inductive>>
        +PersistentVote(ElectionId, PoolIndex, BlockHash, Signature)
        +NonpersistentVote(ElectionId, PoolKeyHash, Signature, BlockHash, Signature)
    }

    class Eligible {
        <<Inductive>>
        +IsPersistent(Proof)
        +IsNonpersistent(Proof)
        +NotEligible
    }

    %% --- Relationships ---
    Election *-- Epoch
    Epoch *-- LeiosParameters
    Epoch *-- Registry
    Epoch *-- StakeDistribution
    Epoch *-- FaitAccompli
    
    %% FaitAccompli references the same stake distribution
    FaitAccompli --> StakeDistribution 
    
    Registry o-- Registration
    Registration *-- Pool
    
    %% Conceptual Links
    Certificate --> Election : validates
    Certificate ..> Vote : aggregates (conceptual)
    
    Vote --> Election : targets
    Eligible --> Election : predicate on
```


## Conventions for constraints

- `WellFormed` constraints ensure that values have basic internal consistency.
- `Valid` constraints ensure that values are consistent with their context.
- `Authentic` constraints ensure that values are cryptographically verified.
- `Checked` constraints simply ensure `WellFormed ∧ Valid ∧ Authentic`.


## Source

- [BLS.lean](./src/Leioscrypto/BLS.lean): primitive BLS types, functions, and axioms.
- [Certificate.lean](./src/Leioscrypto/Certificate.lean): certificates.
- [Contexts.lean](./src/Leioscrypto/Contexts.lean): protocol parameters, epochs, and elections.
- [FaitAccompli.lean](./src/Leioscrypto/FaitAccompli.lean): Fait Accompli sortition.
- [LocalSortition.lean](./src/Leioscrypto/LocalSortition.lean):  local sortition.
- [Registration.lean](./src/Leioscrypto/Registration.lean): key registration.
- [StakeDistribution.lean](./src/Leioscrypto/StakeDistribution.lean): stake distribution.
- [Types.lean](./src/Leioscrypto/Types.lean): basic types.
- [Util.lean](./src/Leioscrypto/Util.lean): miscellaneous functions and theorems.
- [Vote.lean](./src/Leioscrypto/Vote.lean): votes.


## Type-checking and testing the specification

A [Nix shell derivation](./shell.nix) is provided for type-checking the specification and executing its test suite.

```bash
nix-shell
lake build
lake test
```
