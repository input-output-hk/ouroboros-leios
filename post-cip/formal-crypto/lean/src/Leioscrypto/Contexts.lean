
import Leioscrypto.FaitAccompli
import Leioscrypto.Registration
import Leioscrypto.Types
import Mathlib.Data.List.Defs


/-!
Leios protocol parameters, epochs, and elections.
-/


namespace Leioscrypto


-- Note that these contextual types are correct by construction because they are not deserialized from data provided by potentially corrupt parties.


/-- Protocol parameters. -/
structure LeiosParameters where
  /-- Quorum fraction of stake. -/
  τ : Rat
  /-- Between 1/2 and all of the stake can be required for a quorum. -/
  τ_bounded : (1 : Rat) / 2 < τ ∧ τ ≤ 1
  /-- Number of seats in each election. -/
  n : Nat
  /-- A positive number of seats is required. -/
  n_positive : 0 < n


/-- Context for an epoch. -/
structure Epoch where
  /-- The protocol parameters. -/
  protocol : LeiosParameters
  /-- The pool registry. -/
  registry : Registry
  /-- The pool registry must be valid. -/
  valid_registry : registry.IsValidRegistry
  /-- Epochs are labeled by number. -/
  number : Nat
  /-- The stake distribution in the epoch. -/
  stakes : StakeDistribution
  /-- All pools in the stake distribution are also in the pool registry. -/
  pools_valid_ids : ∀ poolId ∈ stakes.pools.map Prod.fst, registry.valid_poolid poolId
  /-- The epoch last for an inclusive range of slots. -/
  slot_range : Slot × Slot
  /-- The start of the slot range is not after the end of the slot range. -/
  slot_range_ordered : slot_range.fst ≤ slot_range.snd
  /-- An epoch nonce is available. -/
  nonce : PraosNonce
  /-- Fait Accompli sortition. -/
  fa : FaitAccompli
  /-- The Fait Accompli sortition conforms to the stake distribution and protocol parameters. -/
  valid_fait_accompli : fa.stakes = stakes ∧ fa.seats = protocol.n

namespace Epoch

  /-- A pool index is in bounds. -/
  def valid_index (epoch : Epoch) : PoolIndex → Prop := epoch.stakes.valid_poolindex

  /-- A pool identifier is present in the epoch stakes. -/
  def valid_poolid (epoch : Epoch) (poolId : PoolKeyHash) : Prop := epoch.stakes.valid_poolid poolId

  /-- Look up pool registration by pool identifier. -/
  def lookupRegistration (epoch : Epoch) (poolId : PoolKeyHash) (h : epoch.valid_poolid poolId) : Registration :=
    let registry := epoch.registry
    let h₁ : registry.valid_poolid poolId :=
      by
        apply epoch.pools_valid_ids poolId
        apply h
    registry.lookupRegistration poolId h₁

  /-- Each persistent pool is in the registry. -/
  theorem valid_persistent_index_in_registry (epoch : Epoch) (poolIndex : PoolIndex) (h : epoch.fa.stakes.valid_poolindex poolIndex) : epoch.registry.valid_poolid (epoch.fa.stakes.lookupPoolId poolIndex h) :=
    by
      let ⟨h_stakes_eq, _⟩ := epoch.valid_fait_accompli
      let p := epoch.fa.stakes.lookupPoolId poolIndex h
      have h_in_fa : p ∈ epoch.fa.stakes.pools.map Prod.fst :=
        epoch.fa.stakes.poolindex_in_pools poolIndex h
      rw [h_stakes_eq] at h_in_fa
      apply epoch.pools_valid_ids
      exact h_in_fa

  /-- Each non-persistent pool is in the registry. -/
  theorem valid_nonpersistent_id_in_registry (epoch : Epoch) (poolId : PoolKeyHash) (valid : epoch.fa.valid_nonpersistent_poolid poolId) : epoch.registry.valid_poolid poolId :=
  by
      obtain ⟨h_in_stakes, _⟩ := valid
      obtain ⟨h_stakes_eq, _⟩ := epoch.valid_fait_accompli
      rw [h_stakes_eq] at h_in_stakes
      apply epoch.pools_valid_ids
      exact h_in_stakes

end Epoch


/-- An election. -/
structure Election where
  /-- The epoch. -/
  epoch : Epoch
  /-- The slot number. -/
  slot : Slot
  /-- The slot is present in the epoch. -/
  slot_in_epoch : epoch.slot_range.fst ≤ slot ∧ slot ≤ epoch.slot_range.snd
  /-- The election identifier. -/
  electionId : ElectionId
  /-- The election identifier is simply the slot number. -/
  electionId_eq_slot : electionId = slot
  /-- The EB being voted upon. -/
  ebHash : BlockHash

namespace Election

  /-- The message signed to vote for a block. -/
  def blockMessage (election : Election) : ByteArray :=
    let eid := election.electionId.toByteArray
    eid ++ election.ebHash.toByteArray

  /-- The message signed to demonstrate eligibility in an election. -/
  def eligibilityMessage (election : Election) : ByteArray :=
    let eid := election.electionId.toByteArray
    eid ++ election.epoch.nonce.toByteArray

end Election


/-- Eligibility. -/
inductive Eligible (election : Election) (poolId : PoolKeyHash) where
/-- A persistent voter. -/
| IsPersistent (h : election.epoch.fa.valid_persistent_poolid poolId) : Eligible election poolId
/-- A non-persistent voter. -/
| IsNonpersistent (h : election.epoch.fa.valid_nonpersistent_poolid poolId) : Eligible election poolId
/-- Not a voter. -/
| NotElibible : Eligible election poolId


namespace Election

  /-- Assess a pool's eligibility to vote in a particular election. -/
  def isEligible (election : Election) (poolId : PoolKeyHash) : Eligible election poolId :=
    let fa := election.epoch.fa
    let stakes := fa.stakes
    let pools := stakes.pools
    let poolIds := pools.map Prod.fst
    let test (entry : PoolKeyHash × Coin) : Bool := entry.fst == poolId
    let test' (poolId' : PoolKeyHash) : Bool := poolId' == poolId
    match h_idx : pools.findIdx? test with
    | some poolIndex =>
        have h_le : stakes.valid_poolindex poolIndex :=
          by
            rw [StakeDistribution.valid_poolindex]
            rw [List.findIdx?_eq_some_iff_findIdx_eq] at h_idx
            aesop
        have h_eq_id : stakes.lookupPoolId poolIndex h_le = poolId :=
          by
            rw [StakeDistribution.lookupPoolId]
            rw [List.findIdx?_eq_some_iff_getElem] at h_idx
            aesop
        have valid₁ : stakes.valid_poolid poolId :=
          by
            let zw := stakes.poolindex_in_pools poolIndex h_le
            rw [h_eq_id] at zw
            simp_all
        have h_eq_index : fa.stakes.lookupPoolIndex poolId valid₁ = poolIndex :=
          by
            simp [StakeDistribution.lookupPoolIndex, lookup₄, lookup₃]
            aesop
        if h_persistent : poolIndex < fa.n₁
          then
            have valid₂ : fa.valid_persistent_poolindex $ fa.stakes.lookupPoolIndex poolId valid₁ :=
              by
                rw [h_eq_index, FaitAccompli.valid_persistent_poolindex]
                simp_all
            Eligible.IsPersistent ⟨ valid₁ , valid₂ ⟩
          else
            have valid₂ : fa.stakes.lookupPoolIndex poolId valid₁ ≥ fa.n₁ :=
              by
                rw [h_eq_index]
                simp_all
            Eligible.IsNonpersistent ⟨ valid₁ , valid₂ ⟩
    | none => Eligible.NotElibible

end Election


end Leioscrypto
