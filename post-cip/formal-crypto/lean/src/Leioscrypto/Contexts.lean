
import Leioscrypto.FaitAccompli
import Leioscrypto.Registration
import Leioscrypto.Types
import Mathlib.Data.List.Defs


namespace Leioscrypto


-- Note that these contextual types are correct by construction because they are not deserialized from data provided by potentially corrupt parties.


structure LeiosParameters where
  τ : Rat
  τ_bounded : (1 : Rat) / 2 < τ ∧ τ ≤ 1
  n : Nat
  n_positive : 0 < n


structure Epoch where
  protocol : LeiosParameters
  registry : Registry
  valid_registry : registry.IsValidRegistry
  number : Nat
  stakes : StakeDistribution
  pools_valid_ids : ∀ poolId ∈ stakes.pools.map Prod.fst, registry.valid_poolid poolId
  slot_range : Slot × Slot
  slot_range_ordered : slot_range.fst ≤ slot_range.snd
  nonce : PraosNonce
  fa : FaitAccompli
  valid_fait_accompli : fa.stakes = stakes ∧ fa.seats = protocol.n

namespace Epoch

  def valid_index (epoch : Epoch) : PoolIndex → Prop := epoch.stakes.valid_poolindex

  def valid_poolid (epoch : Epoch) (poolId : PoolKeyHash) : Prop := epoch.stakes.valid_poolid poolId

  def lookupRegistration (epoch : Epoch) (poolId : PoolKeyHash) (h : epoch.valid_poolid poolId) : Registration :=
    let registry := epoch.registry
    let h₁ : registry.valid_poolid poolId :=
      by
        apply epoch.pools_valid_ids poolId
        apply h
    registry.lookupRegistration poolId h₁

  theorem valid_persistent_index_in_registry (epoch : Epoch) (poolIndex : PoolIndex) (h : epoch.fa.stakes.valid_poolindex poolIndex) : epoch.registry.valid_poolid (epoch.fa.stakes.lookupPoolId poolIndex h) :=
    by
      let ⟨h_stakes_eq, _⟩ := epoch.valid_fait_accompli
      let p := epoch.fa.stakes.lookupPoolId poolIndex h
      have h_in_fa : p ∈ epoch.fa.stakes.pools.map Prod.fst :=
        epoch.fa.stakes.poolindex_in_pools poolIndex h
      rw [h_stakes_eq] at h_in_fa
      apply epoch.pools_valid_ids
      exact h_in_fa

  theorem valid_nonpersistent_id_in_registry (epoch : Epoch) (poolId : PoolKeyHash) (valid : epoch.fa.valid_nonpersistent_poolid poolId) : epoch.registry.valid_poolid poolId :=
  by
      obtain ⟨h_in_stakes, _⟩ := valid
      obtain ⟨h_stakes_eq, _⟩ := epoch.valid_fait_accompli
      rw [h_stakes_eq] at h_in_stakes
      apply epoch.pools_valid_ids
      exact h_in_stakes

end Epoch


structure Election where
  epoch : Epoch
  slot : Slot
  slot_in_epoch : epoch.slot_range.fst ≤ slot ∧ slot ≤ epoch.slot_range.snd
  electionId : ElectionId
  electionId_eq_slot : electionId = slot
  ebHash : BlockHash


end Leioscrypto
