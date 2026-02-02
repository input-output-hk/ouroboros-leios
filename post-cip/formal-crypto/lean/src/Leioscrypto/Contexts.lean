
import Aesop
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


def StakeDistribution := List (PoolKeyHash × Coin)

namespace StakeDistribution

  def total_stake (stakes : StakeDistribution): Coin :=
    (stakes.map Prod.snd).sum

  def not_duplicated (stakes : StakeDistribution) : Prop :=
    (stakes.map Prod.fst).Nodup

  def have_stake (stakes : StakeDistribution) : Prop :=
    ∀ stake ∈ stakes.map Prod.snd, stake > 0

  def sorted_nonincreasing (stakes : StakeDistribution) : Prop :=
    stakes.Pairwise $ fun ⟨ poolId₁ , stake₁ ⟩ ⟨ poolId₂ , stake₂ ⟩ ↦ stake₁ > stake₂ ∨ stake₁ = stake₂ ∧ poolId₁ > poolId₂

end StakeDistribution


structure Epoch where
  registry : Registry
  valid_registry : registry.IsValidRegistry
  number : Nat
  pools : StakeDistribution
  pools_not_duplicated : pools.not_duplicated
  pools_have_stake : pools.have_stake
  pools_sorted_nonincreasing : pools.sorted_nonincreasing
  pools_valid_ids : ∀ p ∈ pools.map Prod.fst, p ∈ registry.map Registration.poolId
  slot_range : Slot × Slot
  slot_range_ordered : slot_range.fst ≤ slot_range.snd
  nonce : PraosNonce

namespace Epoch

  def lookup (epoch : Epoch) (i : Nat) (h : i < epoch.pools.length) : PoolKeyHash × Coin :=
    epoch.pools.get ⟨ i, h ⟩

  def lookupPoolId (epoch : Epoch) (i : Nat) (h : i < epoch.pools.length) : PoolKeyHash :=
    Prod.fst $ epoch.pools.get ⟨ i , h ⟩

  theorem poolId_in_pools (epoch : Epoch) (i : Nat) (h : i < epoch.pools.length) : lookupPoolId epoch i h ∈ epoch.pools.map Prod.fst :=
    by
      let poolId := epoch.lookupPoolId i h
      rw [lookupPoolId]
      apply List.mem_map_of_mem
      apply List.get_mem

end Epoch


structure Election where
  epoch : Epoch
  slot : Slot
  slot_in_epoch : epoch.slot_range.fst ≤ slot ∧ slot ≤ epoch.slot_range.snd
  electionId : ElectionId
  electionId_eq_slot : electionId = slot
  ebHash : BlockHash


end Leioscrypto
