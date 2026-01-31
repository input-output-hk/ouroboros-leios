
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
deriving Repr


structure Epoch where
  registry : Registry
  valid_registry : registry.IsValidRegistry
  number : Nat
  pools : List (PoolKeyHash × Coin)
  pools_not_duplicated : (pools.map Prod.fst).Nodup
  pools_have_stake : ∀ stake ∈ pools.map Prod.snd, stake > 0
  pools_sorted_nonincreasing : pools.Pairwise (fun ⟨ poolId₁ , stake₁ ⟩ ⟨ poolId₂ , stake₂ ⟩ ↦ stake₁ > stake₂ ∨ stake₁ = stake₂ ∧ poolId₁ > poolId₂)
  pools_valid_ids : ∀ p ∈ pools.map Prod.fst, p ∈ registry.map Registration.poolId
  slot_range : Slot × Slot
  slot_range_ordered : slot_range.fst ≤ slot_range.snd
  nonce : PraosNonce

namespace Epoch

  def lookup (epoch : Epoch) (i : Nat) (h : i < epoch.pools.length) : PoolKeyHash × Coin :=
    epoch.pools.get ⟨ i, h ⟩

  def lookupPoolId (epoch : Epoch) (i : Nat) (h : i < epoch.pools.length) : PoolKeyHash :=
    Prod.fst $ epoch.pools[i]

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
