
import Leioscrypto.Types


namespace Leioscrypto


structure StakeDistribution where
  pools : List (PoolKeyHash × Coin)
  not_duplicated : (pools.map Prod.fst).Nodup
  have_stake : ∀ stake ∈ pools.map Prod.snd, stake > 0
  sorted_nonincreasing : pools.Pairwise $ fun ⟨ poolId₁ , stake₁ ⟩ ⟨ poolId₂ , stake₂ ⟩ ↦ stake₁ > stake₂ ∨ stake₁ = stake₂ ∧ poolId₁ > poolId₂

namespace StakeDistribution

  def lookup (stakes : StakeDistribution) (i : Nat) (h : i < stakes.pools.length) : PoolKeyHash × Coin :=
    stakes.pools.get ⟨ i, h ⟩

  def lookupPoolId (stakes : StakeDistribution) (i : Nat) (h : i < stakes.pools.length) : PoolKeyHash :=
    Prod.fst $ stakes.pools.get ⟨ i , h ⟩

  theorem poolId_in_pools (stakes : StakeDistribution) (i : Nat) (h : i < stakes.pools.length) : lookupPoolId stakes i h ∈ stakes.pools.map Prod.fst :=
    by
      let poolId := stakes.lookupPoolId i h
      rw [lookupPoolId]
      apply List.mem_map_of_mem
      apply List.get_mem


  def total (stakes : StakeDistribution): Coin :=
    (stakes.pools.map Prod.snd).sum

  def remaining (stakes : StakeDistribution) : List Coin :=
    Prod.fst
      $ stakes.pools.foldr (init := ([], 0))
        fun ⟨ _ , stake ⟩ (acc, previousTotal) =>
          let newTotal := stake + previousTotal
          (newTotal :: acc, newTotal)

end StakeDistribution


/-
def persistentSeatCount (n : Nat) (stakes : StakeDistribution) : Nat :=
  let test (i : Nat) (S : Nat) (ρ : Nat) : Bool :=
    (n - i + 1) * (ρ - S)^2 ≥ (n - i) * ρ^2
  let ρs := stakes.remaining
  sorry
-/

end Leioscrypto
