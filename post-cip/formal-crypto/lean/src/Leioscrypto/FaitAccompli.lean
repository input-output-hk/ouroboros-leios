
import Aesop
import Leioscrypto.Types


namespace Leioscrypto


structure StakeDistribution where
  pools : List (PoolKeyHash × Coin)
  not_duplicated : (pools.map Prod.fst).Nodup
  have_stake : ∀ stake ∈ pools.map Prod.snd, stake > 0
  sorted_nonincreasing : pools.Pairwise $ fun ⟨ poolId₁ , stake₁ ⟩ ⟨ poolId₂ , stake₂ ⟩ ↦ stake₁ > stake₂ ∨ stake₁ = stake₂ ∧ poolId₁ > poolId₂

namespace StakeDistribution

  def valid_id (stakes : StakeDistribution) (poolId : PoolKeyHash) : Prop := poolId ∈ stakes.pools.map Prod.fst

  def valid_index (stakes : StakeDistribution) (i : PoolIndex) : Prop := i < stakes.pools.length

  def lookup (stakes : StakeDistribution) (i : PoolIndex) (h : i < stakes.pools.length) : PoolKeyHash × Coin :=
    stakes.pools.get ⟨ i, h ⟩

  def lookupPoolId (stakes : StakeDistribution) (i : PoolIndex) (h : i < stakes.pools.length) : PoolKeyHash :=
    Prod.fst $ stakes.pools.get ⟨ i , h ⟩

  def lookupStake (stakes : StakeDistribution) (poolId : PoolKeyHash) : Coin :=
    (stakes.pools.find? (fun x ↦ x.fst == poolId)).elim 0 Prod.snd

  theorem poolId_in_pools (stakes : StakeDistribution) (i : PoolIndex) (h : i < stakes.pools.length) : lookupPoolId stakes i h ∈ stakes.pools.map Prod.fst :=
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


def PoolWeights := List (PoolKeyHash × Rat)
deriving Inhabited

def persistentSeatCount (n : Nat) (stakes : StakeDistribution) : Nat :=
  let test : (PoolKeyHash × Nat) × (Nat × Nat) → Bool
    | ⟨ ⟨ _ , S ⟩ , ⟨ ρ , i ⟩ ⟩ => (n - i + 1) * (ρ - S)^2 ≥ (n - i) * ρ^2
  List.length
    $ List.takeWhile test
    $ stakes.pools.zip
    $ stakes.remaining.zip
    $ (List.range stakes.pools.length).map (· + 1)

def nonpersistentWeights (n : Nat) (stakes : StakeDistribution) : PoolWeights :=
  let n₁ := persistentSeatCount n stakes
  match h₁ : n₁ with
  | 0 => default
  | Nat.succ iStar =>
      let h₂ : iStar < stakes.remaining.length :=
        sorry
      let ρStar : Rat := stakes.remaining[iStar].cast
      (stakes.pools.drop n₁).map
        $ fun ⟨ poolId , S ⟩ ↦ ⟨ poolId , Rat.div S.cast ρStar ⟩


end Leioscrypto
