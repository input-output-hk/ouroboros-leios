
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

private def persistenceTest (n : Nat) : (PoolKeyHash × Nat) × (Nat × Nat) → Bool
| ⟨ ⟨ _ , S ⟩ , ⟨ ρ , i ⟩ ⟩ => (n - i + 1) * (ρ - S)^2 ≥ (n - i) * ρ^2

private def persistenceMetric (stakes : StakeDistribution) : List ((PoolKeyHash × Nat) × (Nat × Nat)) :=
  stakes.pools.zip
    $ stakes.remaining.zip
    $ (List.range stakes.pools.length).map (· + 1)

def persistentSeatCount (n : Nat) (stakes : StakeDistribution) : Nat :=
  List.length
    $ List.takeWhile (persistenceTest n)
    $ persistenceMetric stakes

def nonpersistentWeights (n : Nat) (stakes : StakeDistribution) : Rat × PoolWeights :=
  let n₁ := persistentSeatCount n stakes
  match h₁ : n₁ with
  | 0 => default
  | Nat.succ iStar =>
      let pm := persistenceMetric stakes
      let pt := persistenceTest n
      let h₂ : iStar < stakes.remaining.length :=
        by
          have h_bound : List.length (List.takeWhile pt pm) ≤ List.length pm :=
            by
              induction pm with
              | nil =>
                simp
              | cons head tail ih =>
                simp [List.takeWhile]
                split
                · apply Nat.succ_le_succ
                  exact ih
                · apply Nat.zero_le
          change n₁ ≤ _ at h_bound
          rw [h₁] at h_bound
          dsimp [pm, persistenceMetric] at h_bound
          rw [List.length_zip, List.length_zip] at h_bound
          apply Nat.lt_of_succ_le
          apply Nat.le_trans h_bound
          apply Nat.le_trans (Nat.min_le_right _ _)
          apply Nat.min_le_left
      let ρStar : Rat := stakes.remaining[iStar].cast
      ⟨
        ρStar
      , (stakes.pools.drop n₁).map $ fun ⟨ poolId , S ⟩ ↦ ⟨ poolId , Rat.div S.cast ρStar ⟩
      ⟩


structure FaitAccompli where
  stakes : StakeDistribution
  seats : Nat
  n₁ : Nat
  valid_persistent_seats : n₁ = persistentSeatCount seats stakes
  persistentStake : List (PoolKeyHash × Rat)
  valid_persistent_stake : persistentStake = (stakes.pools.take n₁).map (fun ⟨ poolId , s ⟩ ↦ ⟨ poolId , s.cast ⟩)
  nonpersistentStake : Rat
  nonpersistentCandidates : List (PoolKeyHash × Rat)
  valid_nonpersistent_seats : ⟨ nonpersistentStake , nonpersistentCandidates ⟩ = nonpersistentWeights seats stakes
  n₂ : Nat
  valid_seats : n₁ + n₂ = seats


end Leioscrypto
