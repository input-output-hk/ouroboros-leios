
import Leioscrypto.BLS
import Leioscrypto.LocalSortition
import Leioscrypto.Registration
import Leioscrypto.StakeDistribution
import Leioscrypto.Types


namespace Leioscrypto


structure WeightedPublicKey where
  publicKey : BLS.PublicKey
  weight : Rat

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

namespace FaitAccompli

  def valid_persistent_id (fa : FaitAccompli) (poolIndex : PoolIndex) : Prop :=
    poolIndex < fa.n₁

  def valid_nonpersistent_pool (fa : FaitAccompli) (poolId : PoolKeyHash) : Prop :=
    poolId ∈ fa.nonpersistentCandidates.map Prod.fst

  def voteWeight (fa : FaitAccompli) (poolId : PoolKeyHash) : Option BLS.Signature → Option Rat
  | none =>
      Prod.snd <$> fa.persistentStake.find? (fun ⟨ poolId' , _ ⟩ ↦ poolId' == poolId)
  | some σ_eid =>
      do
        let 𝒮 ← Prod.snd <$> fa.nonpersistentCandidates.find? (fun ⟨ poolId' , _ ⟩ ↦ poolId' == poolId)
        let seats := countSeats fa.n₂ 𝒮 σ_eid
        guard $ seats > 0
        pure $ fa.nonpersistentStake * seats

  def weighPersistent (fa : FaitAccompli) (poolIndex : PoolIndex) (h : fa.valid_persistent_id poolIndex) : WeightedPublicKey :=
    sorry

  def weighNonpersistent (fa : FaitAccompli) (poolId : PoolKeyHash) : WeightedPublicKey :=
    sorry

end FaitAccompli


end Leioscrypto
