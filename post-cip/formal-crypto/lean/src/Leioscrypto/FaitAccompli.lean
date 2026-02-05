
import Leioscrypto.BLS
import Leioscrypto.LocalSortition
import Leioscrypto.Registration
import Leioscrypto.StakeDistribution
import Leioscrypto.Types
import Leioscrypto.Util


namespace Leioscrypto


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

theorem persistent_seats_le_pools (n : Nat) (stakes : StakeDistribution) : persistentSeatCount n stakes ≤ stakes.pools.length :=
  by
    rw [persistentSeatCount]
    have h₁ : (List.takeWhile (persistenceTest n) (persistenceMetric stakes)).length ≤ (persistenceMetric stakes).length :=
      by
        apply length_takeWhile_le
    have h₂ : (persistenceMetric stakes).length ≤ stakes.pools.length :=
      by
        rw [persistenceMetric]
        simp [List.length_zip]
        omega
    omega

def nonpersistentSeatCount (n : Nat) (stakes : StakeDistribution) : Nat × Rat :=
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
        n - n₁
      , ρStar
      ⟩


structure FaitAccompli where
  stakes : StakeDistribution
  seats : Nat
  ρStar : Rat
  n₁ : Nat
  n₂ : Nat
  valid_persistent_seats : n₁ = persistentSeatCount seats stakes
  valid_nonpersistent_seats : ⟨ n₂ , ρStar ⟩ = nonpersistentSeatCount seats stakes

namespace FaitAccompli

  def valid_persistent_poolindex (fa : FaitAccompli) (poolIndex : PoolIndex) : Prop :=
    poolIndex < fa.n₁

  structure valid_nonpersistent_poolid (fa : FaitAccompli) (poolId : PoolKeyHash) : Prop where
  --FIXME: Experiment with rewriting this using `∃` and `def` instead of `structure`.
    valid₁ : fa.stakes.valid_poolid poolId
    valid₂ : fa.stakes.lookupPoolIndex poolId valid₁ ≥ fa.n₁

  theorem persistent_index_is_valid_index (fa : FaitAccompli) (poolIndex : PoolIndex) (h : fa.valid_persistent_poolindex poolIndex) : fa.stakes.valid_poolindex poolIndex :=
    by
      let stakes := fa.stakes
      have h₁ : poolIndex < persistentSeatCount fa.seats fa.stakes :=
        by
          rw [←fa.valid_persistent_seats]
          exact h
      have h₂ : persistentSeatCount fa.seats fa.stakes ≤ stakes.pools.length :=
        by
          apply persistent_seats_le_pools
      apply Nat.lt_of_lt_of_le h₁ h₂

  def persistentWeight (fa : FaitAccompli) (poolIndex : PoolIndex) (h : fa.valid_persistent_poolindex poolIndex) : Rat :=
    let stakes := fa.stakes
    let h₁ : stakes.valid_poolindex poolIndex := fa.persistent_index_is_valid_index poolIndex h
    let stake : Coin := stakes.lookupStakeByIndex poolIndex h₁
    stake.cast

  def nonpersistentWeight (fa : FaitAccompli) (poolId : PoolKeyHash) (h : fa.stakes.valid_poolid poolId) (σ_eid : BLS.Signature) : Rat :=
    let stakes := fa.stakes
    let stake : Coin := stakes.lookupStake poolId h
    let 𝒮 : Rat := stake.cast / fa.ρStar
    let seats := countSeats fa.n₂ 𝒮 σ_eid
    fa.ρStar * seats

end FaitAccompli


end Leioscrypto
