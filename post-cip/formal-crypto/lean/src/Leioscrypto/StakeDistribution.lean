
import Leioscrypto.Registration
import Leioscrypto.Types


/-!
Stake distributions in Leios.
-/


namespace Leioscrypto


-- Note that these contextual types are correct by construction because they are not deserialized from data provided by potentially corrupt parties.


/-- Stake distribution. -/
structure StakeDistribution where
  /-- The pools-/
  pools : List (PoolKeyHash × Coin)
  /-- Pools are unique. -/
  not_duplicated : (pools.map Prod.fst).Nodup
  /-- All pools have some stake. -/
  have_stake : ∀ stake ∈ pools.map Prod.snd, stake > 0
  /-- Pools are sorted by stake in non-decreasing order. -/
  sorted_nonincreasing : pools.Pairwise $ fun ⟨ poolId₁ , stake₁ ⟩ ⟨ poolId₂ , stake₂ ⟩ ↦ stake₁ > stake₂ ∨ stake₁ = stake₂ ∧ poolId₁ > poolId₂

namespace StakeDistribution

  /-- A pool identifier is valid. -/
  def valid_poolid (stakes : StakeDistribution) (poolId : PoolKeyHash) : Prop := poolId ∈ stakes.pools.map Prod.fst

  /-- A pool index is valid. -/
  def valid_poolindex (stakes : StakeDistribution) (poolIndex : PoolIndex) : Prop := poolIndex < stakes.pools.length

  /-- Look up a pool identifier by index. -/
  def lookupPoolId (stakes : StakeDistribution) (poolIndex : PoolIndex) (h : stakes.valid_poolindex poolIndex) : PoolKeyHash :=
    Prod.fst $ stakes.pools.get ⟨ poolIndex , h ⟩

  /-- Look up a pool's stake by identifier. -/
  def lookupStake (stakes : StakeDistribution) (poolId : PoolKeyHash) (h : stakes.valid_poolid poolId) : Coin :=
    lookup₁ stakes.pools poolId h

  /-- Look up a pool's stake by index. -/
  def lookupStakeByIndex (stakes : StakeDistribution) (poolIndex : PoolIndex) (h : stakes.valid_poolindex poolIndex) : Coin :=
    Prod.snd $ stakes.pools.get ⟨ poolIndex , h ⟩

  /-- Look up a pool index by pool identifier. -/
  def lookupPoolIndex (stakes : StakeDistribution) (poolId : PoolKeyHash) (h : stakes.valid_poolid poolId) : PoolIndex :=
    lookup₄ stakes.pools poolId h

  /-- A valid pool index corresponds to a valid pool identifier. -/
  theorem poolindex_in_pools (stakes : StakeDistribution) (poolIndex : PoolIndex) (h : stakes.valid_poolindex poolIndex) : stakes.valid_poolid (lookupPoolId stakes poolIndex h) :=
    by
      let poolId := stakes.lookupPoolId poolIndex h
      rw [lookupPoolId]
      apply List.mem_map_of_mem
      apply List.get_mem

  /-- The total stake among all pools. -/
  def total (stakes : StakeDistribution): Coin :=
    (stakes.pools.map Prod.snd).sum

  /-- The cumulatively remaining stake in the sorted list of pools. -/
  def remaining (stakes : StakeDistribution) : List Coin :=
    Prod.fst
      $ stakes.pools.foldr (init := ([], 0))
        fun ⟨ _ , stake ⟩ (acc, previousTotal) =>
          let newTotal := stake + previousTotal
          (newTotal :: acc, newTotal)

end StakeDistribution


end Leioscrypto
