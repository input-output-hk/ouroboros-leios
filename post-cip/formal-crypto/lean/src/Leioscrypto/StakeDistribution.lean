
import Leioscrypto.Registration
import Leioscrypto.Types


namespace Leioscrypto


structure StakeDistribution where
  pools : List (PoolKeyHash × Coin)
  not_duplicated : (pools.map Prod.fst).Nodup
  have_stake : ∀ stake ∈ pools.map Prod.snd, stake > 0
  sorted_nonincreasing : pools.Pairwise $ fun ⟨ poolId₁ , stake₁ ⟩ ⟨ poolId₂ , stake₂ ⟩ ↦ stake₁ > stake₂ ∨ stake₁ = stake₂ ∧ poolId₁ > poolId₂

namespace StakeDistribution

  def valid_poolid (stakes : StakeDistribution) (poolId : PoolKeyHash) : Prop := poolId ∈ stakes.pools.map Prod.fst

  def valid_poolindex (stakes : StakeDistribution) (poolIndex : PoolIndex) : Prop := poolIndex < stakes.pools.length

  def lookupPoolId (stakes : StakeDistribution) (poolIndex : PoolIndex) (h : stakes.valid_poolindex poolIndex) : PoolKeyHash :=
    Prod.fst $ stakes.pools.get ⟨ poolIndex , h ⟩

  def lookupStake (stakes : StakeDistribution) (poolId : PoolKeyHash) (h : stakes.valid_poolid poolId) : Coin :=
    lookup₁ stakes.pools poolId h

  def lookupStakeByIndex (stakes : StakeDistribution) (poolIndex : PoolIndex) (h : stakes.valid_poolindex poolIndex) : Coin :=
    Prod.snd $ stakes.pools.get ⟨ poolIndex , h ⟩

  def lookupPoolIndex (stakes : StakeDistribution) (poolId : PoolKeyHash) (h : stakes.valid_poolid poolId) : PoolIndex :=
    lookup₄ stakes.pools poolId h

  theorem poolindex_in_pools (stakes : StakeDistribution) (poolIndex : PoolIndex) (h : stakes.valid_poolindex poolIndex) : stakes.valid_poolid (lookupPoolId stakes poolIndex h) :=
    by
      let poolId := stakes.lookupPoolId poolIndex h
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


end Leioscrypto
