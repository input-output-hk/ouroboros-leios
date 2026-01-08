module Statistics.Praos (
  stakeDistribution,
  blockDistribution,
)
where

import qualified Statistics.Distribution.Exponential as S

-- | Stake Distribution
-- See: https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/deltaq/linear-leios-preliminaries.md#stake-distribution
stakeDistribution :: Double -> [Double]
stakeDistribution n = map f [0, 1 .. n]
 where
  f k = ((k + 1) / n) ** 10 - (k / n) ** 10

-- | Praos block distribution
-- The poisson schedule for the block production implies that the waiting time for the
-- next block is exponentially distributed with λ (active slot coefficient)
blockDistribution :: Double -> S.ExponentialDistribution
blockDistribution = S.exponential
