-- | Empirical distributions
module DeltaQ.Leios.EmpiricalDistributions (
  empiricalDQ,
) where

import Data.List (sort)
import DeltaQ
import DeltaQ.Distributions

-- | 'empiricalDQ'
empiricalDQ :: [Double] -> DQ
empiricalDQ ms =
  measuredDQ $
    zip
      ([0, (1 / fromIntegral (length ms)) .. 1])
      (sort ms)
