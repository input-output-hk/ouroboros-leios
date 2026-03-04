-- | Empirical distributions
module DeltaQ.Leios.EmpiricalDistributions (
  empiricalDQ,
  applyTx,
  applyTxs,
  reapplyTx,
  reapplyTxs,
) where

import Data.List (sort)
import DeltaQ
import DeltaQ.Distributions

-- | 'empiricalDQ'
empiricalDQ :: [Rational] -> DQ
empiricalDQ ms =
  measuredDQ $
    zip
      ([0, (1 / fromIntegral (length ms)) .. 1])
      (sort ms)

applyTx :: DQ
applyTx = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx

reapplyTx :: DQ
reapplyTx = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx

applyTxs :: DQ
applyTxs = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx

reapplyTxs :: DQ
reapplyTxs = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx
