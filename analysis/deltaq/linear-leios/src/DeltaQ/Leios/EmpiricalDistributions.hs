-- | Empirical distributions
module DeltaQ.Leios.EmpiricalDistributions (
  empiricalDQ,
  applyTx,
  applyTxs,
  reapplyTx,
  reapplyTxs,
) where

import Data.List (sort)
import DeltaQ (DQ, choices)
import DeltaQ.Distributions (logNormalDQ, measuredDQ)

-- | 'empiricalDQ'
empiricalDQ :: [Rational] -> DQ
empiricalDQ ms =
  measuredDQ $
    zip
      ([0, (1 / fromIntegral (length ms)) .. 1])
      (sort ms)

-- | applyTx
--
-- Data from [block-edf.csv](https://github.com/input-output-hk/ouroboros-leios/blob/main/post-cip/empirical-distributions/block-edf.csv)
--
-- Distribution of apply:
--
-- +----------+--------+
-- | \< 5 ms  | 28.20% |
-- +----------+--------+
-- | 5-10 ms  | 37.32% |
-- +----------+--------+
-- | 10-20 ms | 26.68% |
-- +----------+--------+
-- | \> 20 ms | 7.80%  |
-- +----------+--------+
applyTx :: DQ
applyTx =
  measuredDQ
    [ (28.20, 0.005)
    , (37.32, 0.01)
    , (26.68, 0.02)
    , (7.80, 0.03)
    ]

-- | reapplyTx
--
-- Data from [block-edf.csv](https://github.com/input-output-hk/ouroboros-leios/blob/main/post-cip/empirical-distributions/block-edf.csv)
--
-- Distribution of reapply:
--
-- +----------+--------+
-- | \< 1 ms  | 41.85% |
-- +----------+--------+
-- | 1–3 ms   | 48.99% |
-- +----------+--------+
-- | 3–10 ms  | 7.98%  |
-- +----------+--------+
-- | \> 10 ms | 1.17%  |
-- +----------+--------+
reapplyTx :: DQ
reapplyTx =
  measuredDQ
    [ (41.85, 0.001)
    , (48.99, 0.003)
    , (7.98, 0.01)
    , (1.17, 0.02)
    ]

applyTxs :: DQ
applyTxs = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx

reapplyTxs :: DQ
reapplyTxs = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx
