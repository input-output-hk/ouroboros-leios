-- | Empirical distributions
module DeltaQ.Leios.EmpiricalDistributions (
  empiricalDQ,
  applyTx,
  applyTxs,
  reapplyTx,
  reapplyTxs,
) where

import Data.List (sort)
import DeltaQ (DQ)
import DeltaQ.Distributions (normalDQ, measuredDQ)

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
    , (65.52, 0.01)
    , (92.20, 0.02)
    , (100, 0.03)
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
    , (90.84, 0.003)
    , (98.82, 0.01)
    , (100, 0.02)
    ]

-- | applyTx
--
-- We make use of the central limit theorem.
-- Mean and standard derivation of the corresponding
-- numbers in the csv file:
--
-- \(\mu = 10.59939845, \sigma = 25.48883812\)
applyTxs :: DQ
applyTxs = normalDQ 0.01059939845 0.02548883812

-- | reapply
--
-- We make use of the central limit theorem
-- Mean and standard derivation of the corresponding
-- numbers in the csv file:
--
-- \(\mu = 2.711165479, \sigma = 24.41685076\)
reapplyTxs :: DQ
reapplyTxs = normalDQ 0.002711165479 0.02441685076
