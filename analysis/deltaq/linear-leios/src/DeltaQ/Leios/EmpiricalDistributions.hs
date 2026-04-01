-- | Empirical distributions
--
-- The module provides empirical DQs for apply and reapply transactions
-- based on measurements, see linked files in the comments below.
module DeltaQ.Leios.EmpiricalDistributions (
  empiricalDQ,
  applyTx,
  applyTxs,
  reapplyTx,
  reapplyTxs,
) where

import Data.List (sort)
import DeltaQ (DQ)
import DeltaQ.Distributions (
  measuredDQ,
  scaleMixtureDQ,
 )

-- | Helper function for building a DQ from empirical data
empiricalDQ :: [Rational] -> DQ
empiricalDQ ms =
  measuredDQ $
    zip
      ([0, (1 / fromIntegral (length ms)) .. 1])
      (sort ms)

-- | DQ for applyTx
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

-- | DQ for reapplyTx
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

-- | DQ for sequential 'applyTx'
--
-- We make use of the central limit theorem and get the following normal distribution
-- as distribution of sequential application of 'applyTx'
--
-- \(nZ \sim \mathcal{N}(\mu,\sigma^{2})\)
--
-- where \(n\) is the number of transactions. Mean and standard derivation
-- from the corresponding numbers in the csv file are:
--
-- \(\mu = 10.59939845, \sigma = 25.48883812\)
--
-- We assume a uniform distribution for the number of transactions \(n \sim \mathcal{U}(1,N)\)
-- upto \(N=100\).
--
-- The resulting distribution function is the scale mixture distribution
-- and the cumulative distribution function is:
--
-- \(F(x) = \frac{1}{N} \sum_1^N \Phi\left(\frac{x - n\mu}{n\sigma}\right)\)
applyTxs :: DQ
applyTxs = scaleMixtureDQ 100 0.01059939845 0.02548883812

-- | DQ for sequential 'reapplyTx'
--
-- We make use of the central limit theorem and get the following normal distribution
-- as distribution of sequential application of 'reapplyTx'
--
-- \(nZ \sim \mathcal{N}(\mu,\sigma^{2})\)
--
-- where \(n\) is the number of transactions. Mean and standard derivation
-- from the corresponding numbers in the csv file are:
--
-- \(\mu = 2.711165479, \sigma = 24.41685076\)
--
-- We assume a uniform distribution for the number of transactions \(n \sim \mathcal{U}(1,N)\)
-- upto \(N=2500\).
--
-- The resulting distribution function is the scale mixture distribution
-- and the cumulative distribution function is:
--
-- \(F(x) = \frac{1}{N} \sum_1^N \Phi\left(\frac{x - n\mu}{n\sigma}\right)\)
reapplyTxs :: DQ
reapplyTxs = scaleMixtureDQ 2500 0.002711165479 0.02441685076
