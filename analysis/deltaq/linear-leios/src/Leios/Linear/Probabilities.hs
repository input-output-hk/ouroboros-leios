{-# LANGUAGE RecordWildCards #-}

{-
Questions to ask:
1. Probablity of certification for an EB
  * Probability to be in the voting committee
  * Probability that votes are delivered on-time
    * Probability of a quorum
    * Probability no RB/EB has been produced before:
2. Expectation of distribution of certified EBs (see throughput analysis)
3. Probability of safety property violation
-}
module Leios.Linear.Probabilities where

import Leios.Linear.Stats (pValidating)
import qualified Statistics.Distribution as S
import qualified Statistics.Distribution.Exponential as S
import qualified Statistics.Distribution.Normal as S

-- | Stake Distribution
-- See: https://github.com/input-output-hk/ouroboros-leios/blob/main/analysis/deltaq/linear-leios-preliminaries.md#stake-distribution
stakeDistribution :: Double -> [Double]
stakeDistribution n = map f [0, 1 .. n]
 where
  f k = ((k + 1) / n) ** 10 - (k / n) ** 10

bisectionSearch :: (Double -> Double) -> Double -> Double -> Double -> Integer -> Double
bisectionSearch _ low high _ 0 = (low + high) / 2
bisectionSearch f low high eps maxIter =
  let mid = (low + high) / 2
   in if high - low < eps || abs (f mid) < eps
        then mid
        else
          if f low * f mid < 0
            then bisectionSearch f low mid eps (maxIter - 1)
            else bisectionSearch f mid high eps (maxIter - 1)

calibrateCommittee :: Double -> Double -> Double
calibrateCommittee n m =
  let f x = sum (map (\s -> 1 - exp (-x * s)) (stakeDistribution n)) - m
   in bisectionSearch f m n 0.5 10

committeeDistribution :: Double -> Double -> Double -> (Double, Double)
committeeDistribution n pSuccessfulVote m =
  let m' = calibrateCommittee n m
      ps = map (\s -> pSuccessfulVote * (1 - exp (-m' * s))) (stakeDistribution n)
      μ = sum ps
      σ = sqrt $ sum $ map (\p -> p * (1 - p)) ps
   in (μ, σ)

quorumProbability :: Double -> Double -> Double -> Double -> Double
quorumProbability n pSuccessfulVote m τ =
  let (μ, σ) = (committeeDistribution n pSuccessfulVote) m
   in S.complCumulative (S.normalDistr μ σ) (τ * m)

-- | Configuration
data Config = Config
  { lHdr :: Integer
  , lVote :: Integer
  , lDiff :: Integer
  , λ :: Rational
  , nPools :: Integer
  , committeeSizeEstimated :: Integer
  , votingThreshold :: Rational
  }

-- | Probability that there is a quorum
pQuorum :: Config -> Double
pQuorum Config{..} =
  quorumProbability
    (fromInteger nPools)
    (fromRational $ pValidating (lHdr, lVote))
    (fromInteger committeeSizeEstimated)
    (fromRational votingThreshold)

-- | Praos block distribution
-- The poisson schedule for the block production implies that the waiting time for the
-- next block is exponentially distributed with λ (active slot coefficient)
praosBlockDistr :: Double -> S.ExponentialDistribution
praosBlockDistr = S.exponential

{-
The EB is the one announced by the latest RB in the voter's current chain,
The EB's transactions form a valid extension of the RB that announced it,
For non-persistent voters, it is eligible to vote based on sortition using the announcing RB's slot number as the election identifier,
The EB contains at least one transaction (i.e., is not empty), as specified in the [formal specification][leios-formal-spec-empty-eb].
Step 4: Certification
During the voting period, if enough committee votes are collected such that the total stake exceeds a high threshold parameter (
), for example 75%, the EB becomes certified:

TODO: Probability that the elected members of the committee received the EB

Step 5: Chain Inclusion
RB' may include a certificate for the EB announced in RB if and only if RB' is at least
 slots after RB.
-}
pBlock :: Config -> Double
pBlock Config{..} =
  S.cumulative
    (praosBlockDistr $ fromRational λ)
    (fromInteger $ 3 * lHdr + lVote + lDiff)

{-
Any included certificate must be valid as defined in Certificate Validation.

If RB' cannot include a certificate due to timing constraints (i.e., fewer than
 slots have elapsed since RB), then RB' operates as a standard Praos block containing its own transactions, and the EB announced by RB is discarded.

Regardless of whether RB' includes a certificate, it may optionally announce its own EB for future certification by subsequent blocks.
-}
pCertified :: Config -> Double
pCertified c = (1 - pBlock c) * pQuorum c

-- | Expectation for the distribution of certified EBs
eCertifiedEB :: Config -> Double
eCertifiedEB Config{..} = (fromRational λ) * (1 - (fromRational λ)) ** (fromInteger $ 3 * lHdr + lVote + lDiff)
