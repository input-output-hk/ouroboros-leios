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
module Leios.Linear.Stats where

import DeltaQ (DQ, DeltaQ (Probability, quantile, successWithin), maybeFromEventually)
import Leios.Linear.EbDiffusion (validateEB)
import Praos.BlockDiffusion (emitRBHeader)
import qualified Statistics.Distribution as S
import qualified Statistics.Distribution.Exponential as S
import qualified Statistics.Distribution.Normal as S

data Config = Config
  { lHdr :: Rational
  , lVote :: Rational
  , lDiff :: Rational
  , lambda :: Rational
  , nPools :: Double
  , committeeSizeEstimated :: Double
  , votingThreshold :: Rational
  }

-- The quantiles of validateEB are used to estimate L-vote and L-diff
q75, q95, q99 :: Maybe Rational
q75 = maybeFromEventually $ quantile validateEB 0.75
q95 = maybeFromEventually $ quantile validateEB 0.95
q99 = maybeFromEventually $ quantile validateEB 0.99

lVoteEstimated :: Maybe Integer
lVoteEstimated = round <$> liftA2 (-) q75 (pure 3)

lDiffEstimated :: Maybe Integer
lDiffEstimated = round <$> liftA2 (-) q95 q75

{-
Step 1: Block Production
The poisson schedule for the block production implies that the waiting time for the
next block is exponentially distributed with lambda (active slot coefficient)
-}
praosBlockDistr :: Config -> S.ExponentialDistribution
praosBlockDistr Config{..} = S.exponential (fromRational lambda)

{-
Step 2: EB Distribution
Step 3: Committee Validation
The RB header arrived within
-}
pHeaderOnTime :: Config -> Probability DQ
pHeaderOnTime Config{..} = successWithin emitRBHeader lHdr

{-
It has not detected any equivocating RB header for the same slot,
It finished validating the EB before slots after the EB slot
-}
pValidating :: Config -> Probability DQ
pValidating Config{..} = successWithin validateEB n
 where
  n = 3 * lHdr + lVote

stakeDistribution :: Config -> [Double]
stakeDistribution Config{..} = map f [0, 1 .. nPools]
 where
  f k = ((k + 1) / nPools) ** 10 - (k / nPools) ** 10

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

calibrateCommittee :: Config -> Double -> Double
calibrateCommittee c@Config{..} m =
  let f x = sum (map (\s -> 1 - exp (-x * s)) (stakeDistribution c)) - m
   in bisectionSearch f m nPools 0.5 10

committeeDistribution :: Config -> Double -> Double -> (Double, Double)
committeeDistribution c pSuccessfulVote m =
  let m' = calibrateCommittee c m
      ps = map (\s -> pSuccessfulVote * (1 - exp (-m' * s))) (stakeDistribution c)
      μ = sum ps
      σ = sqrt $ sum $ map (\p -> p * (1 - p)) ps
   in (μ, σ)

quorumProbability :: Config -> Double -> Double -> Double -> Double
quorumProbability c pSuccessfulVote m τ =
  let (μ, σ) = (committeeDistribution c pSuccessfulVote) m
   in S.complCumulative (S.normalDistr μ σ) (τ * m)

pQuorum :: Config -> Double
pQuorum c@Config{..} = quorumProbability c (fromRational $ pValidating c) committeeSizeEstimated (fromRational votingThreshold)

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
pBlock c@Config{..} = S.cumulative (praosBlockDistr c) n
 where
  n = fromRational $ 3 * lHdr + lVote + lDiff

{-
Any included certificate must be valid as defined in Certificate Validation.

If RB' cannot include a certificate due to timing constraints (i.e., fewer than
 slots have elapsed since RB), then RB' operates as a standard Praos block containing its own transactions, and the EB announced by RB is discarded.

Regardless of whether RB' includes a certificate, it may optionally announce its own EB for future certification by subsequent blocks.
-}
pCertified :: Config -> Double
pCertified c = (1 - pBlock c) * pQuorum c

{-
Assumption: The mem-pools are synchronized up to
This implies, that EBs are diffused on time
-}
eCertifiedEB :: Config -> Double
eCertifiedEB Config{..} = l * ((1 - l) ** n)
 where
  n = fromRational $ 3 * lHdr + lVote + lDiff
  l = fromRational lambda
