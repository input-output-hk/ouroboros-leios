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
module Analysis.Leios (
  -- * Types
  Config (..),

  -- * Probabilites
  pBlock,
  pQuorum,
  pCertified,

  -- * Expectations
  eCertifiedEB,
)
where

import DeltaQ.Leios (pValidating)
import qualified Statistics.Distribution as S
import Statistics.Leios (quorumProbability)
import Statistics.Praos (blockDistribution)

-- | 'Config' is a collection of all parameters that determine the outcome
-- of the analysis
data Config = Config
  { lHdr :: Integer
  -- ^ \(L_\text{hdr}\) parameter
  , lVote :: Integer
  -- ^ \(L_\text{vote}\) parameter
  , lDiff :: Integer
  -- ^ \(L_\text{diff}\) parameter
  , numberSPOs :: Integer
  -- ^ Number of stake-pools
  , committeeSizeEstimated :: Integer
  -- ^ Estimation of size of voting committee
  , τ :: Rational
  -- ^ Voting threshold
  , λ :: Rational
  -- ^ Block production rate parameter
  }

-- | Probability of reaching a quorum
pQuorum :: Config -> Double
pQuorum Config{..} =
  quorumProbability
    (fromInteger numberSPOs)
    (fromRational $ pValidating (lHdr, lVote))
    (fromInteger committeeSizeEstimated)
    (fromRational τ)

-- |
-- The EB is the one announced by the latest RB in the voter's current chain,
-- The EB's transactions form a valid extension of the RB that announced it,
-- For non-persistent voters, it is eligible to vote based on sortition using the announcing RB's slot number as the election identifier,
-- The EB contains at least one transaction (i.e., is not empty), as specified in the [formal specification][leios-formal-spec-empty-eb].
-- Step 4: Certification
-- During the voting period, if enough committee votes are collected such that the total stake exceeds a high threshold parameter (
-- ), for example 75%, the EB becomes certified:
--
-- TODO: Probability that the elected members of the committee received the EB
--
-- Step 5: Chain Inclusion
-- RB' may include a certificate for the EB announced in RB if and only if RB' is at least
--  slots after RB.
pBlock :: Config -> Double
pBlock Config{..} =
  S.cumulative
    (blockDistribution $ fromRational λ)
    (fromInteger $ 3 * lHdr + lVote + lDiff)

-- |
-- Any included certificate must be valid as defined in Certificate Validation.
--
-- If RB' cannot include a certificate due to timing constraints (i.e., fewer than
--  slots have elapsed since RB), then RB' operates as a standard Praos block containing its own transactions, and the EB announced by RB is discarded.
--
-- Regardless of whether RB' includes a certificate, it may optionally announce its own EB for future certification by subsequent blocks.
pCertified :: Config -> Double
pCertified c = (1 - pBlock c) * pQuorum c

-- | Expectation for the distribution of certified EBs
eCertifiedEB :: Config -> Double
eCertifiedEB Config{..} = (fromRational λ) * (1 - (fromRational λ)) ** (fromInteger $ 3 * lHdr + lVote + lDiff)
