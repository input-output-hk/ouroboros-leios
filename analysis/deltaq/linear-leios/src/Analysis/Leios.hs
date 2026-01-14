{-# LANGUAGE RecordWildCards #-}

-- |
-- Questions to ask:
--
-- * Probablity of certification for an EB
--
--     * Probability to be in the voting committee
--     * Probability that votes are delivered on-time
--
--         * Probability of a quorum
--         * Probability no RB/EB has been produced before:
--
-- * Expectation of distribution of certified EBs (see throughput analysis)
--
-- * Probability of safety property violation
module Analysis.Leios (
  -- * Types
  Config (..),

  -- * Probabilites
  pInterruptedByNewBlock,
  pQuorum,
  pCertified,

  -- * Expectations
  eCertified,
)
where

import DeltaQ (DQ)
import DeltaQ.Leios (pValidating)
import qualified Statistics.Distribution as S
import Statistics.Leios (quorumProbability)
import Statistics.Praos (blockDistribution)

-- | 'Config' is a collection of all parameters that determine the outcome
-- of the analysis
data Config = Config
  { name :: String
  -- ^ name
  , lHdr :: !Integer
  -- ^ \(L_\text{hdr}\) parameter
  , lVote :: !Integer
  -- ^ \(L_\text{vote}\) parameter
  , lDiff :: !Integer
  -- ^ \(L_\text{diff}\) parameter
  , numberSPOs :: !Integer
  -- ^ Number of stake-pools
  , committeeSizeEstimated :: !Integer
  -- ^ Estimation of size of voting committee
  , τ :: !Rational
  -- ^ Voting threshold
  , λ :: !Rational
  -- ^ Block production rate parameter
  , applyTxs :: !DQ
  -- ^ DQ for applyTxs
  , reapplyTxs :: !DQ
  -- ^ DQ for reapplyTxs
  }
  deriving (Show, Eq)

-- | Probability of reaching a quorum
pQuorum :: Config -> Double
pQuorum Config{..} =
  quorumProbability
    (fromInteger numberSPOs)
    (fromRational $ pValidating applyTxs reapplyTxs (lHdr, lVote))
    (fromInteger committeeSizeEstimated)
    (fromRational τ)

-- | Probability that validation is done before there is new block
pInterruptedByNewBlock :: Config -> Double
pInterruptedByNewBlock Config{..} =
  S.cumulative
    (blockDistribution $ fromRational λ)
    (fromInteger $ 3 * lHdr + lVote + lDiff)

-- | Probability that an EB will be certified
pCertified :: Config -> Double
pCertified c = (1 - pInterruptedByNewBlock c) * pQuorum c

-- | Expectation for the distribution of certified EBs over time
eCertified :: Config -> Double
eCertified Config{..} = (fromRational λ) * (1 - (fromRational λ)) ** (fromInteger $ 3 * lHdr + lVote + lDiff)
