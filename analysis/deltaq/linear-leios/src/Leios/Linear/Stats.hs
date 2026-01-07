{-# LANGUAGE RecordWildCards #-}

module Leios.Linear.Stats where

import DeltaQ (DQ, DeltaQ (Probability, quantile, successWithin), maybeFromEventually)
import Leios.Linear.EbDiffusion (validateEB)
import Praos.BlockDiffusion (emitRBHeader)

data Config = Config
  { lHdr :: Integer
  , lVote :: Integer
  , lDiff :: Integer
  , λ :: Rational
  , nPools :: Integer
  , committeeSizeEstimated :: Integer
  , votingThreshold :: Rational
  }

-- | Estimate for the lVote parameter
lVoteEstimated :: Maybe Integer
lVoteEstimated = round <$> liftA2 (-) q75 (pure 3)
 where
  q75 = maybeFromEventually $ quantile validateEB 0.75

-- | Estimate for the lDiff parameter
lDiffEstimated :: Maybe Integer
lDiffEstimated = round <$> liftA2 (-) q95 q75
 where
  q75 = maybeFromEventually $ quantile validateEB 0.75
  q95 = maybeFromEventually $ quantile validateEB 0.95

-- | Probability that the RB header arrived within lHdr
pHeaderOnTime :: Config -> Probability DQ
pHeaderOnTime Config{..} =
  successWithin
    emitRBHeader
    (toRational lHdr)

-- | Probabiliy that validation finisthed before the end of lVote
pValidating :: Config -> Probability DQ
pValidating Config{..} =
  successWithin
    validateEB
    (toRational $ 3 * lHdr + lVote)
