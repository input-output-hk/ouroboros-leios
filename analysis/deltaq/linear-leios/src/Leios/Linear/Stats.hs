{-# LANGUAGE RecordWildCards #-}

module Leios.Linear.Stats where

import DeltaQ (DQ, DeltaQ (Probability, quantile, successWithin), maybeFromEventually)
import Leios.Linear.EbDiffusion (validateEB)
import Praos.BlockDiffusion (emitRBHeader)

-- | Estimate for the lVote parameter
lVoteEstimated :: Maybe Integer
lVoteEstimated = round <$> ((-) <$> q75 <*> (pure 3))
 where
  q75 = maybeFromEventually $ quantile validateEB 0.75

-- | Estimate for the lDiff parameter
lDiffEstimated :: Maybe Integer
lDiffEstimated = round <$> ((-) <$> q95 <*> q75)
 where
  q75 = maybeFromEventually $ quantile validateEB 0.75
  q95 = maybeFromEventually $ quantile validateEB 0.95

-- | Probability that the RB header arrived within lHdr
pHeaderOnTime :: Integer -> Probability DQ
pHeaderOnTime lHdr =
  successWithin
    emitRBHeader
    (toRational lHdr)

-- | Probabiliy that validation finisthed before the end of lVote
pValidating :: (Integer, Integer) -> Probability DQ
pValidating (lHdr, lVote) =
  successWithin
    validateEB
    (toRational $ 3 * lHdr + lVote)
