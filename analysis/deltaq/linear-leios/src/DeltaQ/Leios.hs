-- | Leios EB diffusion
--
-- TODO:
--
-- * Model freshest first delivery (ffd)
-- * Use measurements to build DQs
module DeltaQ.Leios (
  -- * DeltaQ
  validateEB,

  -- * Estimate protocol parameters
  lVoteEstimated,
  lDiffEstimated,

  -- * Probabilities
  pValidating,
  pHeaderOnTime,
  pEBOnTime,

  -- * DQs
  applyTx,
  reapplyTx,
) where

import DeltaQ (
  DQ,
  DeltaQ (quantile, successWithin),
  Outcome ((./\.), (.>>.)),
  ProbabilisticOutcome (Probability),
  choices,
  maybeFromEventually,
  wait,
 )
import DeltaQ.Distributions (logNormalDQ)
import DeltaQ.Praos (
  BlockSize (..),
  blendedDelay,
  sendRBBody,
  sendRBHeader,
 )

maxTxsInRB, maxTxRefsInEB, maxTxsFetched :: Int
maxTxsInRB = 4
maxTxRefsInEB = 8
maxTxsFetched = 64

fetchingEB :: DQ
fetchingEB = choices [(1, blendedDelay B512), (1, blendedDelay B1024), (1, blendedDelay B2048)] -- TODO: Model FFD

doAll :: [DQ] -> DQ
doAll = foldr (./\.) (wait 0)

{-
concurrentUpToN :: Integer -> DQ -> DQ
concurrentUpToN n dq = choices $ map f [1 .. fromInteger n]
 where
  f i = (1.0 / fromIntegral n, doAll (replicate i dq))
-}

-- Markov model that was presented by Nick in the Leios monthly
-- meeting in February:
--
-- Transition matrix M:
--
-- [ 1−p    p   ]
-- [ 1-p/2  p/2 ]
--
-- Stationary condition: π*M = π
--
-- Solution:
--    π_1 = (2-p)/(2+p)
--    π_2 = 2p/(2+p)
--
-- +-----+-------+-------+

-- | p   | π_1   | π_p   |
-- |-----+-------+-------|
-- | 0.1 | 0.905 | 0.095 |
-- | 0.3 | 0.778 | 0.222 |
-- | 0.5 | 0.600 | 0.400 |
-- | 0.8 | 0.385 | 0.615 |
-- | 1.0 | 0.333 | 0.667 |
-- +-----+-------+-------+

-- Steady-state hit rate
hitRate :: Double -> Rational
hitRate p = toRational $ 2 * p / (2 + p)

fetchingTx :: Double -> DQ
fetchingTx p =
  choices
    [ (hitRate p, wait 0.001)
    , (1 - hitRate p, blendedDelay B1024)
    ]

fetchingTxs :: DQ
fetchingTxs = doAll $ replicate maxTxsFetched (fetchingTx 1.0)

applyTx :: DQ
applyTx = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx

reapplyTx :: DQ
reapplyTx = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx

applyTxs :: DQ
applyTxs = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx

reapplyTxs :: DQ
reapplyTxs = logNormalDQ 0 1 -- FIXME: concurrentUpToN maxTxRefsInEB reapplyTx

processRBandEB :: DQ
processRBandEB = processRB ./\. processEB
 where
  processRB = sendRBBody .>>. applyTxs
  processEB = fetchingEB .>>. fetchingTxs

-- | Distribution of EB validation time
validateEB :: DQ
validateEB = processRBandEB .>>. reapplyTxs

-- | Estimate for the parameter \(L_\text{vote}\) using 'validateEB'
lVoteEstimated :: Maybe Integer
lVoteEstimated = ceiling <$> ((-) <$> q75 <*> (pure 3))
 where
  q75 = maybeFromEventually $ quantile validateEB 0.75

-- | Estimate for the parameter \(L_\text{diff}\) using 'validateEB'
lDiffEstimated :: Maybe Integer
lDiffEstimated = ceiling <$> ((-) <$> q95 <*> q75)
 where
  q75 = maybeFromEventually $ quantile validateEB 0.75
  q95 = maybeFromEventually $ quantile validateEB 0.95

-- | Probability that 'emitRBHeader' is within \(L_\text{hdr}\)
pHeaderOnTime ::
  -- | \(L_\text{hdr}\)
  Integer ->
  -- | Probability that the RB header is within \(L_\text{hdr}\)
  Probability DQ
pHeaderOnTime lHdr =
  successWithin
    sendRBHeader
    (fromIntegral lHdr)

-- | Probability that 'emitRBHeader' is within \(L_\text{hdr}\)
pEBOnTime ::
  -- | \(L_\text{hdr}\)
  Integer ->
  -- | Probability that the RB header is within \(L_\text{hdr}\)
  Probability DQ
pEBOnTime lHdr =
  successWithin
    fetchingEB
    (fromIntegral lHdr)

-- | Probability that 'validateEB' is successful before the end of \(L_\text{vote}\)
pValidating ::
  -- | \(L_\text{hdr} \times L_\text{vote}\)
  (Integer, Integer) ->
  -- | Probability that the EB validation finisthes before \(3*L_\text{hdr} + L_\text{vote}\)
  Probability DQ
pValidating (lHdr, lVote) =
  successWithin validateEB (fromIntegral $ 3 * lHdr + lVote)
