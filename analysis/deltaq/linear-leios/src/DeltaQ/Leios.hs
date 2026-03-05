-- | Leios EB diffusion
--
-- TODO:
--
-- * Model freshest first delivery (ffd)
-- * Use measurements to build DQs
module DeltaQ.Leios (
  -- * DeltaQ
  validateEB,
  fetchingEB,
  fetchingTx,
  fetchingTxs,

  -- * Estimate protocol parameters
  lVoteEstimated,
  lDiffEstimated,

  -- * Probabilities
  pValidating,
  pHeaderOnTime,
  pEBOnTime,

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
import DeltaQ.Leios.EmpiricalDistributions (
  applyTxs,
  reapplyTxs,
 )
import DeltaQ.Praos (
  BlockSize (..),
  blendedDelay,
  sendRBBody,
  sendRBHeader,
 )

maxTxsInRB, maxTxRefsInEB, maxTxsFetched :: Int
maxTxsInRB = 4
maxTxRefsInEB = 8
maxTxsFetched = 1

fetchingEB :: DQ
fetchingEB = choices [(1, blendedDelay B512), (1, blendedDelay B1024), (1, blendedDelay B2048)] -- TODO: Model FFD

-- | fetchingTx
--
-- Markov model for the TxCache that was presented by Nick in the Leios monthly
-- meeting in February:
--
-- Transition matrix: \(M = \begin{pmatrix} 1-p & p \\ 1-p/2 & p/2 \end{pmatrix}\)
--
-- Stationary condition: \(π*M = π\)
--
-- Solution: \(π_1 = (2-p)/(2+p), π_2 = 2p/(2+p)\)
--
-- +-----+---------+---------+
-- | p   | \(π_1\) | \(π_2\) |
-- +=====+=========+=========+
-- | 0.1 | 0.905   | 0.095   |
-- +-----+---------+---------+
-- | 0.3 | 0.778   | 0.222   |
-- +-----+---------+---------+
-- | 0.5 | 0.600   | 0.400   |
-- +-----+---------+---------+
-- | 0.8 | 0.385   | 0.615   |
-- +-----+---------+---------+
-- | 1.0 | 0.333   | 0.667   |
-- +-----+---------+---------+
fetchingTx :: Double -> DQ
fetchingTx p =
  choices
    [ (hitRate, wait 0.001)
    , (1 - hitRate, blendedDelay B1024)
    ]
 where
  -- Steady-state hit rate
  hitRate :: Rational
  hitRate = toRational $ 2 * p / (2 + p)

-- | fetchingTxs
--
-- Geometric Batch Size Model
fetchingTxs :: DQ
fetchingTxs =
  choices
    [ (hitRate, wait 0.001)
    , (1 - hitRate, blendedDelay B1024)
    ]
 where
  π_1 = (2 - p) / (2 + p)
  π_2 = 2 * p / (2 + p)
  p = 1.0

  hitRate :: Rational
  hitRate = π_2 * p + π_1 * (1 - p)

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
