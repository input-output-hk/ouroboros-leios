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
maxTxsFetched = 2

fetchingEB :: DQ
fetchingEB = choices [(1, blendedDelay B512), (1, blendedDelay B1024), (1, blendedDelay B2048)] -- TODO: Model FFD

{-
doAll :: [DQ] -> DQ
doAll = foldr (./\.) (wait 0)

concurrentUpToN :: Integer -> DQ -> DQ
concurrentUpToN n dq = choices $ map f [1 .. fromInteger n]
 where
  f i = (1.0 / fromIntegral n, doAll (replicate i dq))
-}

fetchingTx :: DQ
fetchingTx = blendedDelay B256 -- TODO: Tx size

fetchingTxs :: DQ
fetchingTxs = logNormalDQ 0 1 -- FIXME: Model Tx Cache

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
