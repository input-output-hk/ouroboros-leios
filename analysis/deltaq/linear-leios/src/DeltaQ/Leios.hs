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
import DeltaQ.Praos (
  BlockSize (..),
  blendedDelay,
  sendRBHeader,
  sendRBBody,
 )

maxTxsInRB, maxTxRefsInEB, maxTxsFetched :: Integer
maxTxsInRB = 32
maxTxRefsInEB = 128
maxTxsFetched = 16

fetchingEBHeader :: DQ
fetchingEBHeader = blendedDelay B64

fetchingEBBody :: DQ
fetchingEBBody = blendedDelay B2048

fetchingEB :: DQ
fetchingEB = fetchingEBHeader .>>. fetchingEBBody

doAll :: [DQ] -> DQ
doAll = foldr (./\.) (wait 0)

concurrentUpToN :: Integer -> DQ -> DQ
concurrentUpToN n dq = choices $ map f [1 .. fromInteger n]
 where
  f i = (1.0 / fromIntegral n, doAll (replicate i dq))

fetchingTx :: DQ
fetchingTx = blendedDelay B256 -- TODO: Tx size

fetchingTxs :: DQ
fetchingTxs = concurrentUpToN maxTxsFetched fetchingTx

processRBandEB :: DQ -> DQ
processRBandEB applyTxs = processRB ./\. processEB
 where
  processRB = sendRBBody .>>. applyTxs
  processEB = fetchingEB .>>. fetchingTxs

-- | Distribution of EB validation time
validateEB :: DQ -> DQ -> DQ
validateEB applyTx reapplyTx = processRBandEB applyTxs .>>. reapplyTxs
 where
  applyTxs = concurrentUpToN maxTxsInRB applyTx
  reapplyTxs = concurrentUpToN maxTxRefsInEB reapplyTx

-- | Estimate for the parameter \(L_\text{vote}\) using 'validateEB'
lVoteEstimated :: DQ -> DQ -> Maybe Integer
lVoteEstimated txApply txReapply = ceiling <$> ((-) <$> q75 <*> (pure 3))
 where
  q75 = maybeFromEventually $ quantile (validateEB txApply txReapply) 0.75

-- | Estimate for the parameter \(L_\text{diff}\) using 'validateEB'
lDiffEstimated :: DQ -> DQ -> Maybe Integer
lDiffEstimated txApply txReapply = ceiling <$> ((-) <$> q95 <*> q75)
 where
  dq = validateEB txApply txReapply
  q75 = maybeFromEventually $ quantile dq 0.75
  q95 = maybeFromEventually $ quantile dq 0.95

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

-- | Probability that 'validateEB' is successful before the end of \(L_\text{vote}\)
pValidating ::
  -- | txApply
  DQ ->
  -- | txReapply
  DQ ->
  -- | \(L_\text{hdr} \times L_\text{vote}\)
  (Integer, Integer) ->
  -- | Probability that the EB validation finisthes before \(3*L_\text{hdr} + L_\text{vote}\)
  Probability DQ
pValidating txApply txReapply (lHdr, lVote) =
  successWithin
    (validateEB txApply txReapply)
    (fromIntegral $ 3 * lHdr + lVote)
