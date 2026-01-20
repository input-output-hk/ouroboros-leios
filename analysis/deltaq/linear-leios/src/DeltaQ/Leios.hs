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

import DeltaQ (DQ, DeltaQ (quantile, successWithin), Outcome ((./\.), (.>>.)), ProbabilisticOutcome (Probability), maybeFromEventually, unsafeFromPositiveMeasure)
import DeltaQ.Praos (BlockSize (B2048, B64), blendedDelay, emitRBHeader, fetchingRBBody)
import qualified Numeric.Measure.Finite.Mixed as M

fetchingEBHeader :: DQ
fetchingEBHeader = blendedDelay B64

fetchingEBBody :: DQ
fetchingEBBody = blendedDelay B2048

fetchingEB :: DQ
fetchingEB = fetchingEBHeader .>>. fetchingEBBody

fetchingTxs :: DQ
fetchingTxs = unsafeFromPositiveMeasure $ M.add (M.scale 0.2 (M.dirac 0.2)) (M.scale 0.8 (M.uniform 3 6)) -- TODO: use measurements

processRBandEB :: DQ -> DQ
processRBandEB applyTxs = processRB ./\. processEB
 where
  processRB = fetchingRBBody .>>. applyTxs
  processEB = fetchingEB .>>. fetchingTxs

-- | Distribution of EB validation time
validateEB :: DQ -> DQ -> DQ
validateEB applyTx reapplyTx = processRBandEB applyTxs .>>. reapplyTxs
 where
  -- FIXME: concurrent application
  applyTxs = applyTx -- choices $ map (\i -> (1 % n, doAll (replicate i applyTx))) [1 .. fromInteger n]
  reapplyTxs = reapplyTx -- choices $ map (\i -> (1 % n, doAll (replicate i reapplyTx))) [1 .. fromInteger n]

-- | Estimate for the parameter \(L_\text{vote}\) using 'validateEB'
lVoteEstimated :: DQ -> DQ -> Maybe Integer
lVoteEstimated txApply txReapply = round <$> ((-) <$> q75 <*> (pure 3))
 where
  q75 = maybeFromEventually $ quantile (validateEB txApply txReapply) 0.75

-- | Estimate for the parameter \(L_\text{diff}\) using 'validateEB'
lDiffEstimated :: DQ -> DQ -> Maybe Integer
lDiffEstimated txApply txReapply = round <$> ((-) <$> q95 <*> q75)
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
    emitRBHeader
    (toRational lHdr)

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
    (toRational $ 3 * lHdr + lVote)
