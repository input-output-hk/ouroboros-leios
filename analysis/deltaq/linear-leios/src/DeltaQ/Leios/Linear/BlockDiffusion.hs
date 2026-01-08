{- Leios EB diffusion
TODO: model FFD
-}
module DeltaQ.Leios.Linear.BlockDiffusion (
  -- * DeltaQ
  validateEB,

  -- * Estimate protocol parameters
  lVoteEstimated,
  lDiffEstimated,

  -- * Probabilities
  pValidating,
  pHeaderOnTime,
) where

import DeltaQ (DQ, DeltaQ (Probability, quantile, successWithin), Outcome (wait, (./\.), (.>>.)), maybeFromEventually, unsafeFromPositiveMeasure)
import DeltaQ.Praos.BlockDiffusion (BlockSize (B2048, B64), blendedDelay, emitRBHeader, fetchingRBBody)
import qualified Numeric.Measure.Finite.Mixed as M

fetchingEBHeader :: DQ
fetchingEBHeader = blendedDelay B64

fetchingEBBody :: DQ
fetchingEBBody = blendedDelay B2048

fetchingEB :: DQ
fetchingEB = fetchingEBHeader .>>. fetchingEBBody

applyTxs :: DQ
applyTxs = wait 0.4 -- TODO: use measurements

reapplyTxs :: DQ
reapplyTxs = wait 0.3 -- TODO: use measurements

fetchingTxs :: DQ
fetchingTxs = unsafeFromPositiveMeasure $ M.add (M.scale 0.2 (M.dirac 0.2)) (M.scale 0.8 (M.uniform 2 4)) -- TODO: use measurements

processRBandEB :: DQ
processRBandEB = processRB ./\. processEB
 where
  processRB = fetchingRBBody .>>. applyTxs
  processEB = fetchingEB .>>. fetchingTxs

-- | Distribution of EB validation time
validateEB :: DQ
validateEB = processRBandEB .>>. reapplyTxs

-- | Estimate for the parameter \(L_\text{vote}\) using 'validateEB'
lVoteEstimated :: Maybe Integer
lVoteEstimated = round <$> ((-) <$> q75 <*> (pure 3))
 where
  q75 = maybeFromEventually $ quantile validateEB 0.75

-- | Estimate for the parameter \(L_\text{diff}\) using 'validateEB'
lDiffEstimated :: Maybe Integer
lDiffEstimated = round <$> ((-) <$> q95 <*> q75)
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
    emitRBHeader
    (toRational lHdr)

-- | Probability that 'validateEB' is successful before the end of \(L_\text{vote}\)
pValidating ::
  -- | \(L_\text{hdr} \times L_\text{vote}\)
  (Integer, Integer) ->
  -- | Probability that the EB validation finisthes before \(3*L_\text{hdr} + L_\text{vote}\)
  Probability DQ
pValidating (lHdr, lVote) =
  successWithin
    validateEB
    (toRational $ 3 * lHdr + lVote)
