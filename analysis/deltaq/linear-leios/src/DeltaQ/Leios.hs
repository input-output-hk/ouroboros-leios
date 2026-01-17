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

  -- * Util
  reduceComplexity,
  sequentiallyWithResample,
) where

import Data.List (sort)
import Data.Maybe (mapMaybe)
import Data.Ratio ((%))
import DeltaQ (DQ, DeltaQ (deadline, quantile, successWithin), Eventually (..), Outcome (..), ProbabilisticOutcome (Probability), choices, maybeFromEventually, unsafeFromPositiveMeasure, wait)
import DeltaQ.Leios.EmpiricalDistributions (measuredDQ)
import DeltaQ.Praos (BlockSize (B2048, B64), blendedDelay, emitRBHeader, fetchingRBBody)
import qualified Numeric.Measure.Finite.Mixed as M
import System.Random (Random (randomRs), RandomGen)

fetchingEBHeader :: DQ
fetchingEBHeader = blendedDelay B64

fetchingEBBody :: DQ
fetchingEBBody = blendedDelay B2048

fetchingEB :: RandomGen g => g -> DQ
fetchingEB g = sequentiallyWithResample g fetchingEBHeader fetchingEBBody

fetchingTxs :: DQ
fetchingTxs = unsafeFromPositiveMeasure $ M.add (M.scale 0.2 (M.dirac 0.2)) (M.scale 0.8 (M.uniform 3 6)) -- TODO: use measurements

processRBandEB :: RandomGen g => g -> DQ -> DQ
processRBandEB g applyTxs = processRB ./\. processEB
 where
  processRB = sequentiallyWithResample g fetchingRBBody applyTxs
  processEB = sequentiallyWithResample g (fetchingEB g) fetchingTxs

-- | Distribution of EB validation time
validateEB :: RandomGen g => g -> DQ -> DQ -> DQ
validateEB g applyTx reapplyTx = sequentiallyWithResample g (processRBandEB g applyTxs) reapplyTxs
 where
  n = 32
  doAll = foldr (./\.) (wait 0)
  applyTxs = choices $ map (\i -> (1 % n, doAll (replicate i applyTx))) [1 .. fromInteger n]
  reapplyTxs = choices $ map (\i -> (1 % n, doAll (replicate i reapplyTx))) [1 .. fromInteger n]

-- | Estimate for the parameter \(L_\text{vote}\) using 'validateEB'
lVoteEstimated :: RandomGen g => g -> DQ -> DQ -> Maybe Integer
lVoteEstimated g txApply txReapply = round <$> ((-) <$> q75 <*> (pure 3))
 where
  q75 = maybeFromEventually $ quantile (validateEB g txApply txReapply) 0.75

-- | Estimate for the parameter \(L_\text{diff}\) using 'validateEB'
lDiffEstimated :: RandomGen g => g -> DQ -> DQ -> Maybe Integer
lDiffEstimated g txApply txReapply = round <$> ((-) <$> q95 <*> q75)
 where
  dq = validateEB g txApply txReapply
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
  RandomGen g =>
  g ->
  -- | txApply
  DQ ->
  -- | txReapply
  DQ ->
  -- | \(L_\text{hdr} \times L_\text{vote}\)
  (Integer, Integer) ->
  -- | Probability that the EB validation finisthes before \(3*L_\text{hdr} + L_\text{vote}\)
  Probability DQ
pValidating g txApply txReapply (lHdr, lVote) =
  successWithin
    (validateEB g txApply txReapply)
    (toRational $ 3 * lHdr + lVote)

rand :: RandomGen g => g -> Int -> [Rational]
rand g n = map toRational $ sort $ take n (randomRs (0.000001, 0.999999) g :: [Double])

reduceComplexity :: RandomGen g => g -> Int -> DQ -> DQ
reduceComplexity g n dq =
  let vals = rand g n
      qs = mapMaybe (maybeFromEventually . quantile dq) vals
      ms = zip vals qs
   in case deadline dq of
        Occurs d -> measuredDQ $ ms ++ [(1 % 1, d)]
        Abandoned -> measuredDQ ms

sequentiallyWithResample :: RandomGen g => g -> DQ -> DQ -> DQ
sequentiallyWithResample g a b = reduceComplexity g 20 $ sequentially a b
