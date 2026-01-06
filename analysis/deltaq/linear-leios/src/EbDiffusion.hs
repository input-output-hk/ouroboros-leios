{- Leios EB diffusion
-}
module EbDiffusion where

import qualified Numeric.Measure.Finite.Mixed as M

import DeltaQ (DQ, Outcome (wait, (./\.), (.>>.)), unsafeFromPositiveMeasure)

import RbDiffusion (BlockSize (B2048, B64), blendedDelay, fetchingRBBody)

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
fetchingTxs = unsafeFromPositiveMeasure $ M.add (M.scale 0.2 (M.dirac 0.2)) (M.scale 0.8 (M.uniform 2 4))

processRBandEB :: DQ
processRBandEB = processRB ./\. processEB
 where
  processRB = fetchingRBBody .>>. applyTxs
  processEB = fetchingEB .>>. fetchingTxs

validateEB :: DQ
validateEB = processRBandEB .>>. reapplyTxs
