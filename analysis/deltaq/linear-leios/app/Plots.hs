module Main where

import Data.Ratio ((%))
import DeltaQ
import DeltaQ.Leios (validateEB)
import DeltaQ.Leios.EmpiricalDistributions (applyTx, reapplyTx)
import DeltaQ.Praos (blendedDelay, blockSizes)
import Graphics.Rendering.Chart.Backend.Cairo
import Graphics.Rendering.Chart.Easy
import Statistics.Leios (quorumProbability)

main :: IO ()
main = do
  let committeeSizeEstimated = 600 :: Integer
  let numberSPOs = 2500 :: Integer
  let τ = 3 % 4
  _ <-
    renderableToFile def{_fo_format = SVG} "tx-apply.svg" $
      toRenderable $
        plotCDFWithQuantiles "Tx Apply" [0.75, 0.95, 0.99] applyTx
  _ <-
    renderableToFile def{_fo_format = SVG} "tx-reapply.svg" $
      toRenderable $
        plotCDFWithQuantiles "Tx Reapply" [0.75, 0.95, 0.99] reapplyTx
  _ <-
    renderableToFile def{_fo_format = SVG} "block-diffustion.svg" $
      toRenderable $
        plotCDFs "Block diffusion" $
          zip (map show blockSizes) (map blendedDelay blockSizes)
  _ <-
    renderableToFile def{_fo_format = SVG} "validateEB.svg" $
      toRenderable $
        plotCDFWithQuantiles "EB diffusion" [0.75, 0.95, 0.99] validateEB
  _ <-
    renderableToFile def{_fo_format = SVG} "quorumProb.svg" $
      toRenderable $
        let xs = [0.50, 0.51 .. 1]
            s = fromInteger committeeSizeEstimated
            n = fromInteger numberSPOs
            vs = [(x, quorumProbability n x s (fromRational τ)) | x <- xs]
         in do
              layout_title .= "Quorum distribution"
              plot (line "pQuorum" [vs])
  return ()
