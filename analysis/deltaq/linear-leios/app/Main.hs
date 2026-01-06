module Main where

import EbDiffusion
import RbDiffusion
import Stats

import DeltaQ

import Text.Printf

import Graphics.Rendering.Chart.Backend.Cairo
import Graphics.Rendering.Chart.Easy

main :: IO ()
main = do
  _ <- renderableToFile def{_fo_format = SVG} "block-diffustion.svg" $ toRenderable $ plotCDFs "Block diffusion" $ zip (map show blockSizes) (map blendedDelay blockSizes)
  _ <- renderableToFile def{_fo_format = SVG} "validateEB.svg" $ toRenderable $ plotCDFWithQuantiles "EB diffusion" [0.75, 0.95, 0.99] validateEB
  _ <-
    renderableToFile def{_fo_format = SVG} "quorumProb.svg" $
      toRenderable $
        let xs = [0.50, 0.51 .. 1]
            vs = [(x, quorumProbability x committeeSizeEstimated (fromRational votingThreshold)) | x <- xs]
         in do
              layout_title .= "Quorum distribution"
              plot (line "pQuorum" [vs])

  maybe (print "Nothing") (printf "Estimate for lVote: %d\n") lVoteEstimated
  maybe (print "Nothing") (printf "Estimate for lDiff: %d\n") lDiffEstimated

  printf "Probability that a header arrives on time: %.2f\n" $ (fromRational pHeaderOnTime :: Double)
  printf "Probability that EB validation is completed before voting is over: %.2f\n" $ (fromRational pValidating :: Double)
  printf "Probability of Quorum: %.2f\n" pQuorum
  printf "Probability that the next Praos block has already been produced after the waiting period: %.4f\n" pBlock
  printf "Probability that an EB is certified: %.4f\n" pCertified
  printf "Expected time for certified EB: %.2f slots" (1 / eCertifiedEB)
