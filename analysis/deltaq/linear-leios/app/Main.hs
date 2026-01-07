{-# LANGUAGE RecordWildCards #-}

module Main where

import Data.Ratio ((%))
import DeltaQ
import Graphics.Rendering.Chart.Backend.Cairo
import Graphics.Rendering.Chart.Easy
import Leios.Linear.EbDiffusion
import Leios.Linear.Probabilities
import Leios.Linear.Stats
import Praos.BlockDiffusion
import Text.Printf

-- | main
main :: IO ()
main =
  mainWith
    Config
      { -- cip
        lHdr = 1
      , lVote = 4
      , lDiff = 7
      , votingThreshold = 3 % 4
      , -- estimate
        committeeSizeEstimated = 600
      , -- mainnet
        λ = 1 % 20
      , nPools = 2500
      }

mainWith :: Config -> IO ()
mainWith c@Config{..} = do
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
            n = fromInteger nPools
            t = fromRational votingThreshold
            vs = [(x, quorumProbability n x s t) | x <- xs]
         in do
              layout_title .= "Quorum distribution"
              plot (line "pQuorum" [vs])

  maybe (print "Nothing") (printf "Estimate for lVote: %d\n") lVoteEstimated
  maybe (print "Nothing") (printf "Estimate for lDiff: %d\n") lDiffEstimated

  printf
    "Probability that a header arrives on time: %.2f\n"
    $ (fromRational (pHeaderOnTime lHdr) :: Double)
  printf
    "Probability that EB validation is completed before voting is over: %.2f\n"
    $ (fromRational (pValidating (lHdr, lVote)) :: Double)
  printf "Probability of Quorum: %.2f\n" (pQuorum c)
  printf
    "Probability that the next Praos block has already been produced after the waiting period: %.4f\n"
    (pBlock c)
  printf "Probability that an EB is certified: %.4f\n" (pCertified c)
  printf "Expected time for certified EB: %.2f slots\n" (1 / (eCertifiedEB c))
