{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Analysis.Leios
import qualified Data.ByteString.Lazy as BL
import Data.Csv (FromNamedRecord (..), Header, decodeByName, (.:))
import Data.Ratio ((%))
import qualified Data.Vector as V
import DeltaQ
import DeltaQ.Leios
import DeltaQ.Leios.EmpiricalDistributions (empiricalDQ)
import DeltaQ.Praos
import GHC.Generics
import Graphics.Rendering.Chart.Backend.Cairo
import Graphics.Rendering.Chart.Easy
import Statistics.Leios (quorumProbability)
import System.Random
import Text.Printf

data BlockEDF = BlockEDF
  { txCount :: !Int
  , blockSize :: !Double
  , apply :: !Double
  , reapply :: !Double
  , fraction :: !Double
  }
  deriving (Show, Eq, Generic)

instance FromNamedRecord BlockEDF where
  parseNamedRecord m =
    BlockEDF
      <$> m .: "Tx count"
      <*> m .: "Block size [kB]"
      <*> m .: "Apply [ms]"
      <*> m .: "Reapply [ms]"
      <*> m .: "Fraction of blocks [%/100]"

readFromFile :: IO (Either String (Header, V.Vector BlockEDF))
readFromFile = decodeByName @BlockEDF <$> BL.readFile "../../../post-cip/empirical-distributions/block-edf.csv"

sampleElements :: RandomGen g => g -> Int -> [a] -> [a]
sampleElements g n xs =
  let is = take n $ randomRs (0, length xs - 1) g
   in [xs !! i | i <- is]

-- | main
main :: IO ()
main = do
  Right (_, edf) <- readFromFile
  let txApplyTimes = V.toList (V.map ((/ 1000) . apply) edf)
  let txReapplyTimes = V.toList (V.map ((/ 1000) . reapply) edf)

  -- Reduce sample size for better performance
  let sampleSize = 10
  let seed = 100
  let gen = mkStdGen seed
  let txApplyTimesReduced = sampleElements gen sampleSize txApplyTimes
  let txReapplyTimesReduced = sampleElements gen sampleSize txReapplyTimes

  mainWith
    Config
      { -- cip
        lHdr = 1
      , lVote = 4
      , lDiff = 7
      , τ = 3 % 4
      , -- estimate
        committeeSizeEstimated = 600
      , -- mainnet
        λ = 1 % 20
      , numberSPOs = 2500
      , -- empirical cdf
        applyTxs = empiricalDQ txApplyTimesReduced
      , reapplyTxs = empiricalDQ txReapplyTimesReduced
      }

mainWith :: Config -> IO ()
mainWith c@Config{..} = do
  -- _ <-
  --   renderableToFile def{_fo_format = SVG} "tx-apply.svg" $
  --     toRenderable $
  --       plotCDFWithQuantiles "Tx Apply" [0.75, 0.95, 0.99] (measuredDQ ms)
  -- _ <-
  --   renderableToFile def{_fo_format = SVG} "block-diffustion.svg" $
  --     toRenderable $
  --       plotCDFs "Block diffusion" $
  --         zip (map show blockSizes) (map blendedDelay blockSizes)
  -- _ <-
  --   renderableToFile def{_fo_format = SVG} "validateEB.svg" $
  --     toRenderable $
  --       plotCDFWithQuantiles "EB diffusion" [0.75, 0.95, 0.99] (validateEB applyTxs reapplyTxs)
  -- _ <-
  --   renderableToFile def{_fo_format = SVG} "quorumProb.svg" $
  --     toRenderable $
  --       let xs = [0.50, 0.51 .. 1]
  --           s = fromInteger committeeSizeEstimated
  --           n = fromInteger numberSPOs
  --           t = fromRational τ
  --           vs = [(x, quorumProbability n x s t) | x <- xs]
  --        in do
  --             layout_title .= "Quorum distribution"
  --             plot (line "pQuorum" [vs])

  maybe (print @String "Nothing") (printf "Estimate for lVote: %d\n") (lVoteEstimated applyTxs reapplyTxs)
  maybe (print @String "Nothing") (printf "Estimate for lDiff: %d\n") (lDiffEstimated applyTxs reapplyTxs)

  printf
    "Probability that a header arrives on time: %.2f\n"
    $ (fromRational (pHeaderOnTime lHdr) :: Double)
  printf
    "Probability that EB validation is completed before voting is over: %.2f\n"
    $ (fromRational (pValidating applyTxs reapplyTxs (lHdr, lVote)) :: Double)
  printf "Probability of Quorum: %.2f\n" (pQuorum c)
  printf
    "Probability that the next Praos block has already been produced after the waiting period: %.4f\n"
    (pInterruptedByNewBlock c)
  printf "Probability that an EB is certified: %.4f\n" (pCertified c)
  printf "Expected time for certified EB: %.2f slots\n" (1 / (eCertified c))
