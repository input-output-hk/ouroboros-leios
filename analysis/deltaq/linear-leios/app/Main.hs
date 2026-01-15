{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Analysis.Leios
import Control.Concurrent
import Control.Concurrent.Async
import qualified Data.ByteString.Lazy as BL
import Data.Csv (DefaultOrdered (..), FromNamedRecord (..), Header, ToNamedRecord (..), decodeByName, encodeDefaultOrderedByName, (.:))
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
  let sampleSize = 100
  let seed = 100
  let gen = mkStdGen seed
  let txApplyTimesReduced = sampleElements gen sampleSize txApplyTimes
  let txReapplyTimesReduced = sampleElements gen sampleSize txReapplyTimes

  -- let applyTxs = DeltaQ.uniform 0 0.5
  -- let reapplyTxs = DeltaQ.uniform 0 0.4
  let applyTxs = empiricalDQ txApplyTimesReduced
  let reapplyTxs = empiricalDQ txReapplyTimesReduced

  printf "Complexity applyTxs: %d\n" (complexity applyTxs)
  printf "Complexity reapplyTxs: %d\n" (complexity reapplyTxs)

  _ <- forkIO $ maybe (print @String "Nothing") (printf "Estimate for lVote: %d\n") (lVoteEstimated applyTxs reapplyTxs)
  _ <- forkIO $ maybe (print @String "Nothing") (printf "Estimate for lDiff: %d\n") (lDiffEstimated applyTxs reapplyTxs)

  let generatePlots = False
  let configs =
        [ Config{name = "C113", lHdr = 1, lVote = 1, lDiff = 3, τ = 3 % 4, committeeSizeEstimated = 600, λ = 1 % 20, numberSPOs = 2500, ..}
        , Config{name = "C124", lHdr = 1, lVote = 2, lDiff = 4, τ = 3 % 4, committeeSizeEstimated = 600, λ = 1 % 20, numberSPOs = 2500, ..}
        , Config{name = "C135", lHdr = 1, lVote = 3, lDiff = 5, τ = 3 % 4, committeeSizeEstimated = 600, λ = 1 % 20, numberSPOs = 2500, ..}
        , Config{name = "C145", lHdr = 1, lVote = 4, lDiff = 5, τ = 3 % 4, committeeSizeEstimated = 600, λ = 1 % 20, numberSPOs = 2500, ..}
        , Config{name = "C147", lHdr = 1, lVote = 4, lDiff = 7, τ = 3 % 4, committeeSizeEstimated = 600, λ = 1 % 20, numberSPOs = 2500, ..}
        , Config{name = "C155", lHdr = 1, lVote = 5, lDiff = 5, τ = 3 % 4, committeeSizeEstimated = 600, λ = 1 % 20, numberSPOs = 2500, ..}
        , Config{name = "C165", lHdr = 1, lVote = 6, lDiff = 5, τ = 3 % 4, committeeSizeEstimated = 600, λ = 1 % 20, numberSPOs = 2500, ..}
        , Config{name = "C999", lHdr = 9, lVote = 9, lDiff = 9, τ = 3 % 4, committeeSizeEstimated = 600, λ = 1 % 20, numberSPOs = 2500, ..}
        ]
  mapConcurrently (mainWith generatePlots) configs >>= printResults

mainWith :: Bool -> Config -> IO Result
mainWith True config = plots config >> mainWith False config
mainWith False config = return (stats config)

data Result
  = -- | Config name
    Result
    { res_config :: !String
    -- ^ Probability that a header arrives on time
    , lHdr :: !Integer
    -- ^ \(L_\text{hdr}\) parameter
    , lVote :: !Integer
    -- ^ \(L_\text{vote}\) parameter
    , lDiff :: !Integer
    -- ^ \(L_\text{diff}\) parameter
    , res_pHeaderOnTime :: !Double
    -- ^ Probability that EB validation is completed before voting is over
    , res_pValidating :: !Double
    -- ^ Probability of Quorum
    , res_pQuorum :: !Double
    -- ^ Probability that the next Praos block has already been produced after the waiting period
    , res_pInterruptedByNewBlock :: !Double
    -- ^ Probability that an EB is certified
    , res_pCertified :: !Double
    -- ^ Expected time for certified EB
    , res_eCertified :: !Double
    }
  deriving (Show, Eq, Generic)

instance FromNamedRecord Result
instance ToNamedRecord Result
instance DefaultOrdered Result

plots :: Config -> IO ()
plots Config{..} = do
  _ <-
    renderableToFile def{_fo_format = SVG} (name <> "-tx-apply.svg") $
      toRenderable $
        plotCDFWithQuantiles "Tx Apply" [0.75, 0.95, 0.99] applyTxs
  _ <-
    renderableToFile def{_fo_format = SVG} (name <> "-block-diffustion.svg") $
      toRenderable $
        plotCDFs "Block diffusion" $
          zip (map show blockSizes) (map blendedDelay blockSizes)
  _ <-
    renderableToFile def{_fo_format = SVG} (name <> "-validateEB.svg") $
      toRenderable $
        plotCDFWithQuantiles "EB diffusion" [0.75, 0.95, 0.99] (validateEB applyTxs reapplyTxs)
  _ <-
    renderableToFile def{_fo_format = SVG} (name <> "-quorumProb.svg") $
      toRenderable $
        let xs = [0.50, 0.51 .. 1]
            s = fromInteger committeeSizeEstimated
            n = fromInteger numberSPOs
            t = fromRational τ
            vs = [(x, quorumProbability n x s t) | x <- xs]
         in do
              layout_title .= "Quorum distribution"
              plot (line "pQuorum" [vs])
  pure ()

stats :: Config -> Result
stats config@Config{..} =
  let res_config = name
      res_pHeaderOnTime = fromRational (pHeaderOnTime lHdr)
      res_pValidating = fromRational (pValidating applyTxs reapplyTxs (lHdr, lVote))
      res_pQuorum = pQuorum config
      res_pInterruptedByNewBlock = pInterruptedByNewBlock config
      res_pCertified = pCertified config
      res_eCertified = 1 / (eCertified config)
   in Result{..}

printResults :: [Result] -> IO ()
printResults = BL.writeFile "output.csv" . encodeDefaultOrderedByName
