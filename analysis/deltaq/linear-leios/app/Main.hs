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
import Control.Monad
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
  let sampleSize = 2 -- FIXME: larger value
  let seed = 100
  let gen = mkStdGen seed
  let txApplyTimesReduced = sampleElements gen sampleSize txApplyTimes
  let txReapplyTimesReduced = sampleElements gen sampleSize txReapplyTimes

  -- let applyTx = DeltaQ.uniform 0 3.3 -- 0 0.5
  -- let reapplyTx = DeltaQ.uniform 0 2.1 -- 0 0.4
  let applyTx = empiricalDQ txApplyTimesReduced
  let reapplyTx = empiricalDQ txReapplyTimesReduced

  -- (maybe (print @String "Nothing") (printf "Estimate for lVote: %d\n") (lVoteEstimated applyTx reapplyTx))
  -- (maybe (print @String "Nothing") (printf "Estimate for lDiff: %d\n") (lDiffEstimated applyTx reapplyTx))

  _ <- forkIO $ printf "Complexity applyTx: %d\n" (complexity applyTx)
  _ <- forkIO $ printf "Complexity reapplyTx: %d\n" (complexity reapplyTx)

  let committeeSizeEstimated = 600
  let numberSPOs = 2500
  let λ = 1 % 20
  let τ = 3 % 4

  let generatePlots = True
  let configs =
        [ Config{name = "C113", lHdr = 1, lVote = 1, lDiff = 3, ..}
        , Config{name = "C124", lHdr = 1, lVote = 2, lDiff = 4, ..}
        , Config{name = "C137", lHdr = 1, lVote = 3, lDiff = 7, ..}
        , Config{name = "C145", lHdr = 1, lVote = 4, lDiff = 5, ..}
        , Config{name = "C146", lHdr = 1, lVote = 4, lDiff = 6, ..}
        , Config{name = "C147", lHdr = 1, lVote = 4, lDiff = 7, ..}
        , Config{name = "C155", lHdr = 1, lVote = 5, lDiff = 5, ..}
        , Config{name = "C165", lHdr = 1, lVote = 6, lDiff = 5, ..}
        , Config{name = "C999", lHdr = 9, lVote = 9, lDiff = 9, ..}
        ]

  mapConcurrently_ (mainWith generatePlots >=> print) configs

-- mapConcurrently (mainWith generatePlots) configs >>= printResults

mainWith :: Bool -> Config -> IO Result
mainWith True config = snd <$> concurrently (plots config) (mainWith False config)
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
        plotCDFWithQuantiles "Tx Apply" [0.75, 0.95, 0.99] applyTx
  _ <-
    renderableToFile def{_fo_format = SVG} (name <> "-tx-reapply.svg") $
      toRenderable $
        plotCDFWithQuantiles "Tx Reapply" [0.75, 0.95, 0.99] reapplyTx
  _ <-
    renderableToFile def{_fo_format = SVG} (name <> "-block-diffustion.svg") $
      toRenderable $
        plotCDFs "Block diffusion" $
          zip (map show blockSizes) (map blendedDelay blockSizes)
  _ <-
    renderableToFile def{_fo_format = SVG} (name <> "-validateEB.svg") $
      toRenderable $
        plotCDFWithQuantiles "EB diffusion" [0.75, 0.95, 0.99] (validateEB applyTx reapplyTx)
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
      res_pValidating = fromRational (pValidating applyTx reapplyTx (lHdr, lVote))
      res_pQuorum = pQuorum config
      res_pInterruptedByNewBlock = pInterruptedByNewBlock config
      res_pCertified = pCertified config
      res_eCertified = 1 / (eCertified config)
   in Result{..}

printResults :: [Result] -> IO ()
printResults = BL.writeFile "output.csv" . encodeDefaultOrderedByName
