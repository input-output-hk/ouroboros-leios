{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Analysis.Leios
import Control.Concurrent.Async (mapConcurrently)
import qualified Data.ByteString.Lazy as BL
import Data.Csv (DefaultOrdered (..), FromNamedRecord (..), ToNamedRecord (..), encodeDefaultOrderedByName)
import Data.Ratio ((%))
import DeltaQ.Leios (pHeaderOnTime, pValidating)
import GHC.Generics

data Result = Result
  { res_config :: !String
  , lHdr :: !Integer
  , lVote :: !Integer
  , lDiff :: !Integer
  , res_pHeaderOnTime :: !Double
  , res_pValidating :: !Double
  , res_pQuorum :: !Double
  , res_pInterruptedByNewBlock :: !Double
  , res_pCertified :: !Double
  , res_eCertified :: !Double
  }
  deriving (Show, Eq, Generic)

instance FromNamedRecord Result
instance ToNamedRecord Result
instance DefaultOrdered Result

stats :: Config -> Result
stats config@Config{..} =
  let res_config = name
      res_pHeaderOnTime = fromRational $ pHeaderOnTime lHdr
      res_pValidating = fromRational $ pValidating (lHdr, lVote)
      res_pQuorum = pQuorum config
      res_pInterruptedByNewBlock = pInterruptedByNewBlock config
      res_pCertified = pCertified config
      res_eCertified = eCertified config
   in Result{..}

writeResults :: [Result] -> IO ()
writeResults = BL.writeFile "output.csv" . encodeDefaultOrderedByName

main :: IO ()
main = do
  let f = 1 % 20
  let τ = 3 % 4
  let committeeSizeEstimated = 600
  let numberSPOs = 2500
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
  mapConcurrently (return . stats) configs >>= writeResults
