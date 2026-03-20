{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Concurrent.Async (concurrently_)
import DeltaQ.Leios (lDiffEstimated, lVoteEstimated)
import Text.Printf (printf)

main :: IO ()
main =
  concurrently_
    (maybe (print @String "Nothing") (printf "Estimate for lVote: %d\n") lVoteEstimated)
    (maybe (print @String "Nothing") (printf "Estimate for lDiff: %d\n") lDiffEstimated)
