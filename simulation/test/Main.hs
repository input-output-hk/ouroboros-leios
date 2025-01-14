module Main where

import Test.Tasty (defaultMain, testGroup)
import qualified Test.Topology

main :: IO ()
main =
  defaultMain . testGroup "ouroboros-leios-sim" $
    [ Test.Topology.tests
    ]
