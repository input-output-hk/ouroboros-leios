module Main where

import qualified Test.Config
import qualified Test.ShortToFull
import Test.Tasty (defaultMain, testGroup)
import qualified Test.Topology

main :: IO ()
main =
  defaultMain . testGroup "ouroboros-leios-sim" $
    [ Test.Topology.tests
    , Test.Config.tests
    , Test.ShortToFull.tests
    ]
