module Main where

import Spec.Generated (generated)
import Spec.Golden (golden)
import Test.Hspec (describe, hspec)

main :: IO ()
main =
  hspec $ do
    describe "Generated trace" generated
    describe "Golden traces" golden
