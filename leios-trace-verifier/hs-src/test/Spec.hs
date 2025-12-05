-- | Main entry point.
module Main where

import Spec.Generated (generated)
import Spec.Golden (golden)
import Test.Hspec (describe, hspec)

-- | Test the trace verifier.
main :: IO ()
main =
  hspec $ do
    describe "Generated traces" generated
    describe "Golden traces" golden
