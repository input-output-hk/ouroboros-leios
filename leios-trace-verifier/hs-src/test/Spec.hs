-- | Main entry point.
module Main where

-- import Spec.Generated (generated)
import Spec.Golden (golden)
import Test.Hspec (describe, hspec)

-- | Test the trace verifier.
main :: IO ()
main =
  hspec $ do
    -- TODO: port test cases for Short- to Linear Leios
    -- describe "Generated traces" generated
    describe "Golden traces" golden
