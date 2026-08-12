-- | Main entry point.
module Main where

-- import Spec.Generated (generated)
import Spec.ChainEvents (chainEvents)
import Spec.ChainVerifier (chainVerifier)
import Spec.Golden (golden)
import Test.Hspec (describe, hspec)

-- | Test the trace verifier.
main :: IO ()
main =
  hspec $ do
    -- TODO: port test cases for Short- to Linear Leios
    -- describe "Generated traces" generated
    describe "Golden traces" golden
    describe "node.log chain events" chainEvents
    describe "chain verifier" chainVerifier
