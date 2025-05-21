module Main where

import Spec.Generated (generated)
import Spec.Golden (golden)
import Test.Hspec (hspec)

main :: IO ()
main =
  hspec $ do
    generated
    golden
