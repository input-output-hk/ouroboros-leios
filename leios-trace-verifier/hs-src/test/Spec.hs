module Main where

import Spec.Golden (golden)
import Test.Hspec (hspec)

main :: IO ()
main =
  hspec
    golden
