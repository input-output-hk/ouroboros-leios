module Leios.ModelSpec where

import Leios.Model (Slice (..), slice)
import Test.Hspec (Spec, describe, it, shouldBe)

spec :: Spec
spec =
  describe "slice" $ do
    it "returns [5, 10) given len = 5, start = 18, and #slice = 2" $
      slice 5 18 2 `shouldBe` Slice 5 10
