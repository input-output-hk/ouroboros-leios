module VizNameSpec where

import Test.Hspec

import Data.Proxy (Proxy (..))
import Test.QuickCheck.Classes (lawsCheck, showReadLaws)
import VizName (VizName)

spec :: Spec
spec =
  it "read is inverse to show" $ lawsCheck $ showReadLaws (Proxy :: Proxy VizName)
