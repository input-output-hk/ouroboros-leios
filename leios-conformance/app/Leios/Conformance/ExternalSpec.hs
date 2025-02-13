module Leios.Conformance.ExternalSpec where

import Leios.Conformance.Test.External (prop_node)
import System.IO (Handle)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Blind (Blind), arbitrary, forAll, scale)

-- | Test an external implementation against the Agda executable specification.
spec :: Handle -> Handle -> Spec
spec hReader hWriter =
  describe "External node"
    . prop "Implementation respects Leios protocol"
    $ forAll
      arbitrary
      (prop_node hReader hWriter . Blind)
