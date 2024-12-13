module Test.Topology where

import Data.Graph.Inductive (Gr)
import Data.Graph.Inductive.Arbitrary (NoLoops (..), NoMultipleEdges (..), SimpleGraph)
import P2P (Latency)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Topology (grToSimpleTopology, simpleTopologyToGr)

tests :: TestTree
tests =
  testGroup "Topology" $
    [ testProperty "prop_GrToSimpleTopologyToGrIsIso" prop_GrToSimpleTopologyToGrIsIso
    ]

prop_GrToSimpleTopologyToGrIsIso :: SimpleGraph Gr () Latency -> Bool
prop_GrToSimpleTopologyToGrIsIso (NL (NME gr)) =
  let gr' = simpleTopologyToGr . grToSimpleTopology $ gr
   in gr == gr'
