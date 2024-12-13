{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}

module Test.Topology where

import Data.Graph.Inductive (Gr)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.Arbitrary (NoLoops (..), NoMultipleEdges (..), SimpleGraph)
import qualified Data.Text as T
import P2P (Latency)
import Test.QuickCheck (Arbitrary (..), Gen, NonNegative (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (Small (..), testProperty)
import Topology (ClusterName (..), NodeName (..), grToSimpleTopology, simpleTopologyToGr, withNodeNames)

tests :: TestTree
tests =
  testGroup "Topology" $
    [ testProperty "prop_GrToSimpleTopologyToGrIsIso" prop_GrToSimpleTopologyToGrIsIso
    ]

prop_GrToSimpleTopologyToGrIsIso :: SimpleGraph Gr (Maybe ClusterName) Latency -> Bool
prop_GrToSimpleTopologyToGrIsIso gr = do
  let gr1 = withNodeNames . nmeGraph . looplessGraph $ gr
  let gr2 = simpleTopologyToGr . grToSimpleTopology $ gr1
  gr1 == gr2

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance Arbitrary ClusterName where
  arbitrary :: Gen ClusterName
  arbitrary = ClusterName . T.pack . ("cluster-" <>) . show @Int . getSmall . getNonNegative <$> arbitrary