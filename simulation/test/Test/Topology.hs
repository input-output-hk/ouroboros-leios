{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}

module Test.Topology where

import Data.Graph.Inductive (Gr)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.Arbitrary (NoLoops (..), NoMultipleEdges (..), SimpleGraph)
import qualified Data.Text as T
import P2P (Latency)
import Paths_ouroboros_leios_sim (getDataFileName)
import SimTypes (WorldDimensions)
import System.Directory (doesFileExist)
import Test.QuickCheck (Arbitrary (..), Gen, NonNegative (..), Property, ioProperty)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertEqual, testCase)
import Test.Tasty.QuickCheck (Small (..), testProperty)
import Topology (ClusterName (..), NodeName (..), addNodeNames, augmentWithPositionInformation, benchTopologyToSimpleTopology, defaultParams, forgetPositionInformation, forgetUnusedFieldsInBenchTopology, grToSimpleTopology, readBenchTopology, readLatenciesSqlite3Gz, simpleTopologyToBenchTopology, simpleTopologyToGr, sortBenchTopology)

tests :: TestTree
tests =
  testGroup "Topology" $
    [ testCase "test_benchTopologyToSimpleTopologyPreservesTopology" test_benchTopologyToSimpleTopologyPreservesTopology
    , testProperty "prop_grToSimpleTopologyPreservesTopology" prop_grToSimpleTopologyPreservesTopology
    , testProperty "prop_augmentWithPositionInformationPreservesTopology" prop_augmentWithPositionInformationPreservesTopology
    , testProperty "prop_augmentWithPositionInformationPreservesTopology" prop_augmentWithPositionInformationPreservesTopology
    ]

--------------------------------------------------------------------------------
-- Conversion between BenchTopology and SimpleTopology
--------------------------------------------------------------------------------

-- | Test that the conversion between BenchTopology and SimpleTopology preserves the topology.
test_benchTopologyToSimpleTopologyPreservesTopology :: Assertion
test_benchTopologyToSimpleTopologyPreservesTopology = do
  -- Find test/data/BenchTopology/topology-dense-52.json
  benchTopologyFile <- getDataFileName "test/data/BenchTopology/topology-dense-52.json"
  doesBenchTopologyFileExist <- doesFileExist benchTopologyFile
  assertBool "File data/BenchTopology/topology-dense-52.json does not exist" doesBenchTopologyFileExist
  -- Find test/data/BenchTopology/latency.sqlite3.gz
  latenciesSqlite3GzFile <- getDataFileName "test/data/BenchTopology/latency.sqlite3.gz"
  doesLatenciesFileExit <- doesFileExist latenciesSqlite3GzFile
  assertBool "File data/BenchTopology/latency.sqlite3.gz does not exist" doesLatenciesFileExit
  -- Read bench topology
  benchTopology1 <- sortBenchTopology . forgetUnusedFieldsInBenchTopology <$> readBenchTopology benchTopologyFile
  -- Read latencies
  latencies <- readLatenciesSqlite3Gz benchTopology1 latenciesSqlite3GzFile
  -- Test conversion to/from simple topology
  let simpleTopology = benchTopologyToSimpleTopology latencies benchTopology1
  let benchTopology2 = sortBenchTopology . simpleTopologyToBenchTopology $ simpleTopology
  assertEqual "Conversion to/from SimpleTopology does not preserve topology" benchTopology1 benchTopology2

--------------------------------------------------------------------------------
-- Conversion between SimpleTopology and FGL Graph
--------------------------------------------------------------------------------

-- | Test that the conversion between SimpleTopology and FGL Graphs preserves the topology.
prop_grToSimpleTopologyPreservesTopology :: SimpleGraph Gr (Maybe ClusterName) Latency -> Bool
prop_grToSimpleTopologyPreservesTopology gr = do
  let gr1 = addNodeNames . nmeGraph . looplessGraph $ gr
  let gr2 = simpleTopologyToGr . grToSimpleTopology $ gr1
  gr1 == gr2

--------------------------------------------------------------------------------
-- Augmentation with Position Information
--------------------------------------------------------------------------------

prop_augmentWithPositionInformationPreservesTopology ::
  WorldDimensions ->
  SimpleGraph Gr (Maybe ClusterName) Latency ->
  Property
prop_augmentWithPositionInformationPreservesTopology wordDimensions gr = ioProperty $ do
  let gr1 = addNodeNames . nmeGraph . looplessGraph $ gr
  gr2 <- augmentWithPositionInformation defaultParams wordDimensions gr1
  let gr3 = forgetPositionInformation gr2
  pure $ gr1 == gr3

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance Arbitrary ClusterName where
  arbitrary :: Gen ClusterName
  arbitrary = ClusterName . T.pack . ("cluster-" <>) . show @Int . getSmall . getNonNegative <$> arbitrary
