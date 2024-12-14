{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}

module Test.Topology where

import Data.Graph.Inductive (Gr)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.Arbitrary (NoLoops (..), NoMultipleEdges (..), SimpleGraph)
import qualified Data.Text as T
import P2P (Latency)
import Paths_ouroboros_leios_sim (getDataFileName)
import System.Directory (doesFileExist)
import Test.QuickCheck (Arbitrary (..), Gen, NonNegative (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertEqual, testCase)
import Test.Tasty.QuickCheck (Small (..), testProperty)
import Topology (ClusterName (..), NodeName (..), benchTopologyToSimpleTopology, forgetUnusedFieldsInBenchTopology, grToSimpleTopology, readBenchTopology, readLatenciesSqlite3Gz, simpleTopologyToBenchTopology, simpleTopologyToGr, sortBenchTopology, withNodeNames)

tests :: TestTree
tests =
  testGroup "Topology" $
    [ testCase "test_BenchTopologyToSimpleTopologyToBenchTopologyIsIso" test_BenchTopologyToSimpleTopologyToBenchTopologyIsIso
    , testProperty "prop_GrToSimpleTopologyToGrIsIso" prop_GrToSimpleTopologyToGrIsIso
    ]

test_BenchTopologyToSimpleTopologyToBenchTopologyIsIso :: Assertion
test_BenchTopologyToSimpleTopologyToBenchTopologyIsIso = do
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
