{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Test.Topology where

import Data.Bifunctor (Bifunctor (..))
import Data.Graph.Inductive (Gr)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive.Arbitrary (NoLoops (..), NoMultipleEdges (..), SimpleGraph)
import qualified Data.Text as T
import P2P (Latency, P2PTopography (..), P2PTopographyCharacteristics (..), genArbitraryP2PTopography)
import Paths_ouroboros_leios_sim (getDataFileName)
import SimTypes (World (..), WorldDimensions, WorldShape (..))
import System.Directory (doesFileExist)
import Test.QuickCheck (Arbitrary (..), Gen, NonNegative (..), Positive (..), Property, ioProperty)
import Test.QuickCheck.Arbitrary (arbitraryBoundedEnum)
import Test.QuickCheck.Gen (Gen (..))
import Test.QuickCheck.Random (QCGen (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertEqual, testCase)
import Test.Tasty.QuickCheck (Small (..), testProperty)
import Topology (ClusterName (..), LatencyMs (..), NodeName (..), addNodeNames, augmentWithPosition, benchTopologyToSimpleTopology, defaultParams, forgetPaths, forgetPoints, forgetPosition, forgetSimpleNodeInfo, forgetUnusedFieldsInBenchTopology, grToP2PTopography, grToSimpleTopology, p2pTopologyToGr, readBenchTopology, readLatenciesSqlite3Gz, readSimpleTopologyFromBenchTopologyAndLatency, simpleTopologyToBenchTopology, simpleTopologyToGr, sortBenchTopology)

tests :: TestTree
tests =
  testGroup
    "Topology"
    [ testCase "test_benchTopologyToSimpleTopologyPreservesTopology" test_benchTopologyToSimpleTopologyPreservesTopology
    , testCase "test_benchTopologyIsConnected" test_benchTopologyIsConnected
    , testProperty "prop_grToSimpleTopologyPreservesTopology" prop_grToSimpleTopologyPreservesTopology
    , testProperty "prop_augmentWithPositionPreservesTopology" prop_augmentWithPositionPreservesTopology
    , testProperty "prop_grToP2PTopographyPreservesTopology" prop_grToP2PTopographyPreservesTopology
    -- NOTE: Disabled, as `genArbitraryP2PTopography` appears to loop for certain inputs.
    -- , testProperty "prop_p2pTopographyToGrPreservesTopology" prop_p2pTopographyToGrPreservesTopology
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

test_benchTopologyIsConnected :: Assertion
test_benchTopologyIsConnected = do
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
  let gr = simpleTopologyToGr simpleTopology
  assertBool "BenchTopology is not connected" (G.isConnected gr)

--------------------------------------------------------------------------------
-- Conversion between SimpleTopology and FGL Graph
--------------------------------------------------------------------------------

-- | Test that the conversion between SimpleTopology and FGL Graphs preserves the topology.
prop_grToSimpleTopologyPreservesTopology :: SimpleGraph Gr (Maybe ClusterName) LatencyMs -> Bool
prop_grToSimpleTopologyPreservesTopology gr = do
  let gr1 = addNodeNames . nmeGraph . looplessGraph $ gr
  let gr2 = simpleTopologyToGr . grToSimpleTopology $ gr1
  gr1 == gr2

--------------------------------------------------------------------------------
-- Augmentation with Position Information
--------------------------------------------------------------------------------

prop_augmentWithPositionPreservesTopology ::
  WorldDimensions ->
  SimpleGraph Gr (Maybe ClusterName) LatencyMs ->
  Property
prop_augmentWithPositionPreservesTopology wordDimensions gr = ioProperty $ do
  let gr1 = addNodeNames . nmeGraph . looplessGraph $ gr
  gr2 <- augmentWithPosition defaultParams wordDimensions gr1
  let gr3 = forgetPosition gr2
  pure $ gr1 == gr3

--------------------------------------------------------------------------------
-- Conversion between FGL Graph and P2P Topography
--------------------------------------------------------------------------------

-- | Test that the conversion between SimpleTopology and FGL Graphs preserves the topology.
prop_grToP2PTopographyPreservesTopology ::
  World ->
  SimpleGraph Gr (Maybe ClusterName) Latency ->
  Property
prop_grToP2PTopographyPreservesTopology world@World{..} gr = ioProperty $ do
  let gr1 = addNodeNames . nmeGraph . looplessGraph $ gr
  gr2 <- forgetSimpleNodeInfo . forgetPaths <$> augmentWithPosition defaultParams worldDimensions gr1
  let gr3 = grToP2PTopography world gr2
  let gr4 = p2pTopologyToGr gr3
  let forgetPoints = G.nmap (const ())
  pure $ forgetPoints gr2 == forgetPoints gr4

-- | Test that the conversion between SimpleTopology and FGL Graphs preserves the topology.
prop_p2pTopographyToGrPreservesTopology ::
  P2PTopography ->
  Bool
prop_p2pTopographyToGrPreservesTopology gr1@P2PTopography{..} = do
  let gr2 = p2pTopologyToGr gr1
  let gr3 = grToP2PTopography p2pWorld gr2
  gr1 == gr3

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance Arbitrary ClusterName where
  arbitrary :: Gen ClusterName
  arbitrary = ClusterName . T.pack . ("cluster-" <>) . show @Int . getSmall . getNonNegative <$> arbitrary

instance Arbitrary LatencyMs where
  arbitrary :: Gen LatencyMs
  arbitrary = LatencyMs . getPositive <$> arbitrary

instance Arbitrary World where
  arbitrary :: Gen World
  arbitrary = do
    worldDimensions <- bimap getPositive getPositive <$> arbitrary
    worldShape <- arbitrary
    pure $ World{..}

instance Arbitrary WorldShape where
  arbitrary :: Gen WorldShape
  arbitrary = arbitraryBoundedEnum

instance Arbitrary P2PTopographyCharacteristics where
  arbitrary :: Gen P2PTopographyCharacteristics
  arbitrary = do
    p2pWorld <- arbitrary
    p2pNumNodes <- getPositive <$> arbitrary
    p2pNodeLinksClose <- getSmall . getPositive <$> arbitrary
    p2pNodeLinksRandom <- getSmall . getPositive <$> arbitrary
    pure P2PTopographyCharacteristics{..}

instance Arbitrary P2PTopography where
  arbitrary :: Gen P2PTopography
  arbitrary = arbitraryP2PTopography =<< arbitrary
   where
    -- TODO: This appears to loop for some inputs.
    arbitraryP2PTopography :: P2PTopographyCharacteristics -> Gen P2PTopography
    arbitraryP2PTopography p2pTopographyCharacteristics = MkGen $ \gen size ->
      genArbitraryP2PTopography p2pTopographyCharacteristics gen
