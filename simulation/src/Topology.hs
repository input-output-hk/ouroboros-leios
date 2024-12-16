{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Topology where

import Codec.Compression.GZip as GZip (decompress)
import Control.Arrow (Arrow ((&&&)), second)
import Control.Exception (assert)
import Control.Monad (forM_, void, (<=<))
import Data.Aeson (encode)
import Data.Aeson.Decoding (throwDecode)
import Data.Aeson.Types (FromJSON (..), FromJSONKey, Options (..), ToJSON (..), ToJSONKey, defaultOptions, genericParseJSON, genericToEncoding)
import qualified Data.ByteString.Lazy as BSL
import Data.Coerce (coerce)
import Data.Function (on)
import qualified Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.GraphViz (GraphvizCanvas (..), GraphvizOutput (..), GraphvizParams (..), X11Color (..))
import qualified Data.GraphViz as GV
import qualified Data.GraphViz.Attributes as GV
import Data.GraphViz.Attributes.Colors (Color (X11Color))
import Data.GraphViz.Attributes.Complete (GraphSize (..))
import qualified Data.GraphViz.Attributes.Complete as GV
import qualified Data.GraphViz.Commands as GV
import qualified Data.GraphViz.Types as GVT (PrintDot)
import qualified Data.GraphViz.Types.Generalised as GVTG
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.List (sort, sortBy)
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (maybeToList)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Lazy (LazyText)
import qualified Data.Text.Lazy as TL
import Data.Vector (Vector)
import qualified Data.Vector as V
import Database.SQLite.Simple (NamedParam (..))
import qualified Database.SQLite.Simple as SQLlite
import qualified Database.SQLite.Simple.ToField as SQLite (ToField)
import GHC.Generics (C, Generic)
import GHC.Records (HasField (..))
import P2P (Latency, P2PTopography (..))
import SimTypes (NodeId (..), Path (..), Point (..), WorldDimensions, WorldShape (..))
import System.FilePath (dropExtension, takeDirectory, takeExtension, takeExtensions, takeFileName)
import System.IO (hClose)
import System.IO.Temp (withTempFile)
import Text.Printf (PrintfArg, printf)

--------------------------------------------------------------------------------
-- Bench Topology
--
-- As provided in 'data/BenchTopology/topology-dense-52.json'.
--------------------------------------------------------------------------------

newtype NodeName = NodeName {unNodeName :: Text}
  deriving stock (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON, FromJSONKey, ToJSONKey)
  deriving newtype (GVT.PrintDot)
  deriving newtype (SQLite.ToField)
  deriving newtype (PrintfArg)

newtype OrgName = OrgName {unOrgName :: Text}
  deriving stock (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

newtype RegionName = RegionName {unRegionName :: Text}
  deriving stock (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

data BenchTopologyNode
  = BenchTopologyNode
  { name :: !NodeName
  , nodeId :: !NodeId
  , org :: !(Maybe OrgName)
  , pools :: !(Maybe Int)
  , producers :: !(Vector NodeName)
  , region :: !(Maybe RegionName)
  , stakePool :: !(Maybe Bool)
  }
  deriving (Eq, Show, Generic)

benchTopologyOptions :: Options
benchTopologyOptions = defaultOptions{unwrapUnaryRecords = False}

instance ToJSON BenchTopologyNode where
  toEncoding = genericToEncoding benchTopologyOptions

instance FromJSON BenchTopologyNode

newtype BenchTopology = BenchTopology
  { coreNodes :: Vector BenchTopologyNode
  }
  deriving (Eq, Show, Generic)

instance ToJSON BenchTopology where
  toEncoding = genericToEncoding benchTopologyOptions

instance FromJSON BenchTopology where
  parseJSON = genericParseJSON benchTopologyOptions

readBenchTopology :: FilePath -> IO BenchTopology
readBenchTopology = throwDecode <=< BSL.readFile

-- | Helper for testing. Sorts the list of producers and the list of core nodes by node name.
sortBenchTopology :: BenchTopology -> BenchTopology
sortBenchTopology benchTopology =
  BenchTopology
    { coreNodes = V.fromList . sortBy (compare `on` (.name)) . V.toList . fmap sortBenchTopologyNode $ benchTopology.coreNodes
    }
 where
  sortBenchTopologyNode :: BenchTopologyNode -> BenchTopologyNode
  sortBenchTopologyNode BenchTopologyNode{..} =
    BenchTopologyNode
      { producers = V.fromList . sort . V.toList $ producers
      , ..
      }

-- | Helper for testing. Forgets fields that are not represented by `SimpleTopology`.
forgetUnusedFieldsInBenchTopology :: BenchTopology -> BenchTopology
forgetUnusedFieldsInBenchTopology benchTopology =
  BenchTopology
    { coreNodes = forgetUnusedFieldsInBenchTopologyNode <$> benchTopology.coreNodes
    }
 where
  forgetUnusedFieldsInBenchTopologyNode :: BenchTopologyNode -> BenchTopologyNode
  forgetUnusedFieldsInBenchTopologyNode BenchTopologyNode{..} =
    BenchTopologyNode
      { org = Nothing
      , pools = Nothing
      , stakePool = Nothing
      , ..
      }

--------------------------------------------------------------------------------
-- Latencies
--
-- As provided in 'data/BenchTopology/latency.sqlite3.gz'.
--------------------------------------------------------------------------------

type Latencies = Map NodeName (Map NodeName Latency)

readLatencies :: BenchTopology -> FilePath -> IO Latencies
readLatencies topology latencyFile =
  case takeExtensions latencyFile of
    ".sqlite3" ->
      readLatenciesSqlite3 topology latencyFile
    ".sqlite3.gz" ->
      readLatenciesSqlite3Gz topology latencyFile
    _otherwise ->
      error $ printf "unknown latency file format %s" (takeFileName latencyFile)

readLatenciesSqlite3Gz :: BenchTopology -> FilePath -> IO Latencies
readLatenciesSqlite3Gz topology latencySqliteGzFile =
  assert (takeExtension latencySqliteGzFile == ".gz") $ do
    let latencySqliteDirectory = takeDirectory latencySqliteGzFile
    let latencySqliteFileName = takeFileName (dropExtension latencySqliteGzFile)
    withTempFile latencySqliteDirectory latencySqliteFileName $ \latencySqliteFile latencySqliteHandle -> do
      latencySqliteGzContent <- BSL.readFile latencySqliteGzFile
      let latencySqliteContent = GZip.decompress latencySqliteGzContent
      BSL.hPut latencySqliteHandle latencySqliteContent
      hClose latencySqliteHandle
      readLatencies topology latencySqliteFile

readLatenciesSqlite3 :: BenchTopology -> FilePath -> IO Latencies
readLatenciesSqlite3 topology latencySqliteFile = do
  let queryAvgTime =
        "select avg(time) from ping \
        \where source = :consumer and dest = :producer \
        \or    source = :producer and dest = :consumer"
  latenciesRef <- newIORef mempty
  conn <- SQLlite.open latencySqliteFile
  forM_ topology.coreNodes $ \consumer -> do
    atomicModifyIORef' latenciesRef $ \latencies ->
      (M.insert consumer.name M.empty latencies, ())
    forM_ consumer.producers $ \producerName -> do
      SQLlite.queryNamed conn queryAvgTime [":consumer" := consumer.name, ":producer" := producerName] >>= \case
        [] -> error $ printf "missing latency for connection between %s and %s" consumer.name producerName
        [[latency :: Double]] ->
          atomicModifyIORef' latenciesRef $ \latencies ->
            (M.adjust (M.insert producerName latency) consumer.name latencies, ())
        _otherwise -> error "impossible: SQL query for average returned multiple rows"
  readIORef latenciesRef

--------------------------------------------------------------------------------
-- Simple Topology
--
-- Combines the graph structure from Bench Topology with the average connection
-- latency from Latencies.
--------------------------------------------------------------------------------

newtype ClusterName = ClusterName {unClusterName :: Text}
  deriving stock (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

data SimpleNode
  = SimpleNode
  { name :: !NodeName
  , nodeId :: !NodeId
  , producers :: !(Map NodeName Latency)
  , clusterName :: !(Maybe ClusterName)
  }
  deriving (Eq, Show, Generic)

simpleNodeOptions :: Options
simpleNodeOptions = defaultOptions{unwrapUnaryRecords = False}

instance ToJSON SimpleNode where
  toEncoding = genericToEncoding simpleNodeOptions

instance FromJSON SimpleNode where
  parseJSON = genericParseJSON simpleNodeOptions

newtype SimpleTopology
  = SimpleTopology
  { nodes :: Vector SimpleNode
  }
  deriving (Eq, Show, Generic)

instance ToJSON SimpleTopology where
  toEncoding = genericToEncoding simpleNodeOptions

instance FromJSON SimpleTopology where
  parseJSON = genericParseJSON simpleNodeOptions

-- | Convert a 'BenchTopology' to a 'SimpleTopology' using the 'Latencies' read from the latency database.
benchTopologyToSimpleTopology :: Latencies -> BenchTopology -> SimpleTopology
benchTopologyToSimpleTopology latencies benchTopology =
  SimpleTopology{nodes = benchTopologyNodeToSimpleNode <$> benchTopology.coreNodes}
 where
  benchTopologyNodeToSimpleNode :: BenchTopologyNode -> SimpleNode
  benchTopologyNodeToSimpleNode benchTopologyNode =
    SimpleNode
      { name = benchTopologyNode.name
      , nodeId = benchTopologyNode.nodeId
      , producers = latencies M.! benchTopologyNode.name
      , clusterName = regionNameToClusterName <$> benchTopologyNode.region
      }

-- | Helper for testing. Partial inverse of 'benchTopologyToSimpleTopology'.
simpleTopologyToBenchTopology :: SimpleTopology -> BenchTopology
simpleTopologyToBenchTopology simpleTopology =
  BenchTopology
    { coreNodes = simpleNodeToBenchTopologyNode <$> simpleTopology.nodes
    }
 where
  simpleNodeToBenchTopologyNode :: SimpleNode -> BenchTopologyNode
  simpleNodeToBenchTopologyNode simpleNode =
    BenchTopologyNode
      { name = simpleNode.name
      , nodeId = simpleNode.nodeId
      , org = Nothing
      , pools = Nothing
      , producers = V.fromList . M.keys $ simpleNode.producers
      , region = clusterNameToRegionName <$> simpleNode.clusterName
      , stakePool = Nothing
      }

-- | Read a 'SimpleTopology' from a 'BenchTopology' file and a 'Latencies' database.
readSimpleTopologyFromBenchTopologyAndLatency :: FilePath -> FilePath -> IO SimpleTopology
readSimpleTopologyFromBenchTopologyAndLatency benchTopologyFile latencyFile = do
  benchTopology <- readBenchTopology benchTopologyFile
  latencies <- readLatencies benchTopology latencyFile
  pure $ benchTopologyToSimpleTopology latencies benchTopology

-- | Read a 'SimpleTopology' from a JSON file.
readSimpleTopology :: FilePath -> IO SimpleTopology
readSimpleTopology = throwDecode <=< BSL.readFile

-- | Write a 'SimpleTopology' to a JSON file.
writeSimpleTopology :: FilePath -> SimpleTopology -> IO ()
writeSimpleTopology simpleTopologyFile = BSL.writeFile simpleTopologyFile . encode

-- | Get the set of cluster names in a 'SimpleTopology'.
clusterSet :: SimpleTopology -> Set (Maybe ClusterName)
clusterSet = S.fromList . map (.clusterName) . V.toList . (.nodes)

-- | Get the list of unique cluster names in a 'SimpleTopology'.
clusters :: SimpleTopology -> [Maybe ClusterName]
clusters = S.toList . clusterSet

regionNameToClusterName :: RegionName -> ClusterName
regionNameToClusterName = ClusterName . unRegionName

clusterNameToRegionName :: ClusterName -> RegionName
clusterNameToRegionName = RegionName . unClusterName

--------------------------------------------------------------------------------
-- Conversion between SimpleTopology and FGL Graph
--------------------------------------------------------------------------------

data SimpleNodeInfo = SimpleNodeInfo
  { name :: NodeName
  , clusterName :: Maybe ClusterName
  }
  deriving (Eq, Show)

-- | Convert a 'SimpleTopology' to an FGL 'Gr'.
simpleTopologyToGr ::
  SimpleTopology ->
  Gr SimpleNodeInfo Latency
simpleTopologyToGr topology = G.mkGraph graphNodes graphEdges
 where
  nameToIdMap =
    M.fromList
      [ (node.name, node.nodeId)
      | node <- V.toList topology.nodes
      ]
  graphNodes =
    [ (nodeIdToNode nodeId, SimpleNodeInfo{..})
    | SimpleNode{..} <- V.toList topology.nodes
    ]
  graphEdges =
    [ (producerId, consumerId, latency)
    | consumer <- V.toList topology.nodes
    , let consumerId = nodeIdToNode consumer.nodeId
    , (producerName, latency) <- M.toList consumer.producers
    , let producerId = nodeIdToNode $ nameToIdMap M.! producerName
    ]

-- | Helper for testing. Convert an an FGL 'Gr' to a 'SimpleTopology'.
grToSimpleTopology ::
  Gr SimpleNodeInfo Latency ->
  SimpleTopology
grToSimpleTopology gr = SimpleTopology{nodes}
 where
  nodes =
    V.fromList $
      [ SimpleNode{name, nodeId, producers, clusterName}
      | (node, SimpleNodeInfo{..}) <- G.labNodes gr
      , let nodeId = nodeToNodeId node
      , let producers = M.findWithDefault M.empty name producersMap
      ]
  producersMap :: Map NodeName (Map NodeName Latency)
  producersMap =
    M.unionsWith (<>) $
      [ M.singleton consumerName (M.singleton producerName latency)
      | (producer, consumer, latency) <- G.labEdges gr
      , let producerId = nodeToNodeId producer
      , let consumerId = nodeToNodeId consumer
      , let producerName = nodeIdToNodeNameMap M.! producerId
      , let consumerName = nodeIdToNodeNameMap M.! consumerId
      ]
  nodeIdToNodeNameMap :: Map NodeId NodeName
  nodeIdToNodeNameMap =
    M.fromList $
      [ (nodeId, name)
      | (node, SimpleNodeInfo{..}) <- G.labNodes gr
      , let nodeId = nodeToNodeId node
      ]

addNodeNames :: Gr (Maybe ClusterName) b -> Gr SimpleNodeInfo b
addNodeNames = G.gmap (\(inEdges, node, clusterName, outEdges) -> (inEdges, node, SimpleNodeInfo{name = nodeToNodeName node, ..}, outEdges))

nodeToNodeName :: G.Node -> NodeName
nodeToNodeName = NodeName . T.pack . ("node-" <>) . show @Int

nodeIdToNode :: NodeId -> G.Node
nodeIdToNode = coerce

nodeToNodeId :: G.Node -> NodeId
nodeToNodeId = coerce

--------------------------------------------------------------------------------
-- Augmentation with Position Information
--------------------------------------------------------------------------------

clusterByClusterName :: G.LNode SimpleNodeInfo -> GV.NodeCluster ClusterName (G.LNode SimpleNodeInfo)
clusterByClusterName node@(_, nodeInfo) = case nodeInfo.clusterName of
  Nothing -> GV.N node
  Just nodeClusterName -> GV.C nodeClusterName (GV.N node)

clusterNameToLazyText :: ClusterName -> LazyText
clusterNameToLazyText = TL.fromStrict . unClusterName

clusterNameToGraphID :: ClusterName -> GVTG.GraphID
clusterNameToGraphID = GVTG.Str . clusterNameToLazyText

defaultParams :: GraphvizParams G.Node SimpleNodeInfo Latency ClusterName SimpleNodeInfo
defaultParams =
  Params
    { isDirected = True
    , globalAttributes = []
    , clusterBy = clusterByClusterName
    , isDotCluster = const True
    , clusterID = clusterNameToGraphID
    , fmtCluster = const []
    , fmtNode = const []
    , fmtEdge = const []
    }

augmentWithPositionInformation ::
  GraphvizParams G.Node SimpleNodeInfo Latency ClusterName SimpleNodeInfo ->
  WorldDimensions ->
  Gr SimpleNodeInfo Latency ->
  IO (Gr (SimpleNodeInfo, Point) (Latency, Path))
augmentWithPositionInformation params1 worldDimensions gr1 = do
  -- Add world dimension and edge IDs
  let params2 =
        params1
          { fmtEdge = GV.setEdgeIDAttribute params1.fmtEdge
          }
  let gr2 = GV.addEdgeIDs gr1
  let dg2 = GV.graphToDot params2 gr2
  gr3 <- GV.dotAttributes params2.isDirected gr2 dg2
  let gr4 = G.nemap unsafeUnpackAttributeNode unsafeUnpackAttributeEdge gr3
  let gr5 = rescaleGraph worldDimensions gr4
  pure gr5

unsafeUnpackAttributeNode :: GV.AttributeNode a -> (a, Point)
unsafeUnpackAttributeNode ([GV.Pos (GV.PointPos point)], x) = (x, unsafeToPoint point)
unsafeUnpackAttributeNode _ = error "post-condition of dotizeGraph violated"

unsafeToPoint :: GV.Point -> Point
unsafeToPoint (GV.Point x y _z False) = Point x y
unsafeToPoint _ = error "post-condition of dotizeGraph violated"

unsafeUnpackAttributeEdge :: GV.AttributeEdge a -> (a, Path)
unsafeUnpackAttributeEdge ([GV.Pos (GV.SplinePos splines)], x) = (x, unsafeToPath splines)
unsafeUnpackAttributeEdge _ = error "post-condition of dotizeGraph violated"

unsafeToPath :: [GV.Spline] -> Path
unsafeToPath = Path . concatMap toPoints
 where
  toPoints :: GV.Spline -> [Point]
  toPoints (GV.Spline maybeEnd maybeStart points) =
    fmap unsafeToPoint . concat $
      [ maybeToList maybeStart
      , points
      , maybeToList maybeEnd
      ]

rescaleGraph :: WorldDimensions -> Gr (node, Point) (edge, Path) -> Gr (node, Point) (edge, Path)
rescaleGraph (w, h) gr = G.nmap (second rescalePoint) gr
 where
  rescalePoint p = Point (rescaleX p._1) (rescaleY p._2)
   where
    ps0 = fmap (snd . snd) (G.labNodes gr)
    rescaleX x = xPad + (x - x0l) / w0 * (w - 2 * xPad)
     where
      xPad = 0.05 * w
      (x0l, x0u) = (minimum &&& maximum) (fmap _1 ps0)
      w0 = x0u - x0l
    rescaleY y = yPad + (y - y0l) / h0 * (h - 2 * yPad)
     where
      yPad = 0.05 * h
      (y0l, y0u) = (minimum &&& maximum) (fmap _2 ps0)
      h0 = y0u - y0l

forgetPositionInformation ::
  Gr (SimpleNodeInfo, Point) (Latency, Path) ->
  Gr SimpleNodeInfo Latency
forgetPositionInformation =
  G.nemap fst fst

--------------------------------------------------------------------------------
-- Conversion between FGL Graph and P2PTopography
--------------------------------------------------------------------------------

grToP2PTopography ::
  GraphvizParams G.Node SimpleNodeInfo Latency ClusterName SimpleNodeInfo ->
  WorldDimensions ->
  Gr SimpleNodeInfo Latency ->
  IO P2PTopography
grToP2PTopography params worldDimensions gr1 = do
  gr2 <- augmentWithPositionInformation params worldDimensions gr1
  let nodeInfoMap = M.fromList [(n, nodeInfo) | (n, nodeInfo) <- G.labNodes gr2]
  let edgeInfoMap = M.fromList [((n1, n2), edgeInfo) | (n1, n2, edgeInfo) <- G.labEdges gr2]
  let p2pNodes =
        M.fromList
          [ (nodeToNodeId node, point)
          | (node, (_, point)) <- M.assocs nodeInfoMap
          ]
  let p2pLinks =
        M.fromList
          [ ((nodeToNodeId node1, nodeToNodeId node2), latency)
          | ((node1, node2), (latency, _path)) <- M.assocs edgeInfoMap
          , let (_, _point1) = nodeInfoMap M.! node1
          , let (_, _point2) = nodeInfoMap M.! node2
          ]
  let p2pWorldShape = WorldShape{worldIsCylinder = True, ..}
  pure P2PTopography{..}

readP2PTopography ::
  GraphvizParams G.Node SimpleNodeInfo Latency ClusterName SimpleNodeInfo ->
  WorldDimensions ->
  FilePath ->
  IO P2PTopography
readP2PTopography params worldDimensions simpleTopologyFile = do
  simpleTopology <- readSimpleTopology simpleTopologyFile
  grToP2PTopography params worldDimensions (simpleTopologyToGr simpleTopology)
