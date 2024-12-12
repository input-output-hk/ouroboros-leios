{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import qualified Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.GraphViz (GraphvizParams (..), X11Color (..))
import qualified Data.GraphViz as GV
import qualified Data.GraphViz.Attributes as GVA
import qualified Data.GraphViz.Attributes.Complete as GVAC
import qualified Data.GraphViz.Commands as GVC
import qualified Data.GraphViz.Types as GVT (PrintDot)
import qualified Data.GraphViz.Types.Generalised as GVTG
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (maybeToList)
import qualified Data.Sequence as Seq
import qualified Data.Set as S
import Data.Text (Text)
import Data.Text.Lazy (LazyText)
import qualified Data.Text.Lazy as TL
import Data.Vector (Vector)
import qualified Data.Vector as V
import Database.SQLite.Simple (NamedParam (..))
import qualified Database.SQLite.Simple as SQLlite
import qualified Database.SQLite.Simple.ToField as SQLite (ToField)
import GHC.Generics (Generic)
import GHC.Records (HasField)
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
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON, FromJSONKey, ToJSONKey)
  deriving newtype (GVT.PrintDot)
  deriving newtype (SQLite.ToField)
  deriving newtype (PrintfArg)

newtype OrgName = OrgName {unOrgName :: Text}
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

newtype RegionName = RegionName {unRegionName :: Text}
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

data BenchTopologyNode
  = BenchTopologyNode
  { name :: !NodeName
  , nodeId :: !NodeId
  , org :: !OrgName
  , pools :: !(Maybe Int)
  , producers :: !(Vector NodeName)
  , region :: !RegionName
  , stakePool :: !Bool
  }
  deriving (Show, Generic)

instance ToJSON BenchTopologyNode where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON BenchTopologyNode

newtype BenchTopology = BenchTopology
  { coreNodes :: Vector BenchTopologyNode
  }
  deriving (Show, Generic)

instance ToJSON BenchTopology where
  toEncoding =
    genericToEncoding
      defaultOptions
        { unwrapUnaryRecords = False
        }

instance FromJSON BenchTopology where
  parseJSON =
    genericParseJSON
      defaultOptions
        { unwrapUnaryRecords = False
        }

readBenchTopology :: FilePath -> IO BenchTopology
readBenchTopology = throwDecode <=< BSL.readFile

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

data SimpleNode
  = SimpleNode
  { name :: !NodeName
  , nodeId :: !NodeId
  , producers :: !(Map NodeName Latency)
  , region :: !RegionName
  }
  deriving (Show, Generic)

instance ToJSON SimpleNode where
  toEncoding =
    genericToEncoding
      defaultOptions
        { unwrapUnaryRecords = False
        }

instance FromJSON SimpleNode where
  parseJSON =
    genericParseJSON
      defaultOptions
        { unwrapUnaryRecords = False
        }

newtype SimpleTopology
  = SimpleTopology
  { nodes :: Vector SimpleNode
  }
  deriving (Show, Generic)

instance ToJSON SimpleTopology where
  toEncoding =
    genericToEncoding
      defaultOptions
        { unwrapUnaryRecords = False
        }

instance FromJSON SimpleTopology where
  parseJSON =
    genericParseJSON
      defaultOptions
        { unwrapUnaryRecords = False
        }

benchTopologyNodeToSimpleNode :: Latencies -> BenchTopologyNode -> SimpleNode
benchTopologyNodeToSimpleNode latencies benchTopologyNode =
  SimpleNode
    { name = benchTopologyNode.name
    , nodeId = benchTopologyNode.nodeId
    , producers = latencies M.! benchTopologyNode.name
    , region = benchTopologyNode.region
    }

benchTopologyToSimpleTopology :: Latencies -> BenchTopology -> SimpleTopology
benchTopologyToSimpleTopology latencies benchTopology =
  SimpleTopology{nodes = benchTopologyNodeToSimpleNode latencies <$> benchTopology.coreNodes}

readSimpleTopologyFromBenchTopologyAndLatency :: FilePath -> FilePath -> IO SimpleTopology
readSimpleTopologyFromBenchTopologyAndLatency benchTopologyFile latencyFile = do
  benchTopology <- readBenchTopology benchTopologyFile
  latencies <- readLatencies benchTopology latencyFile
  pure $ benchTopologyToSimpleTopology latencies benchTopology

readSimpleTopology :: FilePath -> IO SimpleTopology
readSimpleTopology = throwDecode <=< BSL.readFile

writeSimpleTopology :: FilePath -> SimpleTopology -> IO ()
writeSimpleTopology simpleTopologyFile = BSL.writeFile simpleTopologyFile . encode

--------------------------------------------------------------------------------
-- General Topology
--
-- Abstraction over Bench Topology and Simple Topology
--------------------------------------------------------------------------------

class
  ( HasField "name" node NodeName
  , HasField "nodeId" node NodeId
  , HasField "region" node RegionName
  ) =>
  Node node edge
    | node -> edge
  where
  outgoingEdges :: node -> Map NodeName edge

  adjacentNodes :: node -> [NodeName]
  adjacentNodes = M.keys . outgoingEdges

instance Node BenchTopologyNode () where
  outgoingEdges node =
    M.fromList [(producerName, ()) | producerName <- V.toList node.producers]

instance Node SimpleNode Latency where
  outgoingEdges = (.producers)

class Node node edge => Topology topology node edge | topology -> node where
  allNodes :: topology -> [node]

  allRegions :: topology -> [RegionName]
  allRegions = S.toList . foldr (S.insert . (.region)) S.empty . allNodes

instance Topology BenchTopology BenchTopologyNode () where
  allNodes = V.toList . (.coreNodes)

instance Topology SimpleTopology SimpleNode Latency where
  allNodes = V.toList . (.nodes)

--------------------------------------------------------------------------------
-- Conversion to GraphViz Graph
--------------------------------------------------------------------------------

regionNameToLazyText :: RegionName -> LazyText
regionNameToLazyText = TL.fromStrict . unRegionName

regionNameToGraphID :: RegionName -> GVTG.GraphID
regionNameToGraphID = GVTG.Str . regionNameToLazyText

-- NOTE: Taken from https://sashamaps.net/docs/resources/20-colors/
simpleDistinctColors :: [X11Color]
simpleDistinctColors =
  cycle
    [ Red
    , Green
    , Yellow
    , Blue
    , Orange
    , Purple
    , Cyan
    , Magenta
    , LimeGreen
    , Pink
    , Turquoise
    , Lavender
    , Brown
    , Beige
    , Maroon
    , MintCream
    , OliveDrab
    , Coral
    , Navy
    , Gray
    , White
    , Black
    ]

toDotGraphAsTorus ::
  Topology topology node edge =>
  topology ->
  GVTG.DotGraph NodeName
toDotGraphAsTorus topology =
  GVTG.DotGraph True True Nothing . Seq.fromList $
    globalStatements : nodeStatements <> edgeStatements
 where
  globalStatements =
    GVTG.GA . GVTG.GraphAttrs $
      [ GVAC.Smoothing GVAC.Spring
      , GVAC.K 0.5
      , GVAC.RepulsiveForce 2.0
      ]
  nodeStatements =
    [ GVTG.DN . GVTG.DotNode nodeName $
      [ GVA.style GVA.filled
      , GVA.fillColor nodeRegionColor
      ]
    | node <- allNodes topology
    , let nodeName = node.name
    , let nodeRegionColor = regionColorMap M.! node.region
    ]
  edgeStatements =
    [ GVTG.DE . GVTG.DotEdge producerName consumerName $
      [ GVA.fillColor producerRegionColor
      ]
    | consumer <- allNodes topology
    , let consumerName = consumer.name
    , producerName <- adjacentNodes consumer
    , let producerRegionColor = regionColorMap M.! (nodeRegionMap M.! producerName)
    ]
  nodeRegionMap =
    M.fromList [(node.name, node.region) | node <- allNodes topology]
  regionColorMap =
    M.fromList $ zip (allRegions topology) simpleDistinctColors

toDotGraphByRegion ::
  Topology topology node edge =>
  topology ->
  GVTG.DotGraph NodeName
toDotGraphByRegion topology =
  GVTG.DotGraph True True Nothing . Seq.fromList $
    graphAttributes : subGraphStatements <> edgeStatements
 where
  graphAttributes =
    GVTG.GA . GVTG.GraphAttrs $
      []
  subGraphStatements =
    [ GVTG.SG . GVTG.DotSG True (Just subGraphId) . Seq.fromList $
      subGraphAttributtes : subGraphNodeStatements <> subGraphEdgeStatements
    | regionName <- allRegions topology
    , let subGraphId = regionNameToGraphID regionName
    , let subGraphAttributtes =
            GVTG.GA . GVTG.GraphAttrs $
              [ GVA.textLabel (regionNameToLazyText regionName)
              ]
    , let subGraphNodeStatements =
            [ GVTG.DN . GVTG.DotNode nodeName $
              [ GVA.style GVA.filled
              , GVA.fillColor nodeRegionColor
              ]
            | node <- allNodes topology
            , let nodeName = node.name
            , let nodeRegionName = node.region
            , nodeRegionName == regionName
            , let nodeRegionColor = regionColorMap M.! nodeRegionName
            ]
    , let subGraphEdgeStatements =
            [ GVTG.DE . GVTG.DotEdge producerName consumerName $
              [ GVA.fillColor producerRegionColor
              ]
            | consumer <- allNodes topology
            , let consumerName = consumer.name
            , let consumerRegionName = consumer.region
            , consumerRegionName == regionName
            , producerName <- adjacentNodes consumer
            , let producerRegionName = nodeRegionMap M.! producerName
            , producerRegionName == regionName
            , let producerRegionColor = regionColorMap M.! producerRegionName
            ]
    ]
  edgeStatements =
    [ GVTG.DE . GVTG.DotEdge producerName consumerName $
      [ GVA.fillColor producerRegionColor
      ]
    | consumer <- allNodes topology
    , let consumerName = consumer.name
    , let consumerRegionName = consumer.region
    , producerName <- adjacentNodes consumer
    , let producerRegionName = nodeRegionMap M.! producerName
    , let producerRegionColor = regionColorMap M.! producerRegionName
    , consumerRegionName /= producerRegionName
    ]
  nodeRegionMap =
    M.fromList [(node.name, node.region) | node <- allNodes topology]
  regionColorMap =
    M.fromList $ zip (allRegions topology) simpleDistinctColors

renderTopologyAsTorus ::
  Topology topology node edge => FilePath -> topology -> IO ()
renderTopologyAsTorus outputFile topology =
  void $ GVC.runGraphvizCommand GVC.Sfdp (toDotGraphAsTorus topology) GVC.Png outputFile

renderTopologyByRegion ::
  Topology topology node edge => FilePath -> topology -> IO ()
renderTopologyByRegion outputFile topology =
  void $ GVC.runGraphvizCommand GVC.Dot (toDotGraphByRegion topology) GVC.Png outputFile

--------------------------------------------------------------------------------
-- Conversion to FGL Graph
--------------------------------------------------------------------------------

toGraph ::
  Topology topology node edge =>
  topology ->
  Gr node edge
toGraph topology = G.mkGraph graphNodes graphEdges
 where
  nameToIdMap =
    M.fromList
      [ (node.name, node.nodeId)
      | node <- allNodes topology
      ]
  graphNodes =
    [ (consumerId, consumer)
    | consumer <- allNodes topology
    , let consumerId = coerce consumer.nodeId
    ]
  graphEdges =
    [ (consumerId, producerId, producerLatency)
    | consumer <- allNodes topology
    , let consumerId = coerce consumer.nodeId
    , (producerName, producerLatency) <- M.toList (outgoingEdges consumer)
    , let producerId = coerce $ nameToIdMap M.! producerName
    ]

toGraphWithPositionInformation ::
  forall topology node edge.
  Topology topology node edge =>
  WorldDimensions ->
  topology ->
  IO (Gr (node, Point) (edge, Path))
toGraphWithPositionInformation (w, h) topology = do
  let gr0 = toGraph topology
  let gr1 = GV.dotizeGraph params gr0
  let gr2 = G.nemap unsafeUnpackAttributeNode unsafeUnpackAttributeEdge gr1
  let gr3 = rescale gr2
  pure gr3
 where
  params =
    GV.defaultParams
      { globalAttributes = [GV.GraphAttrs [GVAC.Layout GVC.Neato]]
      , clusterBy = clusterByRegion
      , clusterID = regionNameToGraphID
      }

  rescale :: Gr (node, Point) (edge, Path) -> Gr (node, Point) (edge, Path)
  rescale gr = G.nmap (second rescalePoint) gr
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

  unsafeUnpackAttributeNode :: GV.AttributeNode a -> (a, Point)
  unsafeUnpackAttributeNode ([GVAC.Pos (GVAC.PointPos point)], x) = (x, unsafeToPoint point)
  unsafeUnpackAttributeNode _ = error "post-condition of dotizeGraph violated"

  unsafeToPoint :: GVAC.Point -> Point
  unsafeToPoint (GVAC.Point x y _z False) = Point x y
  unsafeToPoint _ = error "post-condition of dotizeGraph violated"

  unsafeUnpackAttributeEdge :: GV.AttributeEdge a -> (a, Path)
  unsafeUnpackAttributeEdge ([GVAC.Pos (GVAC.SplinePos splines)], x) = (x, unsafeToPath splines)
  unsafeUnpackAttributeEdge _ = error "post-condition of dotizeGraph violated"

  unsafeToPath :: [GVAC.Spline] -> Path
  unsafeToPath = Path . concatMap toPoints
   where
    toPoints :: GVAC.Spline -> [Point]
    toPoints (GVAC.Spline maybeEnd maybeStart points) =
      fmap unsafeToPoint . concat $
        [ maybeToList maybeStart
        , points
        , maybeToList maybeEnd
        ]

  clusterByRegion :: G.LNode node -> GV.NodeCluster RegionName (G.LNode node)
  clusterByRegion lnode@(_, node) = GV.C node.region (GV.N lnode)

toP2PTopography ::
  WorldDimensions ->
  SimpleTopology ->
  IO P2PTopography
toP2PTopography worldDimensions topology = do
  graphWithInfo <- toGraphWithPositionInformation worldDimensions topology
  let nodeInfoMap = M.fromList [(n, nodeInfo) | (n, nodeInfo) <- G.labNodes graphWithInfo]
  let edgeInfoMap = M.fromList [((n1, n2), edgeInfo) | (n1, n2, edgeInfo) <- G.labEdges graphWithInfo]
  let p2pNodes =
        M.fromList
          [ (node.nodeId, point)
          | (node, point) <- M.elems nodeInfoMap
          ]
  let p2pLinks =
        M.fromList
          [ ((node1.nodeId, node2.nodeId), latency)
          | ((n1, n2), (latency, _path)) <- M.assocs edgeInfoMap
          , let (node1, _point1) = nodeInfoMap M.! n1
          , let (node2, _point2) = nodeInfoMap M.! n2
          ]
  let p2pWorldShape = WorldShape{worldIsCylinder = True, ..}
  pure P2PTopography{..}

readP2PTopography :: WorldDimensions -> FilePath -> IO P2PTopography
readP2PTopography worldDimensions simpleTopologyFile = do
  simpleTopology <- readSimpleTopology simpleTopologyFile
  toP2PTopography worldDimensions simpleTopology
