{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Topology (
  module LeiosTopology,
  module Topology,
)
where

import Codec.Compression.GZip as GZip (decompress)
import Control.Arrow (Arrow ((&&&)), second)
import Control.Exception (Exception (displayException), assert)
import Control.Monad (forM_, guard, unless, (<=<))
import Data.Aeson (withObject)
import qualified Data.Aeson as Json
import Data.Aeson.Types (FromJSON (..), KeyValue ((.=)), Options (..), Parser, ToJSON (..), Value (..), defaultOptions, genericParseJSON, genericToEncoding, object, (.!=), (.:?))
import qualified Data.ByteString.Lazy as BSL
import Data.Coerce (coerce)
import Data.Default (Default (..))
import Data.Function (on)
import qualified Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.GraphViz (GraphvizParams (..))
import qualified Data.GraphViz as GV
import qualified Data.GraphViz.Attributes.Complete as GV
import qualified Data.GraphViz.Types as GVT (PrintDot)
import qualified Data.GraphViz.Types.Generalised as GVTG
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.List (sort, sortBy, uncons)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe, mapMaybe, maybeToList)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Yaml (ParseException)
import qualified Data.Yaml as Yaml
import Database.SQLite.Simple (NamedParam (..))
import qualified Database.SQLite.Simple as SQLlite
import qualified Database.SQLite.Simple.ToField as SQLite (ToField)
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import LeiosTopology
import ModelTCP (Bytes, kilobytes)
import P2P (Latency, Link, Link' (..), P2PTopography (..), P2PTopographyCharacteristics (..), genArbitraryP2PTopography, pattern (:<-))
import SimTypes (NodeId (..), NumCores (..), Path (..), Point (..), StakeFraction (StakeFraction), World (..), WorldDimensions)
import System.Exit (exitFailure)
import System.FilePath (dropExtension, takeDirectory, takeExtension, takeExtensions, takeFileName)
import System.IO (hClose, hPutStrLn, stderr)
import System.IO.Temp (withTempFile)
import System.Random (RandomGen)
import Text.Printf (printf)

deriving newtype instance GVT.PrintDot NodeName
deriving newtype instance SQLite.ToField NodeName

instance HasField "latencyS" LinkInfo Latency where
  getField :: LinkInfo -> Latency
  getField linkInfo = linkInfo.latencyMs.unLatencyMs / 1000

--------------------------------------------------------------------------------
-- Convert between BenchTopology and Topology 'CLUSTER
--------------------------------------------------------------------------------

-- | Convert a 'BenchTopology' and 'Latencies' to a 'Topology'.
benchTopologyToTopology :: BenchTopology -> LatenciesMs -> Word -> Topology 'CLUSTER
benchTopologyToTopology benchTopology latencies stakeShareSize =
  Topology
    { nodes =
        M.fromList
          [ (benchTopologyNode.name, benchTopologyNodeToNode benchTopologyNode)
          | benchTopologyNode <- V.toList benchTopology.coreNodes
          ]
    }
 where
  benchTopologyNodeToNode :: BenchTopologyNode -> Node 'CLUSTER
  benchTopologyNodeToNode benchTopologyNode =
    Node
      { nodeInfo =
          NodeInfo
            { stake = maybe 0 (stakeShareSize *) benchTopologyNode.pools
            , cpuCoreCount = Unbounded
            , location = LocCluster (regionNameToClusterName <$> benchTopologyNode.region)
            , adversarial = Nothing
            }
      , producers =
          M.fromList
            [ (producerName, LinkInfo{..})
            | let consumerName = benchTopologyNode.name
            , producerName <- V.toList benchTopologyNode.producers
            , let latencyMs = (latencies M.! consumerName) M.! producerName
            , let bandwidthBytesPerSecond = Unbounded
            ]
      }

regionNameToClusterName :: RegionName -> ClusterName
regionNameToClusterName = ClusterName . unRegionName

clusterNameToRegionName :: ClusterName -> RegionName
clusterNameToRegionName = RegionName . unClusterName

-- | Create a 'Topology' from a file.
readTopology :: FilePath -> IO (Either ParseException SomeTopology)
readTopology = Yaml.decodeFileEither

-- | Write a 'Topology' to a file.
writeTopology :: FilePath -> SomeTopology -> IO ()
writeTopology = Yaml.encodeFile

-- | Create a 'Topology' from a 'BenchTopology', a 'Latencies' database, and a stake share size.
readTopologyFromBenchTopology :: FilePath -> FilePath -> Word -> IO (Topology 'CLUSTER)
readTopologyFromBenchTopology benchTopologyFile latencyFile stakeShareSize = do
  benchTopology <- readBenchTopology benchTopologyFile
  latencies <- readLatencies benchTopology latencyFile
  pure $ benchTopologyToTopology benchTopology latencies stakeShareSize

--------------------------------------------------------------------------------
-- Convert between Topology and FGL Graph
--------------------------------------------------------------------------------

-- | Convert 'SomeTopology' to an FGL 'Gr' with coordinates.
someTopologyToGrCoord2D ::
  GraphvizParams G.Node (NodeName, NodeInfo 'CLUSTER) LinkInfo ClusterName (NodeName, NodeInfo 'CLUSTER) ->
  SomeTopology ->
  IO (Gr (NodeName, NodeInfo 'COORD2D) LinkInfo)
someTopologyToGrCoord2D params = \case
  SomeTopology SCLUSTER topology -> layoutGr params $ topologyToGr topology
  SomeTopology SCOORD2D topology -> pure $ topologyToGr topology

linkToEdge :: Link -> a -> G.LEdge a
linkToEdge Link{..} x = (coerce upstream, coerce downstream, x)

edgeToLink :: G.LEdge a -> (Link, a)
edgeToLink (producer, consumer, x) =
  ( Link
      { upstream = NodeId producer
      , downstream = NodeId consumer
      }
  , x
  )

-- | Convert 'Topology' to an FGL 'Gr'.
--
--   edges are in '(producer, consumer, info)' format, c.f. 'linkToEdge'/'edgeToLink' .
topologyToGr :: Topology lk -> Gr (NodeName, NodeInfo lk) LinkInfo
topologyToGr topology = G.mkGraph grNodes grLinks
 where
  nodeNameToGrNodeMap :: Map NodeName G.Node
  nodeNameToGrNodeMap = M.fromList $ zip (M.keys topology.nodes) [0 ..]
  grNodes =
    [ (grNode, (nodeName, nodeInfo))
    | (nodeName, Node{..}) <- M.toList topology.nodes
    , let grNode = nodeNameToGrNodeMap M.! nodeName
    ]
  grLinks =
    [ (grProducer, grConsumer, linkInfo)
    | (consumerName, Node{..}) <- M.toList topology.nodes
    , let grConsumer = nodeNameToGrNodeMap M.! consumerName
    , (producerName, linkInfo) <- M.toList producers
    , let grProducer = nodeNameToGrNodeMap M.! producerName
    ]

-- | Convert an FGL 'Gr' to a 'Topology'.
grToTopology :: forall lk. Gr (NodeName, NodeInfo lk) LinkInfo -> Topology lk
grToTopology gr =
  Topology
    { nodes =
        M.fromList
          [ (nodeName, Node{..})
          | (nodeName, nodeInfo) <- M.elems nodeGrToNodeNameAndInfoMap
          , let producers = nodeNameToProducersMap M.! nodeName
          ]
    }
 where
  nodeGrToNodeNameAndInfoMap :: Map G.Node (NodeName, NodeInfo lk)
  nodeGrToNodeNameAndInfoMap = M.fromList (G.labNodes gr)

  nodeNameToProducersMap :: Map NodeName (Map NodeName LinkInfo)
  nodeNameToProducersMap =
    M.unionsWith
      (<>)
      [ M.singleton consumerName (M.singleton producerName linkInfo)
      | (producerGr, consumerGr, linkInfo) <- G.labEdges gr
      , let consumerName = fst (nodeGrToNodeNameAndInfoMap M.! consumerGr)
      , let producerName = fst (nodeGrToNodeNameAndInfoMap M.! producerGr)
      ]

--------------------------------------------------------------------------------
-- Convert 'NodeInfo' in 'Topology' from cluster names to explicit coordinates
--------------------------------------------------------------------------------

layoutTopology ::
  GraphvizParams G.Node (NodeName, NodeInfo 'CLUSTER) LinkInfo ClusterName (NodeName, NodeInfo 'CLUSTER) ->
  Topology 'CLUSTER ->
  IO (Topology 'COORD2D)
layoutTopology params = fmap grToTopology . layoutGr params . topologyToGr

layoutGr ::
  GraphvizParams G.Node (NodeName, NodeInfo 'CLUSTER) link ClusterName (NodeName, NodeInfo 'CLUSTER) ->
  Gr (NodeName, NodeInfo 'CLUSTER) link ->
  IO (Gr (NodeName, NodeInfo 'COORD2D) link)
layoutGr params gr =
  G.nemap (nodeInfoClusterToNodeInfoCoord2D . unsafeUnpackAttributeNode) snd <$> GV.dotAttributes params.isDirected gr' dg'
 where
  gr' = GV.addEdgeIDs gr
  dg' = GV.graphToDot params{fmtEdge = GV.setEdgeIDAttribute params.fmtEdge} gr'

nodeInfoClusterToNodeInfoCoord2D :: ((NodeName, NodeInfo 'CLUSTER), Point) -> (NodeName, NodeInfo 'COORD2D)
nodeInfoClusterToNodeInfoCoord2D ((name, NodeInfo{..}), coord2d) = (name, NodeInfo{location = LocCoord2D coord2d, ..})

unsafeUnpackAttributeNode :: GV.AttributeNode a -> (a, Point)
unsafeUnpackAttributeNode (attrs, x) = (x, fromMaybe errorMessage $ maybeGetPoint attrs)
 where
  errorMessage = error $ "post-condition of dotizeGraph violated; yielded attributes " <> show attrs
  maybeGetPoint :: GV.Attributes -> Maybe Point
  maybeGetPoint = fmap fst . uncons . mapMaybe maybeToPoint
   where
    maybeToPoint :: GV.Attribute -> Maybe Point
    maybeToPoint (GV.Pos (GV.PointPos point)) = Just (pointToPoint point)
    maybeToPoint _ = Nothing

unsafeUnpackAttributeEdge :: GV.AttributeEdge a -> (a, Path)
unsafeUnpackAttributeEdge (attrs, x) = (x, fromMaybe errorMessage $ maybeGetPath attrs)
 where
  errorMessage = error $ "post-condition of dotizeGraph violated; yielded attributes " <> show attrs
  maybeGetPath :: GV.Attributes -> Maybe Path
  maybeGetPath = fmap fst . uncons . mapMaybe maybeToPath
   where
    maybeToPath :: GV.Attribute -> Maybe Path
    maybeToPath (GV.Pos (GV.SplinePos splines))
      | null splines = Nothing
      | otherwise = Just $ mconcat (splineToPath <$> splines)
    maybeToPath _ = Nothing

pointToPoint :: GV.Point -> Point
pointToPoint (GV.Point x y _z _3d) = Point x y

splineToPath :: GV.Spline -> Path
splineToPath (GV.Spline maybeEnd maybeStart points) =
  Path . map pointToPoint . concat $ [maybeToList maybeStart, points, maybeToList maybeEnd]

rescaleGraph :: WorldDimensions -> Gr (NodeName, NodeInfo 'COORD2D) LinkInfo -> Gr (NodeName, NodeInfo 'COORD2D) LinkInfo
rescaleGraph (w, h) gr = G.nmap (second rescaleNodeInfo) gr
 where
  rescaleNodeInfo :: NodeInfo 'COORD2D -> NodeInfo 'COORD2D
  rescaleNodeInfo NodeInfo{location = LocCoord2D p, ..} =
    NodeInfo{location = LocCoord2D (rescalePoint p), ..}

  rescalePoint :: Point -> Point
  rescalePoint p = Point (rescaleX p._1) (rescaleY p._2)
   where
    ps0 :: [Point]
    ps0 = (.location.coord2D) . snd . snd <$> G.labNodes gr

    rescaleX :: Double -> Double
    rescaleX x = xPad + (x - x0l) / w0 * (w - 2 * xPad)
     where
      xPad = 0.05 * w
      (x0l, x0u) = (minimum &&& maximum) (fmap _1 ps0)
      w0 = x0u - x0l

    rescaleY :: Double -> Double
    rescaleY y = yPad + (y - y0l) / h0 * (h - 2 * yPad)
     where
      yPad = 0.05 * h
      (y0l, y0u) = (minimum &&& maximum) (fmap _2 ps0)
      h0 = y0u - y0l

defaultParams :: GraphvizParams G.Node (NodeName, NodeInfo 'CLUSTER) link ClusterName (NodeName, NodeInfo 'CLUSTER)
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

clusterByClusterName :: G.LNode (NodeName, NodeInfo 'CLUSTER) -> GV.NodeCluster ClusterName (G.LNode (NodeName, NodeInfo 'CLUSTER))
clusterByClusterName node@(_, (_, NodeInfo{location = LocCluster maybeClusterName})) =
  maybe (GV.N node) (\clusterName -> GV.C clusterName (GV.N node)) maybeClusterName

clusterNameToLazyText :: ClusterName -> TL.Text
clusterNameToLazyText = TL.fromStrict . unClusterName

clusterNameToGraphID :: ClusterName -> GVTG.GraphID
clusterNameToGraphID = GVTG.Str . clusterNameToLazyText

forgetPoints :: Gr (a, Point) b -> Gr a b
forgetPoints = G.nmap fst

forgetPaths :: Gr a (b, Path) -> Gr a b
forgetPaths = G.emap fst

forgetPosition :: Gr (a, Point) (b, Path) -> Gr a b
forgetPosition = forgetPoints . forgetPaths

forgetNodeInfo :: Gr (NodeInfo lk, a) b -> Gr a b
forgetNodeInfo = G.nemap snd id

--------------------------------------------------------------------------------
-- Conversion between FGL Graph and P2PNetwork
--------------------------------------------------------------------------------

type BandwidthBytesPerSecond = Bytes

data P2PNetwork = P2PNetwork
  { p2pNodes :: !(Map NodeId Point)
  , p2pNodeNames :: !(Map NodeId Text)
  , p2pNodeCores :: !(Map NodeId NumCores)
  , p2pNodeStakes :: !(Map NodeId StakeFraction)
  , p2pAdversaries :: !(Maybe (Map NodeId Behaviour))
  , p2pLinks :: !(Map Link (Latency, Maybe BandwidthBytesPerSecond))
  , p2pWorld :: !World
  }
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

validateP2PNetwork :: P2PNetwork -> IO P2PNetwork
validateP2PNetwork net = do
  let P2PTopography{..} = networkToTopology net
  let node_triplets = triangleInequalityCheck p2pLinks
  unless (null node_triplets) . putStr . unlines $
    "Latencies do not respect triangle inequalities for these nodes:" : map show node_triplets
  return net

latencyFromSecondsToMiliseconds ::
  Gr a Latency ->
  Gr a LatencyMs
latencyFromSecondsToMiliseconds =
  G.emap (LatencyMs . (* 1000.0))

latencyFromMilisecondsToSeconds ::
  Gr a LatencyMs ->
  Gr a Latency
latencyFromMilisecondsToSeconds =
  G.emap ((/ 1000.0) . unLatencyMs)

grToP2PNetwork :: World -> Gr (NodeName, NodeInfo COORD2D) LinkInfo -> P2PNetwork
grToP2PNetwork p2pWorld gr = P2PNetwork{..}
 where
  nodeInfoMap =
    M.fromList
      [ (NodeId grNode, point)
      | (grNode, point) <- G.labNodes gr
      ]
  edgeInfoMap =
    M.fromList
      [ edgeToLink e
      | e <- G.labEdges gr
      ]
  p2pNodes = Map.map ((.coord2D) . snd) nodeInfoMap
  p2pNodeNames = Map.map (coerce . fst) nodeInfoMap
  p2pNodeCores = flip Map.map nodeInfoMap $ maybe Infinite (Finite . fromIntegral) . unCpuCoreCount . (.cpuCoreCount) . snd
  p2pNodeStakes = flip Map.map nodeInfoMap $ StakeFraction . (/ totalStake) . fromIntegral . (.stake) . snd
  totalStake = fromIntegral . sum $ map (fromIntegral @_ @Integer . (.stake) . snd) $ Map.elems nodeInfoMap
  p2pLinks = flip Map.map edgeInfoMap $ \link ->
    (link.latencyS, fromIntegral <$> unBandwidthBps link.bandwidthBytesPerSecond)
  p2pAdversaries = Just $ Map.fromList [(nid, b) | (nid, (_, NodeInfo{adversarial = Just b})) <- Map.toList nodeInfoMap]

p2pNetworkToGr :: Word -> P2PNetwork -> Gr (NodeName, NodeInfo COORD2D) LinkInfo
p2pNetworkToGr totalStake P2PNetwork{..} = G.mkGraph grNodes grLinks
 where
  grNodes =
    [ (coerce nId, (nodeName, NodeInfo{..}))
    | (nId, point) <- M.toList p2pNodes
    , let nodeName = NodeName $ p2pNodeNames M.! nId
    , let stake = round $ fromIntegral totalStake * coerce @_ @Double (p2pNodeStakes M.! nId)
    , let cpuCoreCount = CpuCoreCount $ case p2pNodeCores M.! nId of
            Infinite -> Nothing
            Finite n -> Just $ fromIntegral n
    , let location = LocCoord2D point
    , let adversarial = Map.lookup nId =<< p2pAdversaries
    ]
  grLinks =
    [ linkToEdge link linkInfo
    | (link, (latency, bw)) <- M.toList p2pLinks
    , let linkInfo =
            LinkInfo
              { latencyMs = LatencyMs $ latency * 1000
              , bandwidthBytesPerSecond = BandwidthBps $ fmap fromIntegral bw
              }
    ]

p2pNetworkToSomeTopology :: Word -> P2PNetwork -> SomeTopology
p2pNetworkToSomeTopology totalStake = SomeTopology SCOORD2D . grToTopology . p2pNetworkToGr totalStake

networkToTopology :: P2PNetwork -> P2PTopography
networkToTopology P2PNetwork{..} = P2PTopography{p2pLinks = Map.map fst p2pLinks, ..}

topologyToNetwork :: P2PTopography -> P2PNetwork
topologyToNetwork P2PTopography{..} = P2PNetwork{p2pLinks = fmap (,defaultBandwidthBps) p2pLinks, ..}
 where
  p2pNodeNames = Map.mapWithKey (\(NodeId n) _ -> T.pack $ "node-" ++ show n) p2pNodes
  p2pNodeCores = Map.map (const Infinite) p2pNodes
  p2pNodeStakes = Map.map (const $ StakeFraction $ 1 / numNodes) p2pNodes
  numNodes = fromIntegral $ Map.size p2pNodes
  -- TODO: unrestricted bandwidth is unsupported
  defaultBandwidthBps = Just (kilobytes 1000)
  p2pAdversaries = Nothing

overrideUnlimitedBandwidth :: Bytes -> P2PNetwork -> P2PNetwork
overrideUnlimitedBandwidth x P2PNetwork{..} =
  P2PNetwork
    { p2pLinks = Map.map (second (maybe (Just x) Just)) p2pLinks
    , ..
    }

p2pTopologyToGr ::
  P2PTopography ->
  Gr Point Latency
p2pTopologyToGr P2PTopography{..} = G.mkGraph nodes edges
 where
  nodes =
    [ (grNode, point)
    | (NodeId grNode, point) <- M.assocs p2pNodes
    ]
  edges =
    [ linkToEdge link latencyInSeconds
    | (link, latencyInSeconds) <- M.assocs p2pLinks
    ]

readP2PTopographyFromSomeTopology ::
  GraphvizParams G.Node (NodeName, NodeInfo 'CLUSTER) LinkInfo ClusterName (NodeName, NodeInfo 'CLUSTER) ->
  World ->
  FilePath ->
  IO P2PNetwork
readP2PTopographyFromSomeTopology params p2pWorld@(World{..}) topologyFile = do
  eitherErrorOrSomeTopology <- readTopology topologyFile
  case eitherErrorOrSomeTopology of
    Left parseError -> do
      hPutStrLn stderr $ displayException parseError
      exitFailure
    Right someTopology -> do
      grToP2PNetwork p2pWorld . rescaleGraph worldDimensions
        <$> someTopologyToGrCoord2D params someTopology

--------------------------------------------------------------------------------
-- BenchTopology - Topology & Latencies
--
-- As provided in
--
--   * data/BenchTopology/topology-dense-52.json
--   * data/BenchTopology/latency.sqlite3.gz
--
--------------------------------------------------------------------------------

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
  , pools :: !(Maybe Word)
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

instance HasField "numNodes" BenchTopology Int where
  getField :: BenchTopology -> Int
  getField benchTopology = V.length benchTopology.coreNodes

instance ToJSON BenchTopology where
  toEncoding = genericToEncoding benchTopologyOptions

instance FromJSON BenchTopology where
  parseJSON = genericParseJSON benchTopologyOptions

readBenchTopology :: FilePath -> IO BenchTopology
readBenchTopology = Json.throwDecode <=< BSL.readFile

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

type LatenciesMs = Map NodeName (Map NodeName LatencyMs)

readLatencies :: BenchTopology -> FilePath -> IO LatenciesMs
readLatencies topology latencyFile =
  case takeExtensions latencyFile of
    ".sqlite3" ->
      readLatenciesSqlite3 topology latencyFile
    ".sqlite3.gz" ->
      readLatenciesSqlite3Gz topology latencyFile
    _otherwise ->
      error $ printf "unknown latency file format %s" (takeFileName latencyFile)

readLatenciesSqlite3Gz :: BenchTopology -> FilePath -> IO LatenciesMs
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

readLatenciesSqlite3 :: BenchTopology -> FilePath -> IO LatenciesMs
readLatenciesSqlite3 topology latencySqliteFile = do
  -- NOTE: The database contains the result of pings, which measures the
  --       /round-trip-time/. Therefore, we use @avg(time)/2@.
  let queryAvgTime =
        "select avg(time)/2 from ping \
        \where source = :consumer and dest = :producer \
        \or    source = :producer and dest = :consumer \
        \and   size = 64"
  latenciesRef <- newIORef mempty
  conn <- SQLlite.open latencySqliteFile
  forM_ topology.coreNodes $ \consumer -> do
    atomicModifyIORef' latenciesRef $ \latencies ->
      (M.insert consumer.name M.empty latencies, ())
    forM_ consumer.producers $ \producerName -> do
      SQLlite.queryNamed conn queryAvgTime [":consumer" := consumer.name, ":producer" := producerName] >>= \case
        [] -> error $ printf "missing latency for connection between %s and %s" consumer.name producerName
        [[latencyInMiliseconds :: Double]] ->
          atomicModifyIORef' latenciesRef $ \latencies ->
            let latency = LatencyMs latencyInMiliseconds
             in (M.adjust (M.insert producerName latency) consumer.name latencies, ())
        _otherwise -> error "impossible: SQL query for average returned multiple rows"
  readIORef latenciesRef

type LinkLatency = (Link, Latency)

-- | Returns nodes failing the expected triangle inequality for latencies.
triangleInequalityCheck :: Map Link Latency -> [(LinkLatency, LinkLatency, LinkLatency)]
triangleInequalityCheck mls = do
  let ls = Map.toList mls
  l1@((s :<- t), st) <- ls
  l2@((s' :<- middle), sm) <- ls
  guard (s' == s)
  Just mt <- pure $ Map.lookup (middle :<- t) mls
  let l3 = ((middle :<- t), mt)
  guard (st > (sm + mt))
  return (l1, l2, l3)

--------------------------------------------------------------------------------
-- Topology generation
--------------------------------------------------------------------------------

data PickLinksCloseAndRandomOptions = PickLinksCloseAndRandomOptions
  { world :: !World
  , numNodes :: !Int
  , numCloseLinksPerNode :: !Int
  , numRandomLinksPerNode :: !Int
  }
  deriving (Eq, Show, Generic)

instance Default PickLinksCloseAndRandomOptions where
  def =
    PickLinksCloseAndRandomOptions
      { world = def
      , numNodes = 10
      , numCloseLinksPerNode = 5
      , numRandomLinksPerNode = 5
      }

data TopologyGenerationStrategy
  = PickLinksCloseAndRandom !PickLinksCloseAndRandomOptions
  deriving (Eq, Show, Generic)

instance Default TopologyGenerationStrategy where
  def = PickLinksCloseAndRandom def

generateTopology :: RandomGen g => g -> TopologyGenerationStrategy -> IO P2PNetwork
generateTopology rng0 = \case
  PickLinksCloseAndRandom PickLinksCloseAndRandomOptions{..} -> do
    let p2pTopographyCharacteristics = P2PTopographyCharacteristics world numNodes numCloseLinksPerNode numRandomLinksPerNode
    let p2pTopography = genArbitraryP2PTopography p2pTopographyCharacteristics rng0
    let p2pNetwork = topologyToNetwork p2pTopography
    pure p2pNetwork

instance ToJSON TopologyGenerationStrategy where
  toJSON :: TopologyGenerationStrategy -> Value
  toJSON (PickLinksCloseAndRandom PickLinksCloseAndRandomOptions{..}) =
    object
      [ "world" .= world
      , "num_nodes" .= numNodes
      , "num_close_links_per_node" .= numCloseLinksPerNode
      , "num_random_links_per_node" .= numRandomLinksPerNode
      ]

instance FromJSON TopologyGenerationStrategy where
  parseJSON :: Value -> Parser TopologyGenerationStrategy
  parseJSON = withObject "PickLinksCloseAndRandom" $ \o -> do
    world <- o .:? "world" .!= def
    numNodes <- o .:? "num_nodes" .!= 100
    numCloseLinksPerNode <- o .:? "num_close_links_per_node" .!= 5
    numRandomLinksPerNode <- o .:? "num_random_links_per_node" .!= 5
    pure $ PickLinksCloseAndRandom PickLinksCloseAndRandomOptions{..}
