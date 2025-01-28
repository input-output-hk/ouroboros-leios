{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
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

module Topology where

import Codec.Compression.GZip as GZip (decompress)
import Control.Arrow (Arrow ((&&&)), second)
import Control.Exception (Exception (displayException), assert)
import Control.Monad (forM_, guard, (<=<))
import Data.Aeson (withObject)
import qualified Data.Aeson as Json
import qualified Data.Aeson.KeyMap as KeyMap
import Data.Aeson.Types (Encoding, FromJSON (..), FromJSONKey, KeyValue ((.=)), Options (..), Parser, ToJSON (..), ToJSONKey, Value (..), defaultOptions, genericParseJSON, genericToEncoding, object, pairs, typeMismatch, (.:))
import qualified Data.ByteString.Lazy as BSL
import Data.Coerce (Coercible, coerce)
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
import Data.Maybe (catMaybes, fromMaybe, mapMaybe, maybeToList)
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
import JSONCompat (Getter, always, get, omitDefault, parseField, parseFieldOrDefault)
import ModelTCP (Bytes)
import P2P (Latency, P2PTopography (..))
import SimTypes (NodeId (..), NumCores (..), Path (..), Point (..), StakeFraction (StakeFraction), World (..), WorldDimensions)
import System.Exit (exitFailure)
import System.FilePath (dropExtension, takeDirectory, takeExtension, takeExtensions, takeFileName)
import System.IO (hClose, hPutStrLn, stderr)
import System.IO.Temp (withTempFile)
import Text.Printf (PrintfArg, printf)

--------------------------------------------------------------------------------
-- Node Properties
--------------------------------------------------------------------------------

newtype NodeName = NodeName {unNodeName :: Text}
  deriving newtype (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON, FromJSONKey, ToJSONKey)
  deriving newtype (GVT.PrintDot)
  deriving newtype (SQLite.ToField)
  deriving newtype (PrintfArg)

-- | A cluster name.
newtype ClusterName = ClusterName {unClusterName :: Text}
  deriving stock (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

-- | Connection bandwidth, measured in bytes per second.
newtype BandwidthBps = BandwidthBps {unBandwidthBps :: Maybe Word}
  deriving newtype (Show, Eq, Ord, FromJSON, ToJSON)

instance Default BandwidthBps where
  def = Unbounded

-- | The number of CPU cores.
newtype CpuCoreCount = CpuCoreCount {unCpuCoreCount :: Maybe Word}
  deriving newtype (Show, Eq, Ord, FromJSON, ToJSON)

instance Default CpuCoreCount where
  def = Unbounded

-- | Connection latency, measured in milliseconds per trip.
newtype LatencyMs = LatencyMs {unLatencyMs :: Double}
  deriving newtype (Show, Eq, Ord, FromJSON, ToJSON, Num, Real, RealFrac, Fractional)

pattern Unbounded :: forall a. Coercible a (Maybe Word) => a
pattern Unbounded <- (coerce @a @(Maybe Word) -> Nothing)
  where
    Unbounded = coerce @(Maybe Word) @a Nothing
{-# INLINE Unbounded #-}

pattern Bounded :: forall a. Coercible a (Maybe Word) => Word -> a
pattern Bounded w <- (coerce @a @(Maybe Word) -> Just w)
  where
    Bounded w = coerce @(Maybe Word) @a (Just w)
{-# INLINE Bounded #-}

{-# COMPLETE Unbounded, Bounded #-}

--------------------------------------------------------------------------------
-- Location
--------------------------------------------------------------------------------

data LocationKind = CLUSTER | COORD2D

data Location (lk :: LocationKind) where
  LocCluster :: {clusterName :: {-# UNPACK #-} !(Maybe ClusterName)} -> Location CLUSTER
  LocCoord2D :: {coord2D :: {-# UNPACK #-} !Point} -> Location COORD2D

deriving instance Show (Location lk)
deriving instance Eq (Location lk)

instance ToJSON (Location lk) where
  toJSON :: Location lk -> Value
  toJSON (LocCluster clusterName) = object ["cluster" .= clusterName]
  toJSON (LocCoord2D coord2d) = toJSON [coord2d._1, coord2d._2]

  toEncoding :: Location lk -> Encoding
  toEncoding (LocCluster clusterName) = pairs ("cluster" .= clusterName)
  toEncoding (LocCoord2D coord2d) = toEncoding [coord2d._1, coord2d._2]

instance FromJSON (Location 'CLUSTER) where
  parseJSON :: Value -> Parser (Location 'CLUSTER)
  parseJSON = withObject "Cluster" $ \o -> do
    clusterName <- o .: "cluster"
    pure $ LocCluster clusterName

instance FromJSON (Location 'COORD2D) where
  parseJSON :: Value -> Parser (Location 'COORD2D)
  parseJSON (Array (V.toList -> [x, y])) =
    LocCoord2D <$> (Point <$> parseJSON x <*> parseJSON y)
  parseJSON value = typeMismatch "Coord2D" value

--------------------------------------------------------------------------------
-- Topology
--
-- As provided in 'data/simulation/topology-dense-52.json'.
--------------------------------------------------------------------------------

data SLocationKind (lk :: LocationKind) where
  SCLUSTER :: SLocationKind 'CLUSTER
  SCOORD2D :: SLocationKind 'COORD2D

data SomeTopology = forall lk. SomeTopology (SLocationKind lk) (Topology lk)

instance ToJSON SomeTopology where
  toJSON :: SomeTopology -> Value
  toJSON (SomeTopology SCLUSTER clusterTopology) = toJSON clusterTopology
  toJSON (SomeTopology SCOORD2D coord2DTopology) = toJSON coord2DTopology

  toEncoding :: SomeTopology -> Encoding
  toEncoding (SomeTopology SCLUSTER clusterTopology) = toEncoding clusterTopology
  toEncoding (SomeTopology SCOORD2D coord2DTopology) = toEncoding coord2DTopology

instance FromJSON SomeTopology where
  parseJSON :: Value -> Parser SomeTopology
  parseJSON v =
    if isTopologyCoord2D v
      then SomeTopology SCOORD2D <$> parseJSON v
      else SomeTopology SCLUSTER <$> parseJSON v

isTopologyCoord2D :: Value -> Bool
isTopologyCoord2D v =
  case v of
    Object o ->
      case KeyMap.lookup "nodes" o of
        Just (Object nodes) ->
          case KeyMap.elems nodes of
            (Object node : _nodes) ->
              case KeyMap.lookup "location" node of
                Just loc
                  | Json.Success{} <- Json.fromJSON @(Location 'COORD2D) loc ->
                      True
                Just loc
                  | Json.Success{} <- Json.fromJSON @(Location 'CLUSTER) loc ->
                      False
                _otherwise ->
                  error "Unrecognized location"
            [] -> False
            _otherwise -> error "Unrecognized topology.nodes contents"
        _otherwise -> error "Unrecognized topology.nodes"
    _otherwise -> error "Unrecognized topology"

newtype Topology lk = Topology
  { nodes :: Map NodeName (Node lk)
  }
  deriving stock (Show, Eq, Generic)

instance HasField "stake" (Topology lk) Word where
  getField :: Topology lk -> Word
  getField topology = sum ((.stake) <$> M.elems topology.nodes)

data Node (lk :: LocationKind) = Node
  { nodeInfo :: !(NodeInfo lk)
  , producers :: !(Map NodeName LinkInfo)
  }
  deriving stock (Show, Eq, Generic)

instance HasField "stake" (Node lk) Word where
  getField :: Node lk -> Word
  getField node = node.nodeInfo.stake

instance HasField "cpuCoreCount" (Node lk) CpuCoreCount where
  getField :: Node lk -> CpuCoreCount
  getField node = node.nodeInfo.cpuCoreCount

instance HasField "location" (Node lk) (Location lk) where
  getField :: Node lk -> Location lk
  getField node = node.nodeInfo.location

instance HasField "coord2D" (Node 'COORD2D) Point where
  getField :: Node 'COORD2D -> Point
  getField node = node.nodeInfo.location.coord2D

instance Default (Node 'CLUSTER) where
  def :: Node 'CLUSTER
  def = Node{nodeInfo = def, producers = mempty}

data NodeInfo (lk :: LocationKind) = NodeInfo
  { stake :: {-# UNPACK #-} !Word
  , cpuCoreCount :: {-# UNPACK #-} !CpuCoreCount
  , location :: !(Location lk)
  }
  deriving stock (Show, Eq, Generic)

instance HasField "coord2D" (NodeInfo 'COORD2D) Point where
  getField :: NodeInfo 'COORD2D -> Point
  getField nodeInfo = nodeInfo.location.coord2D

instance Default (NodeInfo 'CLUSTER) where
  def :: NodeInfo 'CLUSTER
  def =
    NodeInfo
      { stake = 0
      , cpuCoreCount = Unbounded
      , location = LocCluster Nothing
      }

data LinkInfo = LinkInfo
  { latencyMs :: !LatencyMs
  , bandwidthBytesPerSecond :: !BandwidthBps
  }
  deriving stock (Show, Eq, Generic)

instance HasField "latencyS" LinkInfo Latency where
  getField :: LinkInfo -> Latency
  getField linkInfo = linkInfo.latencyMs.unLatencyMs / 1000

instance Default LinkInfo where
  def :: LinkInfo
  def =
    LinkInfo
      { latencyMs = 0
      , bandwidthBytesPerSecond = Unbounded
      }

topologyOptions :: Options
topologyOptions = defaultOptions{unwrapUnaryRecords = False, omitNothingFields = True}

nodeToKVs :: (ToJSON (Location lk), KeyValue e kv) => Getter (Node lk) -> Node lk -> [kv]
nodeToKVs getter node =
  catMaybes
    [ get @"stake" getter node
    , get @"cpuCoreCount" getter node
    , get @"location" getter node
    , get @"producers" getter node
    ]

instance ToJSON (Node 'CLUSTER) where
  toJSON :: Node 'CLUSTER -> Value
  toJSON = object . nodeToKVs omitDefault

  toEncoding :: Node 'CLUSTER -> Encoding
  toEncoding = pairs . mconcat . nodeToKVs omitDefault

instance ToJSON (Node 'COORD2D) where
  toJSON :: Node 'COORD2D -> Value
  toJSON = object . nodeToKVs always

  toEncoding :: Node 'COORD2D -> Encoding
  toEncoding = pairs . mconcat . nodeToKVs always

instance FromJSON (Node 'CLUSTER) where
  parseJSON :: Value -> Parser (Node 'CLUSTER)
  parseJSON = withObject "Node" $ \obj -> do
    stake <- parseFieldOrDefault @(Node 'CLUSTER) @"stake" obj
    cpuCoreCount <- parseFieldOrDefault @(Node 'CLUSTER) @"cpuCoreCount" obj
    location <- parseFieldOrDefault @(Node 'CLUSTER) @"location" obj
    producers <- parseFieldOrDefault @(Node 'CLUSTER) @"producers" obj
    pure Node{nodeInfo = NodeInfo{..}, ..}

instance FromJSON (Node 'COORD2D) where
  parseJSON :: Value -> Parser (Node 'COORD2D)
  parseJSON = withObject "Node" $ \obj -> do
    -- NOTE: There is no default instance for @NodeInfo 'COORD2D@. Hence, this
    --       function uses the default instance for @NodeInfo 'CLUSTER@, which
    --       admittedly looks a bit shady.
    stake <- parseFieldOrDefault @(NodeInfo 'CLUSTER) @"stake" obj
    cpuCoreCount <- parseFieldOrDefault @(Node 'CLUSTER) @"cpuCoreCount" obj
    location <- parseField @(Node 'COORD2D) @"location" obj
    producers <- parseFieldOrDefault @(Node 'CLUSTER) @"producers" obj
    pure Node{nodeInfo = NodeInfo{..}, ..}

linkInfoToKVs :: KeyValue e kv => Getter LinkInfo -> LinkInfo -> [kv]
linkInfoToKVs getter link =
  catMaybes
    [ get @"latencyMs" getter link
    , get @"bandwidthBytesPerSecond" getter link
    ]

instance ToJSON LinkInfo where
  toJSON :: LinkInfo -> Value
  toJSON = object . linkInfoToKVs omitDefault

  toEncoding :: LinkInfo -> Encoding
  toEncoding = pairs . mconcat . linkInfoToKVs omitDefault

instance FromJSON LinkInfo where
  parseJSON :: Value -> Parser LinkInfo
  parseJSON = withObject "LinkInfo" $ \obj -> do
    latencyMs <- parseField @LinkInfo @"latencyMs" obj
    bandwidthBytesPerSecond <- parseFieldOrDefault @LinkInfo @"bandwidthBytesPerSecond" obj
    pure LinkInfo{..}

topologyToKVs :: (ToJSON (Node lk), KeyValue e kv) => Getter (Topology lk) -> Topology lk -> [kv]
topologyToKVs getter topology = catMaybes [get @"nodes" getter topology]

instance ToJSON (Topology 'CLUSTER) where
  toJSON :: Topology 'CLUSTER -> Value
  toJSON = object . topologyToKVs always

  toEncoding :: Topology 'CLUSTER -> Encoding
  toEncoding = pairs . mconcat . topologyToKVs always

instance ToJSON (Topology 'COORD2D) where
  toJSON :: Topology 'COORD2D -> Value
  toJSON = object . topologyToKVs always

  toEncoding :: Topology 'COORD2D -> Encoding
  toEncoding = pairs . mconcat . topologyToKVs always

instance FromJSON (Topology 'CLUSTER) where
  parseJSON :: Value -> Parser (Topology CLUSTER)
  parseJSON = genericParseJSON topologyOptions

instance FromJSON (Topology 'COORD2D) where
  parseJSON :: Value -> Parser (Topology COORD2D)
  parseJSON = genericParseJSON topologyOptions

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

-- | Convert 'Topology' to an FGL 'Gr'.
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
-- Conversion between FGL Graph and P2PTopography
--------------------------------------------------------------------------------

type BandwidthPerSecond = Bytes
data P2PNetwork = P2PNetwork
  { p2pNodes :: !(Map NodeId Point)
  , p2pNodeNames :: !(Map NodeId Text)
  , p2pNodeCores :: !(Map NodeId NumCores)
  , p2pNodeStakes :: !(Map NodeId StakeFraction)
  , p2pLinks :: !(Map (NodeId, NodeId) (Latency, Maybe Bytes))
  , p2pWorld :: !World
  }
  deriving (Eq, Show, Generic)

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
      [ ((NodeId grNode1, NodeId grNode2), latency)
      | (grNode1, grNode2, latency) <- G.labEdges gr
      ]
  p2pNodes = Map.map ((.coord2D) . snd) nodeInfoMap
  p2pNodeNames = Map.map (coerce . fst) nodeInfoMap
  p2pNodeCores = flip Map.map nodeInfoMap $ maybe Infinite (Finite . fromIntegral) . unCpuCoreCount . (.cpuCoreCount) . snd
  p2pNodeStakes = flip Map.map nodeInfoMap $ StakeFraction . (/ totalStake) . fromIntegral . (.stake) . snd
  totalStake = fromIntegral . sum $ map (fromIntegral @_ @Integer . (.stake) . snd) $ Map.elems nodeInfoMap
  p2pLinks = flip Map.map edgeInfoMap $ \link ->
    (link.latencyS, fromIntegral <$> unBandwidthBps link.bandwidthBytesPerSecond)

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
    ]
  grLinks =
    [ (coerce n, coerce m, linkInfo)
    | ((n, m), (latency, bw)) <- M.toList p2pLinks
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

topologyToNetwork :: Maybe Bytes -> P2PTopography -> P2PNetwork
topologyToNetwork bw P2PTopography{..} = P2PNetwork{p2pLinks = Map.map (,bw) p2pLinks, ..}
 where
  p2pNodeNames = Map.mapWithKey (\(NodeId n) _ -> T.pack $ "node-" ++ show n) p2pNodes
  p2pNodeCores = Map.map (const Infinite) p2pNodes
  p2pNodeStakes = Map.map (const $ StakeFraction $ 1 / numNodes) p2pNodes
  numNodes = fromIntegral $ Map.size p2pNodes

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
    [ (grNode1, grNode2, latencyInSeconds)
    | ((NodeId grNode1, NodeId grNode2), latencyInSeconds) <- M.assocs p2pLinks
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

type LinkLatency = ((NodeId, NodeId), Latency)

-- | Returns nodes failing the expected triangle inequality for latencies.
triangleInequalityCheck :: Map (NodeId, NodeId) Latency -> [(LinkLatency, LinkLatency, LinkLatency)]
triangleInequalityCheck mls = do
  let ls = Map.toList mls
  l1@((s, t), st) <- ls
  l2@((s', middle), sm) <- ls
  guard (s' == s)
  Just mt <- pure $ Map.lookup (middle, t) mls
  let l3 = ((middle, t), mt)
  guard (st > (sm + mt))
  return (l1, l2, l3)
