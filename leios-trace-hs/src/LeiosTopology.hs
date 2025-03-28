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

module LeiosTopology where

import Data.Aeson (withObject)
import qualified Data.Aeson as Json
import qualified Data.Aeson.KeyMap as KeyMap
import Data.Aeson.Types (Encoding, FromJSON (..), FromJSONKey, KeyValue ((.=)), Options (..), Parser, ToJSON (..), ToJSONKey, Value (..), defaultOptions, genericParseJSON, object, pairs, typeMismatch, (.:))
import Data.Coerce (Coercible, coerce)
import Data.Default (Default (..))
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import JSONCompat (Getter, always, get, omitDefault, parseField, parseFieldOrDefault)
import LeiosTypes (Point (..))
import Text.Printf (PrintfArg)

--------------------------------------------------------------------------------
-- Node Properties
--------------------------------------------------------------------------------

newtype NodeName = NodeName {unNodeName :: Text}
  deriving newtype (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON, FromJSONKey, ToJSONKey)
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
