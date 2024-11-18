{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Topology where

import Control.Monad (void)
import Data.Aeson (decode)
import Data.Aeson.Types (FromJSON (..), Options (..), ToJSON (..), defaultOptions, genericParseJSON, genericToEncoding)
import qualified Data.ByteString.Lazy as BSL (readFile)
import Data.GraphViz (X11Color (..))
import qualified Data.GraphViz.Attributes as G
import qualified Data.GraphViz.Attributes.Complete as G
import qualified Data.GraphViz.Commands as G
import qualified Data.GraphViz.Types as G (PrintDot)
import qualified Data.GraphViz.Types.Generalised as G
import qualified Data.Map as M
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import Data.Text.Lazy (LazyText)
import qualified Data.Text.Lazy as TL
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word (Word16)
import GHC.Generics (Generic)

newtype NodeName = NodeName {unNodeName :: Text}
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)
  deriving newtype (G.PrintDot)

newtype NodeId = NodeId {unNodeId :: Word16}
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

newtype OrgName = OrgName {unOrgName :: Text}
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

newtype RegionName = RegionName {unRegionName :: Text}
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

data Node
  = Node
  { name :: !NodeName
  , nodeId :: !NodeId
  , org :: !OrgName
  , pools :: !(Maybe Int)
  , producers :: !(Vector NodeName)
  , region :: !RegionName
  , stakePool :: !Bool
  }
  deriving (Show, Generic)

instance ToJSON Node where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON Node

newtype Topology = Topology
  { coreNodes :: Vector Node
  }
  deriving (Show, Generic)

instance ToJSON Topology where
  toEncoding =
    genericToEncoding
      defaultOptions
        { unwrapUnaryRecords = False
        }

instance FromJSON Topology where
  parseJSON =
    genericParseJSON
      defaultOptions
        { unwrapUnaryRecords = False
        }

readTopology :: FilePath -> IO (Maybe Topology)
readTopology = fmap decode . BSL.readFile

regions :: Topology -> Set RegionName
regions = foldr (S.insert . region) S.empty . coreNodes

regionNameToLazyText :: RegionName -> LazyText
regionNameToLazyText = TL.fromStrict . unRegionName

regionNameToGraphID :: RegionName -> G.GraphID
regionNameToGraphID = G.Str . regionNameToLazyText

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

toDotGraphAsTorus :: Topology -> G.DotGraph NodeName
toDotGraphAsTorus topology =
  G.DotGraph True True Nothing . Seq.fromList $
    globalStatements : nodeStatements <> edgeStatements
 where
  globalStatements =
    G.GA . G.GraphAttrs $
      [ G.Smoothing G.Spring
      , G.K 0.5
      , G.RepulsiveForce 2.0
      ]
  nodeStatements =
    [ G.DN . G.DotNode nodeName $
      [ G.style G.filled
      , G.fillColor nodeRegionColor
      ]
    | node <- V.toList $ coreNodes topology
    , let nodeName = name node
    , let nodeRegionColor = regionColorMap M.! region node
    ]
  edgeStatements =
    [ G.DE . G.DotEdge producerName consumerName $
      [ G.fillColor producerRegionColor
      ]
    | consumer <- V.toList (coreNodes topology)
    , let consumerName = name consumer
    , producerName <- V.toList (producers consumer)
    , let producerRegionColor = regionColorMap M.! (nodeRegionMap M.! producerName)
    ]
  nodeRegionMap =
    M.fromList [(name node, region node) | node <- V.toList (coreNodes topology)]
  regionColorMap =
    M.fromList $ zip (S.toList $ regions topology) simpleDistinctColors

toDotGraphByRegion :: Topology -> G.DotGraph NodeName
toDotGraphByRegion topology =
  G.DotGraph True True Nothing . Seq.fromList $
    graphAttributes : subGraphStatements <> edgeStatements
 where
  graphAttributes =
    G.GA . G.GraphAttrs $
      []
  subGraphStatements =
    [ G.SG . G.DotSG True (Just subGraphId) . Seq.fromList $
      subGraphAttributtes : subGraphNodeStatements <> subGraphEdgeStatements
    | regionName <- S.toList $ regions topology
    , let subGraphId = regionNameToGraphID regionName
    , let subGraphAttributtes =
            G.GA . G.GraphAttrs $
              [ G.textLabel (regionNameToLazyText regionName)
              ]
    , let subGraphNodeStatements =
            [ G.DN . G.DotNode nodeName $
              [ G.style G.filled
              , G.fillColor nodeRegionColor
              ]
            | node <- V.toList $ coreNodes topology
            , let nodeName = name node
            , let nodeRegionName = region node
            , nodeRegionName == regionName
            , let nodeRegionColor = regionColorMap M.! nodeRegionName
            ]
    , let subGraphEdgeStatements =
            [ G.DE . G.DotEdge producerName consumerName $
              [ G.fillColor producerRegionColor
              ]
            | consumer <- V.toList (coreNodes topology)
            , let consumerName = name consumer
            , let consumerRegionName = region consumer
            , consumerRegionName == regionName
            , producerName <- V.toList (producers consumer)
            , let producerRegionName = nodeRegionMap M.! producerName
            , producerRegionName == regionName
            , let producerRegionColor = regionColorMap M.! producerRegionName
            ]
    ]
  edgeStatements =
    [ G.DE . G.DotEdge producerName consumerName $
      [ G.fillColor producerRegionColor
      ]
    | consumer <- V.toList (coreNodes topology)
    , let consumerName = name consumer
    , let consumerRegionName = region consumer
    , producerName <- V.toList (producers consumer)
    , let producerRegionName = nodeRegionMap M.! producerName
    , let producerRegionColor = regionColorMap M.! producerRegionName
    , consumerRegionName /= producerRegionName
    ]
  nodeRegionMap =
    M.fromList [(name node, region node) | node <- V.toList (coreNodes topology)]
  regionColorMap =
    M.fromList $ zip (S.toList $ regions topology) simpleDistinctColors

renderTopologyAsTorus :: FilePath -> Topology -> IO ()
renderTopologyAsTorus outputFile topology =
  void $ G.runGraphvizCommand G.Sfdp (toDotGraphAsTorus topology) G.Png outputFile

renderTopologyFileAsTorus :: FilePath -> FilePath -> IO ()
renderTopologyFileAsTorus topologyFile outputFile =
  readTopology topologyFile
    >>= maybe
      (error $ "Could not read " <> topologyFile)
      (renderTopologyAsTorus outputFile)

renderTopologyByRegion :: FilePath -> Topology -> IO ()
renderTopologyByRegion outputFile topology =
  void $ G.runGraphvizCommand G.Dot (toDotGraphByRegion topology) G.Png outputFile

renderTopologyFileByRegion :: FilePath -> FilePath -> IO ()
renderTopologyFileByRegion topologyFile outputFile =
  readTopology topologyFile
    >>= maybe
      (error $ "Could not read " <> topologyFile)
      (renderTopologyByRegion outputFile)
