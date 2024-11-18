{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Topology where

import Control.Monad (void)
import Data.Aeson (decode)
import Data.Aeson.Types (FromJSON (..), Options (..), ToJSON (..), defaultOptions, genericParseJSON, genericToEncoding)
import qualified Data.ByteString.Lazy as BSL (readFile)
import Data.GraphViz (X11Color (..))
import qualified Data.GraphViz.Attributes as GVA
import qualified Data.GraphViz.Commands as GVC
import qualified Data.GraphViz.Types as GV (PrintDot)
import qualified Data.GraphViz.Types.Graph as G
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word (Word16)
import GHC.Generics (Generic)

newtype NodeName = NodeName Text
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)
  deriving newtype (GV.PrintDot)

newtype NodeId = NodeId Word16
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

newtype OrgName = OrgName Text
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

newtype RegionName = RegionName Text
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

regionNameToGraphID :: RegionName -> G.GraphID
regionNameToGraphID (RegionName regionName) =
  G.Str (TL.fromStrict regionName)

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

toDotGraph :: Topology -> G.DotGraph NodeName
toDotGraph topology = addEdges . addNodes $ G.emptyGraph
 where
  -- NOTE: Visualising regions as clusters looks AWFUL.
  -- addRegions =
  --   foldr (.) id $
  --     [ G.addCluster
  --       (regionNameToGraphID regionName)
  --       Nothing -- the parent cluster is the root graph
  --       [] -- no attributes
  --     | regionName <- S.toList (regions topology)
  --     ]
  regionColorMap =
    M.fromList $ zip (S.toList $ regions topology) simpleDistinctColors

  addNodes =
    foldr (.) id $
      [ G.addNode
        (name node)
        -- For regions as clusters, replace Nothing with the following:
        -- (Just $ regionNameToGraphID $ region node)
        Nothing
        [ GVA.style GVA.filled
        , GVA.fillColor (regionColorMap M.! region node)
        ]
      | node <- V.toList (coreNodes topology)
      ]
  addEdges =
    foldr (.) id $
      [ G.addEdge
        producer
        (name consumer)
        []
      | consumer <- V.toList (coreNodes topology)
      , producer <- V.toList (producers consumer)
      ]

renderTopology :: Topology -> FilePath -> IO ()
renderTopology topology outputFile =
  void $ GVC.runGraphviz (toDotGraph topology) GVC.Png outputFile
