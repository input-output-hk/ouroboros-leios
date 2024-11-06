{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Topology where

import Data.Aeson.Types (FromJSON (..), Options (..), ToJSON (..), defaultOptions, genericParseJSON, genericToEncoding)
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Generics (Generic)

newtype NodeName = NodeName Text
  deriving (Show, Eq, Ord)
  deriving newtype (FromJSON, ToJSON)

newtype NodeId = NodeId Int
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

newtype Nodes = Nodes
  { coreNodes :: Vector Node
  }
  deriving (Show, Generic)

instance ToJSON Nodes where
  toEncoding =
    genericToEncoding
      defaultOptions
        { unwrapUnaryRecords = False
        }

instance FromJSON Nodes where
  parseJSON =
    genericParseJSON
      defaultOptions
        { unwrapUnaryRecords = False
        }
