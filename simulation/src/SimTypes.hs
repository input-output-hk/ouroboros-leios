{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SimTypes where

import Data.Aeson.Types (FromJSON, FromJSONKey, ToJSON (..), ToJSONKey, defaultOptions, genericToEncoding)
import Data.Hashable
import Data.Ix (Ix)
import Data.Text (Text)
import GHC.Generics (Generic)
import TimeCompat

data CPUTask = CPUTask {cpuTaskDuration :: !DiffTime, cpuTaskLabel :: !Text}
  deriving (Eq, Ord, Show, Generic)
  deriving (ToJSON, FromJSON)

newtype NodeId = NodeId Int
  deriving (Eq, Ord, Ix, Show)
  deriving newtype (ToJSON, FromJSON, ToJSONKey, FromJSONKey, Hashable)

data LabelNode e = LabelNode NodeId e deriving (Show)

data LabelLink e = LabelLink NodeId NodeId e deriving (Show)

-- | Position in simulation world coordinates
data Point = Point {_1 :: !Double, _2 :: !Double}
  deriving (Eq, Show, Generic)

-- | Path in simulation world
newtype Path = Path [Point]
  deriving (Eq, Show, Generic)
  deriving newtype (Semigroup, Monoid)

instance ToJSON Point where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON Point

type WorldDimensions = (Double, Double)

-- | If the world is a cylinder, and so wraps around from the East edge
-- to the West edge, or if the world is a rectangle, with no wrapping at
-- the edges. This affects the latencies.
data WorldShape
  = Rectangle
  | Cylinder
  deriving (Eq, Show, Generic, Bounded, Enum)

instance ToJSON WorldShape where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON WorldShape

data World = World
  { worldDimensions :: !WorldDimensions
  , worldShape :: !WorldShape
  }
  deriving (Eq, Show, Generic)

instance ToJSON World where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON World
