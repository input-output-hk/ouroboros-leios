{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module SimTypes where

import Data.Aeson.Types (FromJSON (..), FromJSONKey, KeyValue ((.=)), ToJSON (..), ToJSONKey, Value (..), defaultOptions, genericToEncoding, object, typeMismatch, withObject, (.!=), (.:), (.:?))
import Data.Default (Default (..))
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

instance Default WorldShape where
  def = Rectangle

instance ToJSON WorldShape where
  toJSON = \case
    Rectangle -> String "rectangle"
    Cylinder -> String "cylinder"

instance FromJSON WorldShape where
  parseJSON (String txt)
    | txt == "rectangle" = pure Rectangle
    | txt == "cylinder" = pure Cylinder
  parseJSON value = typeMismatch "WorldShape" value

data World = World
  { worldDimensions :: !WorldDimensions
  , worldShape :: !WorldShape
  }
  deriving (Eq, Show, Generic)

instance Default World where
  def = World (0.6, 0.3) Rectangle

instance ToJSON World where
  toJSON World{..} =
    object
      [ "dimensions" .= worldDimensions
      , "shape" .= worldShape
      ]

instance FromJSON World where
  parseJSON = withObject "Word" $ \o -> do
    worldDimensions <- o .: "dimensions"
    worldShape <- o .:? "shape" .!= Rectangle
    pure World{..}
