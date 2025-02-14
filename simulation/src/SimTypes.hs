{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module SimTypes where

import Data.Aeson.Types (FromJSON (..), FromJSONKey, KeyValue ((.=)), Parser, ToJSON (..), ToJSONKey, Value (..), object, typeMismatch, withObject, (.!=), (.:), (.:?))
import Data.Default (Default (..))
import Data.Hashable
import Data.Ix (Ix)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V
import GHC.Generics (Generic)
import GHC.Records
import TimeCompat

data CPUTask = CPUTask {cpuTaskDuration :: !DiffTime, cpuTaskLabel :: !Text}
  deriving (Eq, Ord, Show, Generic)
  deriving (ToJSON, FromJSON)

cpuTask :: HasField "stringId" t String => String -> (t -> DiffTime) -> t -> CPUTask
cpuTask prefix d x =
  let !delay = d x
      !label = T.pack $ prefix ++ ": " ++ x.stringId
   in CPUTask delay label

newtype NodeId = NodeId Int
  deriving (Eq, Ord, Ix, Show)
  deriving newtype (ToJSON, FromJSON, ToJSONKey, FromJSONKey, Hashable)

data LabelNode e = LabelNode NodeId e deriving (Show)

data LabelLink e = LabelLink NodeId NodeId e deriving (Show)

-- | Position in simulation world coordinates
data Point = Point {_1 :: !Double, _2 :: !Double}
  deriving (Eq, Show, Generic)

instance ToJSON Point where
  toJSON :: Point -> Value
  toJSON (Point x y) = toJSON [x, y]

instance FromJSON Point where
  parseJSON :: Value -> Parser Point
  parseJSON = withTuple "Point" $ \(x, y) ->
    Point <$> parseJSON x <*> parseJSON y
   where
    withTuple :: String -> ((Value, Value) -> Parser a) -> Value -> Parser a
    withTuple _expected k (toTuple -> Just xy) = k xy
    withTuple expected _k v = typeMismatch expected v

    toTuple :: Value -> Maybe (Value, Value)
    toTuple (Array v) | V.length v == 2 = Just (v V.! 0, v V.! 1)
    toTuple _ = Nothing

-- | Path in simulation world
newtype Path = Path [Point]
  deriving (Eq, Show, Generic)
  deriving newtype (Semigroup, Monoid)

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

newtype NetworkRate = NetworkRate Double
  deriving (Eq, Ord, Show)
  deriving newtype (ToJSON, FromJSON)
newtype NodeRate = NodeRate Double
  deriving (Eq, Ord, Show)
  deriving newtype (ToJSON, FromJSON)
newtype StakeFraction = StakeFraction Double
  deriving (Eq, Ord, Show)
  deriving newtype (ToJSON, FromJSON)
data NumCores = Infinite | Finite Int
  deriving (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

newtype Bytes = Bytes {fromBytes :: Int}
  deriving newtype (Eq, Ord, Enum, Num, Real, Integral, Show, Hashable, ToJSON, FromJSON)
