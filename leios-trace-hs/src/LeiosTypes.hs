{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-}

module LeiosTypes where

import Data.Aeson
import Data.Aeson.Types
import qualified Data.Vector as V
import GHC.Generics (Generic)

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
