{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}

module Leios.Tracing.Cpu (
  cpu,
) where

import Control.Concurrent.Chan (Chan, readChan)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (StateT, execStateT, modify')
import Data.Aeson (FromJSON (..), Value (Object), withObject, (.:))
import Data.Aeson.Types (Parser, parseMaybe)
import Data.Function (on)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Monoid (Sum (..))
import Data.Text (Text)

import qualified Data.Map.Strict as M (insertWith, toList)
import qualified Data.Text as T (unpack)

newtype Earliest a = Earliest {getEarliest :: Maybe a}
  deriving (Show)

instance Eq a => Eq (Earliest a) where
  Earliest (Just x) == Earliest (Just y) = x == y
  Earliest Nothing == Earliest Nothing = True
  _ == _ = False

instance Ord a => Ord (Earliest a) where
  Earliest (Just x) `compare` Earliest (Just y) = x `compare` y
  Earliest (Just _) `compare` Earliest Nothing = LT
  Earliest Nothing `compare` Earliest (Just _) = GT
  Earliest Nothing `compare` Earliest Nothing = EQ

instance Ord a => Semigroup (Earliest a) where
  x <> y = if x < y then x else y

instance Ord a => Monoid (Earliest a) where
  mempty = Earliest Nothing

instance FromJSON a => FromJSON (Earliest a) where
  parseJSON = fmap Earliest . parseJSON

data ItemKey
  = ItemKey
  { slot :: Int
  , node :: Text
  , task :: Text
  }
  deriving (Eq, Ord, Show)

newtype ItemInfo = ItemInfo { duration :: Sum Double }
  deriving (Show)

instance Semigroup ItemInfo where
  x <> y =
    ItemInfo
      { duration = on (<>) duration x y
      }

instance Monoid ItemInfo where
  mempty =
    ItemInfo
      { duration = mempty
      }

toCSV :: ItemKey -> ItemInfo -> String
toCSV ItemKey{..} ItemInfo{..} =
  intercalate
    sep
    [ show slot
    , T.unpack node
    , T.unpack task
    , show $ getSum duration
    ]

itemHeader :: String
itemHeader =
  intercalate
    sep
    [ "Slot"
    , "Node"
    , "Task"
    , "Duration [s]"
    ]

sep :: String
sep = ","

parseEvent :: Value -> Parser (ItemKey, ItemInfo)
parseEvent =
  withObject "TraceEvent" $ \event ->
    do
      time <- event .: "time_s"
      message <- event .: "message"
      typ <- message .: "type"
      parseMessage typ time $ Object message

parseMessage :: Text -> Double -> Value -> Parser (ItemKey, ItemInfo)
parseMessage "Cpu" created =
  withObject "Cpu" $ \message ->
    do
      let slot = floor created
      node <- message .: "node"
      task <- message .: "task_type"
      duration <- message .: "cpu_time_s"
      pure (ItemKey{..}, mempty{duration})
parseMessage _ _ =
  const $ fail "Ignore"

type Index = Map ItemKey ItemInfo

tally :: Monad m => Value -> StateT Index m ()
tally event =
  case parseMaybe parseEvent event of
    Just (itemKey, itemInfo) ->
      do
        -- Insert the generated items.
        modify' $ M.insertWith (<>) itemKey itemInfo
    Nothing -> pure ()

cpu :: FilePath -> Chan (Maybe Value) -> IO ()
cpu lifecycleFile events =
  do
    let
      go =
        do
          liftIO (readChan events) >>=
            \case
              Nothing -> pure ()
              Just event -> tally event >> go
    index <-
      (`execStateT` mempty) $
        do
          go
    writeFile lifecycleFile . unlines . (itemHeader :) $
      uncurry toCSV <$> M.toList index
