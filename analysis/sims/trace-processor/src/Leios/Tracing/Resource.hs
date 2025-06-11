{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}

module Leios.Tracing.Resource (
  resource,
) where

import Control.Concurrent.Chan (Chan, readChan)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (StateT, execStateT, modify')
import Data.Aeson (Value (Object), withObject, (.:))
import Data.Aeson.Types (Parser, parseMaybe)
import Data.Function (on)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Monoid (Sum (..))
import Data.Text (Text)
import Leios.Tracing.Util (Maximum (..))

import qualified Data.Map.Strict as M (insertWith, map, mapKeysWith, toList)
import qualified Data.Text as T (unpack)

data ItemKey'
  = ItemKey'
  { slot' :: Int
  , node' :: Text
  }
  deriving (Eq, Ord, Show)

data ItemInfo'
  = ItemInfo'
  { egress' :: Sum Double
  , disk' :: Sum Double
  , cpu' :: Sum Double
  }
  deriving (Show)

instance Semigroup ItemInfo' where
  x <> y =
    ItemInfo'
      { egress' = on (<>) egress' x y
      , disk' = on (<>) disk' x y
      , cpu' = on (<>) cpu' x y
      }

instance Monoid ItemInfo' where
  mempty =
    ItemInfo'
      { egress' = mempty
      , disk' = mempty
      , cpu' = mempty
      }

type Index' = Map ItemKey' ItemInfo'

newtype ItemKey
  = ItemKey
  { node :: Text
  }
  deriving (Eq, Ord, Show)

data ItemInfo
  = ItemInfo
  { egress :: Sum Double
  , disk :: Sum Double
  , totalCpu :: Sum Double
  , maximumCpu :: Maximum Double
  }
  deriving (Show)

instance Semigroup ItemInfo where
  x <> y =
    ItemInfo
      { egress = on (<>) egress x y
      , disk = on (<>) disk x y
      , totalCpu = on (<>) totalCpu x y
      , maximumCpu = on (<>) maximumCpu x y
      }

instance Monoid ItemInfo where
  mempty =
    ItemInfo
      { egress = mempty
      , disk = mempty
      , totalCpu = mempty
      , maximumCpu = mempty
      }

toCSV :: ItemKey -> ItemInfo -> String
toCSV ItemKey{..} ItemInfo{..} =
  intercalate
    sep
    [ T.unpack node
    , show $ getSum egress
    , show $ getSum disk
    , show $ getSum totalCpu
    , show maximumCpu
    ]

itemHeader :: String
itemHeader =
  intercalate
    sep
    [ "Node"
    , "Egress [B]"
    , "Disk [B]"
    , "Total CPU [s]"
    , "Maximmum CPU [s/s]"
    ]

sep :: String
sep = ","

parseEvent :: Value -> Parser (ItemKey', ItemInfo')
parseEvent =
  withObject "TraceEvent" $ \event ->
    do
      time <- event .: "time_s"
      message <- event .: "message"
      typ <- message .: "type"
      parseMessage typ time $ Object message

parseMessage :: Text -> Double -> Value -> Parser (ItemKey', ItemInfo')
parseMessage "TXSent" created =
  withObject "TXSent" $ \message ->
    do
      let slot' = floor created
      node' <- message .: "sender"
      egress' <- message .: "msg_size_bytes"
      pure (ItemKey'{..}, mempty{egress'})
parseMessage "IBSent" created =
  withObject "IBSent" $ \message ->
    do
      let slot' = floor created
      node' <- message .: "sender"
      egress' <- message .: "msg_size_bytes"
      pure (ItemKey'{..}, mempty{egress'})
parseMessage "EBSent" created =
  withObject "EBSent" $ \message ->
    do
      let slot' = floor created
      node' <- message .: "sender"
      egress' <- message .: "size_bytes"
      pure (ItemKey'{..}, mempty{egress'})
parseMessage "RBSent" created =
  withObject "RBSent" $ \message ->
    do
      let slot' = floor created
      node' <- message .: "sender"
      egress' <- message .: "msg_size_bytes"
      pure (ItemKey'{..}, mempty{egress'})
parseMessage "VTBundleSent" created =
  withObject "VTBundleSent" $ \message ->
    do
      let slot' = floor created
      node' <- message .: "sender"
      egress' <- message .: "msg_size_bytes"
      pure (ItemKey'{..}, mempty{egress'})
parseMessage "IBGenerated" created =
  withObject "IBGenerated" $ \message ->
    do
      let slot' = floor created
      node' <- message .: "producer"
      disk' <- message .: "size_bytes"
      pure (ItemKey'{..}, mempty{disk'})
parseMessage "EBGenerated" created =
  withObject "EBGenerated" $ \message ->
    do
      let slot' = floor created
      node' <- message .: "producer"
      disk' <- message .: "size_bytes"
      pure (ItemKey'{..}, mempty{disk'})
parseMessage "RBGenerated" created =
  withObject "RBGenerated" $ \message ->
    do
      let slot' = floor created
      node' <- message .: "producer"
      disk' <- message .: "size_bytes"
      pure (ItemKey'{..}, mempty{disk'})
parseMessage "Cpu" created =
  withObject "Cpu" $ \message ->
    do
      let slot' = floor created
      node' <- message .: "node"
      cpu' <- message .: "cpu_time_s"
      pure (ItemKey'{..}, mempty{cpu'})
parseMessage _ _ =
  const $ fail "Ignore"

tally :: Monad m => Value -> StateT Index' m ()
tally event =
  case parseMaybe parseEvent event of
    Just (itemKey, itemInfo) ->
      do
        -- Insert the generated items.
        modify' $ M.insertWith (<>) itemKey itemInfo
    Nothing -> pure ()

resource :: FilePath -> Chan (Maybe Value) -> IO ()
resource resourceFile events =
  do
    let
      go =
        do
          liftIO (readChan events)
            >>= \case
              Nothing -> pure ()
              Just event -> tally event >> go
    index' <- go `execStateT` mempty
    let
      reKey :: ItemKey' -> ItemKey
      reKey ItemKey'{node'} = ItemKey{node = node'}
      reValue :: ItemInfo' -> ItemInfo
      reValue ItemInfo'{..} = ItemInfo{egress = egress', disk = disk', totalCpu = cpu', maximumCpu = Maximum . pure $ getSum cpu'}
      index = M.mapKeysWith (<>) reKey $ M.map reValue index'
    writeFile resourceFile . unlines . (itemHeader :) $
      uncurry toCSV <$> M.toList index
