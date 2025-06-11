{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}

module Leios.Tracing.Receipt (
  receipt,
) where

import Control.Concurrent.Chan (Chan, readChan)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (StateT, execStateT, modify')
import Data.Aeson (Value (Object), withObject, (.:))
import Data.Aeson.Types (Parser, parseMaybe)
import Data.Function (on)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Text (Text)
import Leios.Tracing.Util (Maximum (..), Minimum (..))

import qualified Data.Map.Strict as M (insertWith, singleton, toAscList, toList)
import qualified Data.Text as T (unpack)

data ItemKey
  = ItemKey
  { kind :: Text
  , item :: Text
  , producer :: Text
  }
  deriving (Eq, Ord, Show)

data ItemInfo
  = ItemInfo
  { sent :: Minimum Double
  , size :: Maximum Double
  , receipts :: Map Text Double
  }
  deriving (Show)

instance Semigroup ItemInfo where
  x <> y =
    ItemInfo
      { sent = on (<>) sent x y
      , size = on (<>) size x y
      , receipts = on (<>) receipts x y
      }

instance Monoid ItemInfo where
  mempty =
    ItemInfo
      { sent = mempty
      , size = mempty
      , receipts = mempty
      }

toCSV :: ItemKey -> ItemInfo -> [String]
toCSV ItemKey{..} ItemInfo{..} =
  let
    common =
      [ T.unpack kind
      , T.unpack item
      , T.unpack producer
      , show sent
      ]
    receive :: Text -> Double -> String
    receive recipient received =
      intercalate sep $
        common
          ++ [ T.unpack recipient
             , show received
             , show $ (received -) <$> sent
             ]
   in
    uncurry receive <$> M.toAscList receipts

itemHeader :: String
itemHeader =
  intercalate
    sep
    [ "Kind"
    , "Item"
    , "Producer"
    , "Sent [s]"
    , "Recipient"
    , "Received [s]"
    , "Elapsed [s]"
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
      item <- message .: "id"
      parseMessage typ item time $ Object message

parseMessage :: Text -> Text -> Double -> Value -> Parser (ItemKey, ItemInfo)
parseMessage "TXGenerated" item sent =
  withObject "TXGenerated" $ \message ->
    do
      let kind = "TX"
      producer <- message .: "publisher"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{size, sent = Minimum $ Just sent})
parseMessage "IBGenerated" item sent =
  withObject "IBGenerated" $ \message ->
    do
      let kind = "IB"
      producer <- message .: "producer"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{size, sent = Minimum $ Just sent})
parseMessage "EBGenerated" item sent =
  withObject "EBGenerated" $ \message ->
    do
      let kind = "EB"
      producer <- message .: "producer"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{size, sent = Minimum $ Just sent})
parseMessage "RBGenerated" item sent =
  withObject "RBGenerated" $ \message ->
    do
      let kind = "RB"
      producer <- message .: "producer"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{size, sent = Minimum $ Just sent})
parseMessage "VTBundleGenerated" item sent =
  withObject "VTBundleGenerated" $ \message ->
    do
      let kind = "VT"
      producer <- message .: "producer"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{size, sent = Minimum $ Just sent})
parseMessage "TXReceived" item received =
  withObject "TXReceived" $ \message ->
    do
      let kind = "TX"
      producer <- message .: "producer"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty{receipts = M.singleton recipient received})
parseMessage "IBReceived" item received =
  withObject "IBReceived" $ \message ->
    do
      let kind = "IB"
      producer <- message .: "producer"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty{receipts = M.singleton recipient received})
parseMessage "EBReceived" item received =
  withObject "EBReceived" $ \message ->
    do
      let kind = "EB"
      producer <- message .: "producer"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty{receipts = M.singleton recipient received})
parseMessage "RBReceived" item received =
  withObject "RBReceived" $ \message ->
    do
      let kind = "RB"
      producer <- message .: "producer"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty{receipts = M.singleton recipient received})
parseMessage "VTBundleReceived" item received =
  withObject "VTBundleReceived" $ \message ->
    do
      let kind = "VT"
      producer <- message .: "producer"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty{receipts = M.singleton recipient received})
parseMessage _ _ _ =
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

receipt :: FilePath -> Chan (Maybe Value) -> IO ()
receipt cpuFile events =
  do
    let
      go =
        do
          liftIO (readChan events)
            >>= \case
              Nothing -> pure ()
              Just event -> tally event >> go
    index <- go `execStateT` mempty
    writeFile cpuFile . unlines . (itemHeader :) . concat $
      uncurry toCSV <$> M.toList index
