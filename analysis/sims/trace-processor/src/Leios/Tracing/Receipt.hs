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

import Control.Concurrent.MVar (MVar, takeMVar)
import Control.Monad (void)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (StateT, execStateT, gets, modify')
import Data.Aeson (Value (Object), withObject, (.:))
import Data.Aeson.Types (Parser, parseMaybe)
import Data.Function (on)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Text (Text)
import Leios.Tracing.Util (Maximum (..), Minimum (..))
import System.IO (IOMode (WriteMode), hClose, hPutStrLn, openFile)

import qualified Data.Map.Strict as M (insertWith, (!))
import qualified Data.Text as T (unpack)

data ItemKey
  = ItemKey
  { kind :: Text
  , item :: Text
  }
  deriving (Eq, Ord, Show)

data ItemInfo
  = ItemInfo
  { producer :: Text
  , sent :: Minimum Double
  , size :: Maximum Double
  }
  deriving (Show)

instance Semigroup ItemInfo where
  x <> y =
    ItemInfo
      { producer = on ((maximum .) . (. pure) . (:)) producer x y
      , sent = on (<>) sent x y
      , size = on (<>) size x y
      }

instance Monoid ItemInfo where
  mempty =
    ItemInfo
      { producer = mempty
      , sent = mempty
      , size = mempty
      }

toCSV :: ItemKey -> ItemInfo -> Text -> Double -> String
toCSV ItemKey{..} ItemInfo{..} recipient received =
  intercalate sep $
    [ T.unpack kind
    , T.unpack item
    , T.unpack producer
    , show sent
    , T.unpack recipient
    , show received
    , show $ (received -) <$> sent
    ]

itemHeader :: String
itemHeader =
  intercalate
    sep
    [ "Kind"
    , "Item"
    , "Producer"
    , "Generated [s]"
    , "Recipient"
    , "Received [s]"
    , "Elapsed [s]"
    ]

sep :: String
sep = ","

parseEvent :: Value -> Parser (ItemKey, ItemInfo, Maybe (Text, Double))
parseEvent =
  withObject "TraceEvent" $ \event ->
    do
      time <- event .: "time_s"
      message <- event .: "message"
      typ <- message .: "type"
      item <- message .: "id"
      parseMessage typ item time $ Object message

parseMessage :: Text -> Text -> Double -> Value -> Parser (ItemKey, ItemInfo, Maybe (Text, Double))
parseMessage "TXGenerated" item sent =
  withObject "TXGenerated" $ \message ->
    do
      let kind = "TX"
      producer <- message .: "publisher"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{producer, size, sent = Minimum $ Just sent}, Nothing)
parseMessage "IBGenerated" item sent =
  withObject "IBGenerated" $ \message ->
    do
      let kind = "IB"
      producer <- message .: "producer"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{producer, size, sent = Minimum $ Just sent}, Nothing)
parseMessage "EBGenerated" item sent =
  withObject "EBGenerated" $ \message ->
    do
      let kind = "EB"
      producer <- message .: "producer"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{producer, size, sent = Minimum $ Just sent}, Nothing)
parseMessage "RBGenerated" item sent =
  withObject "RBGenerated" $ \message ->
    do
      let kind = "RB"
      producer <- message .: "producer"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{producer, size, sent = Minimum $ Just sent}, Nothing)
parseMessage "VTBundleGenerated" item sent =
  withObject "VTBundleGenerated" $ \message ->
    do
      let kind = "VT"
      producer <- message .: "producer"
      size <- message .: "size_bytes"
      pure (ItemKey{..}, mempty{producer, size, sent = Minimum $ Just sent}, Nothing)
parseMessage "TXReceived" item received =
  withObject "TXReceived" $ \message ->
    do
      let kind = "TX"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty, Just (recipient, received))
parseMessage "IBReceived" item received =
  withObject "IBReceived" $ \message ->
    do
      let kind = "IB"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty, Just (recipient, received))
parseMessage "EBReceived" item received =
  withObject "EBReceived" $ \message ->
    do
      let kind = "EB"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty, Just (recipient, received))
parseMessage "RBReceived" item received =
  withObject "RBReceived" $ \message ->
    do
      let kind = "RB"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty, Just (recipient, received))
parseMessage "VTBundleReceived" item received =
  withObject "VTBundleReceived" $ \message ->
    do
      let kind = "VT"
      recipient <- message .: "recipient"
      pure (ItemKey{..}, mempty, Just (recipient, received))
parseMessage _ _ _ =
  const $ fail "Ignore"

type Index = Map ItemKey ItemInfo

tally :: Monad m => Value -> StateT Index m (Maybe String)
tally event =
  case parseMaybe parseEvent event of
    Just (itemKey, itemInfo, rec) ->
      do
        -- Insert the generated items.
        modify' $ M.insertWith (<>) itemKey itemInfo
        case rec of
          Just (recipient, received) ->
            do
              itemInfo' <- gets (M.! itemKey)
              pure . Just $ toCSV itemKey itemInfo' recipient received
          Nothing -> pure Nothing
    Nothing -> pure Nothing

receipt :: FilePath -> MVar (Maybe Value) -> IO ()
receipt receiptFile events =
  do
    h <- openFile receiptFile WriteMode
    hPutStrLn h itemHeader
    let
      go =
        liftIO (takeMVar events)
          >>= \case
            Nothing -> pure ()
            Just event -> tally event >>= maybe (pure ()) (liftIO . hPutStrLn h) >> go
    void $ go `execStateT` mempty
    hClose h
