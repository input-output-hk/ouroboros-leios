{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

module LeiosEvents where

import Codec.CBOR.JSON
import Codec.CBOR.Read
import Codec.CBOR.Write
import Control.Exception
import Data.Aeson
import Data.Aeson.TH
import qualified Data.ByteString.Lazy.Char8 as BSL8
import Data.Fixed
import Data.Map (Map)
import Data.Maybe (mapMaybe)
import Data.String ()
import Data.Text (Text)
import Data.Word
import GHC.Generics

type Bytes = Word64
type SlotNo = Word64
type Time = Micro

data NetworkAction = Sent | Received
  deriving (Eq, Show)
  deriving (Generic, ToJSON, FromJSON)

data BlockKind = IB | EB | VT | RB
  deriving (Eq, Show)
  deriving (Generic, ToJSON, FromJSON)

type Node = Text
data Endorsement = Endorsement {eb :: BlockRef}
  deriving (Eq, Show, Generic, ToJSON, FromJSON)
data BlockRef = BlockRef {id :: Text}
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

data Event where
  Cpu ::
    { node :: !Text
    , cpu_time_s :: !Time
    , task_label :: !Text
    } ->
    Event
  IBSent
    , EBSent
    , VTBundleSent
    , RBSent
    , IBReceived
    , EBReceived
    , VTBundleReceived
    , RBReceived ::
    { sender :: !(Maybe Node)
    -- ^ @Just@ when @action == Sent@
    , recipient :: !Node
    , msg_size_bytes :: !(Maybe Bytes)
    , sending_s :: !(Maybe Time)
    , block_id :: !(Maybe Text)
    , block_ids :: !(Maybe [Text])
    -- ^ used by Haskell when sending more blocks in one message.
    } ->
    Event
  IBEnteredState
    , EBEnteredState
    , VTBundleEnteredState
    , RBEnteredState ::
    { node :: !Text
    , id :: !Text
    , slot :: !Word64
    } ->
    Event
  IBGenerated ::
    { producer :: !Text
    , id :: !Text
    , slot :: !SlotNo
    , size_bytes :: !(Maybe Bytes)
    , payload_bytes :: !(Maybe Bytes)
    , rb_ref :: !(Maybe Text)
    } ->
    Event
  EBGenerated ::
    { producer :: !Text
    , id :: !Text
    , slot :: !Word64
    , bytes :: !Word64
    , input_blocks :: ![BlockRef]
    } ->
    Event
  RBGenerated ::
    { producer :: !Text
    , block_id :: !(Maybe Text)
    , vrf :: !(Maybe Int)
    , slot :: !Word64
    , size_bytes :: !(Maybe Word64)
    , endorsement :: !(Maybe Endorsement)
    , endorsements :: !(Maybe [Endorsement])
    , payload_bytes :: !(Maybe Word64)
    } ->
    Event
  VTBundleGenerated ::
    { producer :: !Text
    , id :: !Text
    , slot :: !Word64
    , bytes :: !Word64
    , votes :: !(Map Text Word64)
    } ->
    Event
  deriving (Eq, Show)
  deriving (Generic)

$( deriveJSON
    defaultOptions
      { sumEncoding = defaultTaggedObject{tagFieldName = "type"}
      , fieldLabelModifier = \fl -> case fl of
          ('b' : 'l' : 'o' : 'c' : 'k' : '_' : xs) -> xs
          xs -> xs
      }
    ''Event
 )

data TraceEvent = TraceEvent
  { time_s :: !Time
  , message :: !Event
  }
  deriving (Eq, Show)
  deriving (Generic, ToJSON, FromJSON)

type EventLog = [TraceEvent]

-- | Discards lines that do not parse.
decodeJSONL :: BSL8.ByteString -> [TraceEvent]
decodeJSONL = mapMaybe decode . BSL8.lines

encodeJSONL :: [TraceEvent] -> BSL8.ByteString
encodeJSONL = BSL8.unlines . map encode

-- | Throws exception on CBOR decoding errors, skips values that do not decode as TraceEvent.
--   WARNING: seems not to be compatible with CBOR format produced by rust-sim.
decodeCBOR :: BSL8.ByteString -> [TraceEvent]
decodeCBOR = go
 where
  go s | BSL8.null s = []
  go s =
    case deserialiseFromBytes (decodeValue False) s of
      Left e -> throw e
      Right (s', v) -> case fromJSON v of
        Success x -> x : go s'
        Error _ -> go s'

-- | Uses standard CBOR encoding of JSON values, encoded events are concatenated with no separator.
encodeCBOR :: [TraceEvent] -> BSL8.ByteString
encodeCBOR = BSL8.concat . map (toLazyByteString . encodeValue . toJSON)
