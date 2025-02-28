{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
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

data Event
  = Cpu
      { node :: !Text
      , cpu_time_s :: !Time
      , task_label :: !Text
      }
  | NetworkMessage
      { action :: !NetworkAction
      , sender :: !(Maybe Node)
      -- ^ @Just@ when @action == Sent@
      , recipient :: !Node
      , block_kind :: !BlockKind
      , msg_size_bytes :: !Bytes
      , sending_s :: !Time
      , ids :: ![Text]
      }
  | EnteredStateIB
      { node :: !Text
      , id :: !Text
      , slot :: !Word64
      }
  | EnteredStateEB
      { node :: !Text
      , id :: !Text
      , slot :: !Word64
      }
  | EnteredStateVT
      { node :: !Text
      , id :: !Text
      , slot :: !Word64
      }
  | EnteredStateRB
      { node :: !Text
      , id :: !Text
      , slot :: !Word64
      }
  | GeneratedIB
      { node :: !Text
      , id :: !Text
      , slot :: !SlotNo
      , size_bytes :: !Bytes
      , payload_bytes :: !Bytes
      , rb_ref :: !Text
      }
  | GeneratedEB
      { node :: !Text
      , id :: !Text
      , slot :: !Word64
      , size_bytes :: !Word64
      , input_blocks :: ![Text]
      }
  | GeneratedRB
      { node :: !Text
      , id :: !Text
      , slot :: !Word64
      , size_bytes :: !Word64
      , endorse_blocks :: ![Text]
      , payload_bytes :: !Word64
      }
  | GeneratedVT
      { node :: !Text
      , id :: !Text
      , slot :: !Word64
      , size_bytes :: !Word64
      , votes :: !Word64
      , endorse_blocks :: ![Text]
      }
  deriving (Eq, Show)
  deriving (Generic)

$(deriveJSON defaultOptions{sumEncoding = defaultTaggedObject{tagFieldName = "type"}} ''Event)

data TraceEvent = TraceEvent
  { time_s :: !Time
  , event :: !Event
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
