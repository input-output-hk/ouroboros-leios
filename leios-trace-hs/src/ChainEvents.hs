{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Native parser for a cardano-node tracing log (@node.log@) of a Leios
--   prototype node. Unlike the simulator's @TraceEvent@ JSONL schema, the node
--   emits the cardano tracing envelope @{"ns":…, "data":{…}, …}@ with the Leios
--   events carried under @Consensus.LeiosKernel@ and @Forge.Loop@ namespaces.
--   This module extracts the Leios-relevant events (keyed by @ebHash@) and
--   discards everything else, so the chain verifier can consume node.log
--   directly without the jsonl intermediate.
module ChainEvents where

import Data.Aeson (Value, decode, withObject, (.:))
import Data.Aeson.Types (Parser, parseMaybe)
import qualified Data.ByteString.Lazy.Char8 as BSL8
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Word (Word64)
import GHC.Generics (Generic)

-- | A Leios-relevant event extracted from one node.log line. The @Text@ fields
--   are block hashes (the @ebHash@, or the RB hash); slots are absolute.
data ChainEvent
  = CSlot !Word64
  -- ^ @Forge.Loop.StartLeadershipCheck@: a per-slot tick for the SUT.
  | CEBForged !Text !Word64
  -- ^ @LeiosBlockForged@: the SUT forged an EB (ebHash, slot).
  | CEBAcquired !Text !Word64
  -- ^ @LeiosBlockAcquired@: the SUT received a peer EB (ebHash, ebSlot).
  | CVoted !Text !Word64
  -- ^ @LeiosVoted@: the SUT cast a vote (ebHash, EB's slot).
  | CVoteAcquired !Text !Word64
  -- ^ @LeiosVoteAcquired@: the SUT received a vote (ebHash, EB's slot).
  | CRBForged !Text !Word64
  -- ^ @Forge.Loop.ForgedBlock@: the SUT forged a ranking (Praos) block (hash, slot).
  deriving (Eq, Show, Generic)

-- | Parse a whole node.log, keeping only the Leios events and preserving order.
parseNodeLog :: BSL8.ByteString -> [ChainEvent]
parseNodeLog = mapMaybe parseLine . BSL8.lines

-- | Parse a single log line; @Nothing@ for non-JSON banners and unrelated events.
parseLine :: BSL8.ByteString -> Maybe ChainEvent
parseLine line = decode line >>= parseMaybe pEvent

pEvent :: Value -> Parser ChainEvent
pEvent = withObject "logline" $ \o -> do
  ns <- o .: "ns"
  d <- o .: "data"
  case ns :: Text of
    "Forge.Loop.StartLeadershipCheck" -> CSlot <$> d .: "slot"
    "Forge.Loop.ForgedBlock" -> CRBForged <$> d .: "block" <*> d .: "slot"
    "Consensus.LeiosKernel.TraceLeiosKernel" -> do
      kind <- d .: "kind"
      case kind :: Text of
        "LeiosBlockForged" -> CEBForged <$> d .: "hash" <*> d .: "slot"
        "LeiosBlockAcquired" -> CEBAcquired <$> d .: "ebHash" <*> d .: "ebSlot"
        "LeiosVoted" -> do
          v <- d .: "vote"
          CVoted <$> v .: "ebHash" <*> v .: "slot"
        "LeiosVoteAcquired" -> do
          v <- d .: "vote"
          CVoteAcquired <$> v .: "ebHash" <*> v .: "slot"
        _ -> fail "unhandled LeiosKernel kind"
    _ -> fail "unhandled ns"
