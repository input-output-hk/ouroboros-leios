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
--
--   Two node trace schemas are supported:
--
--   * pre-w31: one combined namespace @Consensus.LeiosKernel.TraceLeiosKernel@
--     with the event in @data.kind@, and votes carrying @vote.ebHash@ +
--     @vote.slot@;
--   * w31+: per-event namespaces (@Consensus.LeiosKernel.BlockForged@,
--     @….BlockAcquired@, @….Voted@, …) — the @data.kind@ dispatch is shared
--     with the old schema — and votes carrying only the announcing RB
--     (@vote.rbHash@). RB-keyed votes are resolved to their EB via the
--     @….BlockAnnounced@ events (@rbHash@ → @ebHash@, @ebSlot@) seen earlier
--     in the stream; see 'resolveVotes'.
module ChainEvents where

import Control.Applicative ((<|>))
import Data.Aeson (Object, Value, decode, withObject, (.:))
import Data.Aeson.Types (Parser, parseMaybe)
import qualified Data.ByteString.Lazy.Char8 as BSL8
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word (Word64)
import GHC.Generics (Generic)

-- | A Leios-relevant event extracted from one node.log line. The @Text@ fields
--   are block hashes (the @ebHash@, or the RB hash); slots are absolute.
data ChainEvent
  = -- | @Forge.Loop.StartLeadershipCheck@: a per-slot tick for the SUT.
    CSlot !Word64
  | -- | @LeiosBlockForged@: the SUT forged an EB (ebHash, slot).
    CEBForged !Text !Word64
  | -- | @LeiosBlockAcquired@: the SUT received a peer EB (ebHash, ebSlot).
    CEBAcquired !Text !Word64
  | -- | @LeiosVoted@: the SUT cast a vote (ebHash, EB's slot). A w31+ vote
    --   whose announcing RB has not (yet) been seen keeps the RB hash and
    --   slot 0; the verifier ignores votes for unknown EBs, so an unresolved
    --   vote stays visible in the event stream without affecting verification.
    CVoted !Text !Word64
  | -- | @LeiosVoteAcquired@: the SUT received a vote (ebHash, EB's slot);
    --   unresolved w31+ votes are kept as for 'CVoted'.
    CVoteAcquired !Text !Word64
  | -- | @Forge.Loop.ForgedBlock@: the SUT forged a ranking (Praos) block (hash, slot).
    CRBForged !Text !Word64
  deriving (Eq, Show, Generic)

-- | A parsed log line before RB→EB vote resolution (internal).
data RawEvent
  = -- | Directly representable as a 'ChainEvent'.
    REvent !ChainEvent
  | -- | @LeiosBlockAnnounced@: an RB announcing an EB (rbHash, ebHash, ebSlot).
    RAnnounced !Text !Text !Word64
  | -- | w31+ @LeiosVoted@: the SUT's vote, keyed by the announcing RB.
    RVotedRb !Text
  | -- | w31+ @LeiosVoteAcquired@: a received vote, keyed by the announcing RB.
    RVoteAcquiredRb !Text
  deriving (Eq, Show, Generic)

-- | Parse a whole node.log, keeping only the Leios events and preserving
--   order. Lazy in the input stream, so it can consume a live @tail -f@.
parseNodeLog :: BSL8.ByteString -> [ChainEvent]
parseNodeLog = resolveVotes . mapMaybe parseRawLine . BSL8.lines

-- | Resolve RB-keyed (w31+) votes to their EB using the @BlockAnnounced@
--   events seen so far, dropping the announcements themselves from the
--   stream. Lazy in the tail, so safe on an unbounded stream. Votes whose
--   announcing RB is unknown (announcement not yet seen) keep the RB hash
--   with slot 0 — harmless downstream, since the verifier ignores votes
--   whose hash matches no known EB.
resolveVotes :: [RawEvent] -> [ChainEvent]
resolveVotes = go Map.empty
 where
  go _ [] = []
  go m (REvent e : rest) = e : go m rest
  go m (RAnnounced rb eb ebSlot : rest) = go (Map.insert rb (eb, ebSlot) m) rest
  go m (RVotedRb rb : rest) = resolve CVoted rb m : go m rest
  go m (RVoteAcquiredRb rb : rest) = resolve CVoteAcquired rb m : go m rest
  resolve ctor rb m = case Map.lookup rb m of
    Just (eb, ebSlot) -> ctor eb ebSlot
    Nothing -> ctor rb 0

-- | Parse a single log line; @Nothing@ for non-JSON banners and unrelated
--   events. NOTE: per-line parsing cannot resolve w31+ RB-keyed votes (that
--   needs the announcement context of the whole stream — use 'parseNodeLog');
--   here they are returned unresolved, as for 'CVoted'.
parseLine :: BSL8.ByteString -> Maybe ChainEvent
parseLine line =
  parseRawLine line >>= \raw -> case raw of
    REvent e -> Just e
    RVotedRb rb -> Just (CVoted rb 0)
    RVoteAcquiredRb rb -> Just (CVoteAcquired rb 0)
    RAnnounced{} -> Nothing

-- | Parse a single log line into a 'RawEvent'.
parseRawLine :: BSL8.ByteString -> Maybe RawEvent
parseRawLine line = decode line >>= parseMaybe pRawEvent

pRawEvent :: Value -> Parser RawEvent
pRawEvent = withObject "logline" $ \o -> do
  ns <- o .: "ns"
  d <- o .: "data"
  case ns :: Text of
    "Forge.Loop.StartLeadershipCheck" -> REvent . CSlot <$> d .: "slot"
    "Forge.Loop.ForgedBlock" -> REvent <$> (CRBForged <$> d .: "block" <*> d .: "slot")
    -- Covers both the pre-w31 combined namespace (…LeiosKernel.TraceLeiosKernel)
    -- and the w31+ per-event namespaces (…LeiosKernel.BlockForged, …); both
    -- carry the event discriminator in data.kind.
    _ | "Consensus.LeiosKernel" `T.isPrefixOf` ns -> do
      kind <- d .: "kind"
      case kind :: Text of
        "LeiosBlockForged" -> REvent <$> (CEBForged <$> d .: "hash" <*> d .: "slot")
        "LeiosBlockAcquired" -> REvent <$> (CEBAcquired <$> d .: "ebHash" <*> d .: "ebSlot")
        "LeiosBlockAnnounced" ->
          RAnnounced <$> d .: "rbHash" <*> d .: "ebHash" <*> d .: "ebSlot"
        "LeiosVoted" -> do
          v :: Object <- d .: "vote"
          REvent <$> (CVoted <$> v .: "ebHash" <*> v .: "slot") -- pre-w31
            <|> RVotedRb <$> v .: "rbHash" -- w31+
        "LeiosVoteAcquired" -> do
          v :: Object <- d .: "vote"
          REvent <$> (CVoteAcquired <$> v .: "ebHash" <*> v .: "slot") -- pre-w31
            <|> RVoteAcquiredRb <$> v .: "rbHash" -- w31+
        _ -> fail "unhandled LeiosKernel kind"
    _ -> fail "unhandled ns"
