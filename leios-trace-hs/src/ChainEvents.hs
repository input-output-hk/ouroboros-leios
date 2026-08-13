{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Native parser for a cardano-node tracing log (@node.log@) of a Leios
--   prototype node. Unlike the simulator's @TraceEvent@ JSONL schema, the node
--   emits the cardano tracing envelope @{"ns":…, "data":{…}, …}@.
--
--   w31+ nodes use per-event namespaces (@Consensus.LeiosKernel.BlockForged@
--   etc.); older nodes used a single @Consensus.LeiosKernel.TraceLeiosKernel@
--   envelope with a @kind@ dispatch. Both are handled below.
--
--   Votes are RB-keyed on the wire (@vote.rbHash@) while the verifier's
--   'CVoted'/'CVoteAcquired' carry the voted EB's hash and slot. The parse is
--   therefore a stateful fold maintaining two maps:
--
--     * election slot -> ebHash            (from @AnnouncementAccepted@; in
--       Linear Leios the announcing RB and its EB share the election slot)
--     * rbHash -> slot                     (from @AddedToCurrentChain@ and
--       @SwitchedToAFork@, the two ways ChainDB reports a new selection; both
--       carry the adopted tip in @newtip@, and a node votes on the RB it
--       selected however it came to select it)
--
--   composed at each vote event to resolve rbHash -> (ebHash, ebSlot).
--   Unresolvable votes (linkage missing, e.g. truncated log prefix) are
--   dropped rather than guessed.
module ChainEvents where

import Data.Aeson (Object, Value, decode, withObject, (.:))
import Data.Aeson.Types (Parser, parseMaybe)
import qualified Data.ByteString.Lazy.Char8 as BSL8
import Data.List (mapAccumL)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Read as TR
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
  | -- | @LeiosVoted@: the SUT cast a vote (ebHash, EB's slot).
    CVoted !Text !Word64
  | -- | @LeiosVoteAcquired@: the SUT received a vote (ebHash, EB's slot).
    CVoteAcquired !Text !Word64
  | -- | @Forge.Loop.ForgedBlock@: the SUT forged a ranking (Praos) block (hash, slot).
    CRBForged !Text !Word64
  | -- | @Forge.Loop.NodeIsLeader@: the SUT won the Praos slot lottery (slot).
    --   Emitted by consensus independently of anything Leios does, so it is a
    --   non-circular record of EB-production eligibility — the spec assumes
    --   @canProduceEB@ holds exactly when the node can make a ranking block. Unlike
    --   the cardano-api schedule it covers every epoch the log spans, which makes it
    --   usable as a fallback when the query cannot supply a schedule for an epoch.
    CNodeIsLeader !Word64
  | -- | @Consensus.LeiosKernel.AnnouncementAccepted@: the chain head now announces
    --   this EB (ebHash, election slot). This — not acquiring the body — is what
    --   makes an EB votable, so it is what the verifier must key voting obligations
    --   on. Also retained internally as vote-resolution linkage.
    CAnnouncementAccepted !Text !Word64
  | -- | @Consensus.LeiosKernel.NotVoted@: the SUT deliberately abstained from
    --   voting on an EB (ebHash, EB's election slot, reason). In Linear Leios an
    --   abstention is not a fault: the reason enumerates protocol-legal causes
    --   (@chainTipDoesNotAnnounce@ once the chain has extended past the announcer,
    --   @tooLate@, @notOnCommittee@). Corroborates a closed voting window.
    CNotVoted !Text !Word64 !Text
  | -- | @ChainDB.AddBlockEvent.AddedToCurrentChain@ / @SwitchedToAFork@: the SUT's
    --   selected chain now has this tip slot. In Linear Leios a cert is valid only
    --   in the ranking block that directly extends the announcer, so once the tip
    --   advances past an announced EB that EB can no longer be certified — the
    --   verifier uses this to close the EB's voting window.
    CChainExtended !Word64
  deriving (Eq, Show, Generic)

-- | Internal: one parsed line — a directly-emittable event, a linkage fact
--   for the vote-resolution maps, or an RB-keyed vote awaiting resolution.
data Raw
  = RawEvent !ChainEvent
  | -- | announcement accepted: election slot, ebHash
    RawAnn !Word64 !Text
  | -- | chain linkage: rbHash, new tip slot. Records rbHash -> slot for vote
    --   resolution AND surfaces the tip advance as 'CChainExtended'.
    RawRb !Text !Word64
  | -- | vote (True = cast by the SUT, False = acquired from a peer): rbHash
    RawVote !Bool !Text
  | -- | deliberate abstention: ebHash, election slot, reason. EB-keyed.
    RawNotVoted !Text !Word64 !Text

-- | Vote-resolution state.
data LinkState = LinkState
  { lsEbBySlot :: !(Map.Map Word64 Text)
  , lsSlotByRb :: !(Map.Map Text Word64)
  }

emptyLinkState :: LinkState
emptyLinkState = LinkState Map.empty Map.empty

-- | Parse a whole node.log, keeping only the Leios events and preserving order.
parseNodeLog :: BSL8.ByteString -> [ChainEvent]
parseNodeLog =
  catMaybes . snd . mapAccumL step emptyLinkState . mapMaybe parseRaw . BSL8.lines
 where
  step :: LinkState -> Raw -> (LinkState, Maybe ChainEvent)
  step !st raw = case raw of
    RawEvent ev -> (st, Just ev)
    RawAnn slot ebHash ->
      ( st{lsEbBySlot = Map.insert slot ebHash (lsEbBySlot st)}
      , Just (CAnnouncementAccepted ebHash slot)
      )
    RawRb rbHash slot ->
      ( st{lsSlotByRb = Map.insert rbHash slot (lsSlotByRb st)}
      , Just (CChainExtended slot)
      )
    RawVote ours rbHash ->
      ( st
      , do
          slot <- Map.lookup rbHash (lsSlotByRb st)
          ebHash <- Map.lookup slot (lsEbBySlot st)
          pure $ (if ours then CVoted else CVoteAcquired) ebHash slot
      )
    RawNotVoted ebHash slot reason ->
      (st, Just (CNotVoted ebHash slot reason))

-- | Parse a single log line; @Nothing@ for non-JSON banners and unrelated events.
parseRaw :: BSL8.ByteString -> Maybe Raw
parseRaw line = decode line >>= parseMaybe pRaw

pRaw :: Value -> Parser Raw
pRaw = withObject "logline" $ \o -> do
  ns <- o .: "ns"
  d <- o .: "data"
  case ns :: Text of
    "Forge.Loop.StartLeadershipCheck" -> RawEvent . CSlot <$> d .: "slot"
    "Forge.Loop.ForgedBlock" ->
      RawEvent <$> (CRBForged <$> d .: "block" <*> d .: "slot")
    "Forge.Loop.NodeIsLeader" -> RawEvent . CNodeIsLeader <$> d .: "slot"
    -- w31+ per-event namespaces
    "Consensus.LeiosKernel.BlockForged" ->
      RawEvent <$> (CEBForged <$> d .: "hash" <*> d .: "slot")
    "Consensus.LeiosKernel.BlockAcquired" ->
      RawEvent <$> (CEBAcquired <$> d .: "ebHash" <*> d .: "ebSlot")
    "Consensus.LeiosKernel.AnnouncementAccepted" ->
      RawAnn <$> d .: "electionSlot" <*> d .: "ebHash"
    "Consensus.LeiosKernel.Voted" -> do
      v <- d .: "vote"
      RawVote True <$> v .: "rbHash"
    "Consensus.LeiosKernel.VoteAcquired" -> do
      v <- d .: "vote"
      RawVote False <$> v .: "rbHash"
    "Consensus.LeiosKernel.NotVoted" ->
      RawNotVoted <$> d .: "ebHash" <*> d .: "ebSlot" <*> d .: "reason"
    -- Extending the current chain and switching to a fork are the two ways
    -- ChainDB reports adopting a new tip, and both matter twice over: the tip
    -- advance retires any EB the superseded announcer carried, and the adopted
    -- RB is what a vote is keyed on. Ignoring the fork-switch case silently
    -- drops every vote for an RB that arrived on a fork.
    "ChainDB.AddBlockEvent.AddedToCurrentChain" -> newtip d
    "ChainDB.AddBlockEvent.SwitchedToAFork" -> newtip d
    -- pre-w31 envelope (kept for older logs)
    "Consensus.LeiosKernel.TraceLeiosKernel" -> do
      kind <- d .: "kind"
      case kind :: Text of
        "LeiosBlockForged" -> RawEvent <$> (CEBForged <$> d .: "hash" <*> d .: "slot")
        "LeiosBlockAcquired" -> RawEvent <$> (CEBAcquired <$> d .: "ebHash" <*> d .: "ebSlot")
        "LeiosVoted" -> do
          v <- d .: "vote"
          RawEvent <$> (CVoted <$> v .: "ebHash" <*> v .: "slot")
        "LeiosVoteAcquired" -> do
          v <- d .: "vote"
          RawEvent <$> (CVoteAcquired <$> v .: "ebHash" <*> v .: "slot")
        _ -> fail "unhandled LeiosKernel kind"
    _ -> fail "unhandled ns"

-- | The newly adopted tip, shared by ChainDB's two selection-change events.
newtip :: Object -> Parser Raw
newtip d = do
  tip <- d .: "newtip"
  maybe (fail "unparseable newtip") (pure . uncurry RawRb) (parseTip tip)

-- | @"\<64 hex chars\>@\<decimal slot\>"@ from ChainDB's @newtip@ field.
parseTip :: Text -> Maybe (Text, Word64)
parseTip t = case T.splitOn "@" t of
  [h, s]
    | T.length h == 64 ->
        case TR.decimal s of
          Right (n, rest) | T.null rest -> Just (h, n)
          _ -> Nothing
  _ -> Nothing
