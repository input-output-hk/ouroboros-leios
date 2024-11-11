{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

-- | Generic block relay protocol.
--
-- Modeled after TxSubmission2 from ouroboros-network.
module LeiosProtocol.Relay (
  Relay (..),
  Message (..),
  SingRelay (..),
  SingBlockingStyle (..),
  StBlockingStyle (..),
  BlockingReplyList (..),
  NumBlkIdsToAck (..),
  NumBlkIdsToReq (..),
  BlockRelayMessage,
  relayProducer,
) where

import ChanTCP
import Control.Concurrent.Class.MonadSTM
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Data.Bits
import Data.Kind (Type)
import Data.List (find)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe (catMaybes, isNothing, mapMaybe)
import Data.Monoid (Sum (..))
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as Seq
import Data.Singletons
import Data.Word (Word16)
import GHC.Generics
import Network.TypedProtocol.Core
import qualified Network.TypedProtocol.Peer.Client as TC
import NoThunks.Class (NoThunks (..))
import Ouroboros.Network.Util.ShowProxy
import Quiet (Quiet (..))
import RelayProtocol (BlockWithTicket (BlockWithTicket), RelayBuffer (RelayBuffer), Ticket, lookupByTicket, takeAfterTicket, zeroTicket)

-- | The kind of the transaction-submission protocol, and the types of the
-- states in the protocol state machine.
--
-- We describe this protocol using the label \"client\" for the peer that is
-- submitting transactions, and \"server\" for the one receiving them. The
-- protocol is however pull based, so it is typically the server that has
-- agency in this protocol. This is the opposite of the chain sync and block
-- fetch protocols, but that makes sense because the information flow is also
-- reversed: submitting transactions rather than receiving headers and blocks.
--
-- Because these client\/server labels are somewhat confusing in this case, we
-- sometimes clarify by using the terms inbound and outbound. This refers to
-- whether transactions are flowing towards a peer or away, and thus indicates
-- what role the peer is playing.
data Relay (blkid :: Type) (blk :: Type) (blkmd :: Type) where
  -- | Initial protocol message.
  StInit :: Relay blkid blk blkmd
  -- | The server (inbound side) has agency; it can either terminate, ask for
  -- transaction identifiers or ask for transactions.
  --
  -- There is no timeout in this state.
  StIdle :: Relay blkid blk blkmd
  -- | The client (outbound side) has agency; it must reply with a
  -- list of transaction identifiers that it wishes to submit.
  --
  -- There are two sub-states for this, for blocking and non-blocking cases.
  StBlkIds :: StBlockingStyle -> Relay blkid blk blkmd
  -- | The client (outbound side) has agency; it must reply with the list of
  -- transactions.
  StBlks :: Relay blkid blk blkmd
  -- | Nobody has agency; termination state.
  StDone :: Relay blkid blk blkmd

instance
  ( ShowProxy blkid
  , ShowProxy blk
  , ShowProxy blkmd
  ) =>
  ShowProxy (Relay blkid blk blkmd)
  where
  showProxy _ =
    concat
      [ "Relay "
      , showProxy (Proxy :: Proxy blkid)
      , " "
      , showProxy (Proxy :: Proxy blk)
      , " "
      , showProxy (Proxy :: Proxy blkmd)
      ]

instance ShowProxy (StIdle :: Relay blkid blk blkmd) where
  showProxy _ = "StIdle"

type SingRelay ::
  Relay blkid blk blkmd ->
  Type
data SingRelay k where
  SingInit :: SingRelay StInit
  SingIdle :: SingRelay StIdle
  SingBlkIds ::
    SingBlockingStyle stBlocking ->
    SingRelay (StBlkIds stBlocking)
  SingTxs :: SingRelay StBlks
  SingDone :: SingRelay StDone

deriving instance Show (SingRelay k)

instance StateTokenI StInit where stateToken = SingInit
instance StateTokenI StIdle where stateToken = SingIdle
instance
  SingI stBlocking =>
  StateTokenI (StBlkIds stBlocking)
  where
  stateToken = SingBlkIds sing
instance StateTokenI StBlks where stateToken = SingTxs
instance StateTokenI StDone where stateToken = SingDone

data StBlockingStyle where
  -- | In this sub-state the reply need not be prompt. There is no timeout.
  StBlocking :: StBlockingStyle
  -- | In this state the peer must reply. There is a timeout.
  StNonBlocking :: StBlockingStyle

newtype NumBlkIdsToAck = NumBlkIdsToAck {getNumBlkIdsToAck :: Word16}
  deriving (Eq, Ord, NFData, Generic)
  deriving newtype (Num, Enum, Real, Integral, Bounded, Bits, FiniteBits, NoThunks)
  deriving (Semigroup) via (Sum Word16)
  deriving (Monoid) via (Sum Word16)
  deriving (Show) via (Quiet NumBlkIdsToAck)

newtype NumBlkIdsToReq = NumBlkIdsToReq {getNumBlkIdsToReq :: Word16}
  deriving (Eq, Ord, NFData, Generic)
  deriving newtype (Num, Enum, Real, Integral, Bounded, Bits, FiniteBits, NoThunks)
  deriving (Semigroup) via (Sum Word16)
  deriving (Monoid) via (Sum Word16)
  deriving (Show) via (Quiet NumBlkIdsToReq)

finiteByteSize :: (Integral a, FiniteBits b) => b -> a
finiteByteSize x = ceiling (realToFrac (finiteBitSize x) / 8 :: Double)

-- | There are some constraints of the protocol that are not captured in the
-- types of the messages, but are documented with the messages. Violation
-- of these constraints is also a protocol error. The constraints are intended
-- to ensure that implementations are able to work in bounded space.
instance Protocol (Relay blkid blk blkmd) where
  -- \| The messages in the block relay protocol.
  --
  -- In this protocol the consumer (inbound side, server role) always
  -- initiates and the producer (outbound side, client role) replies.
  -- This makes it a pull based protocol where the receiver manages the
  -- control flow.
  --
  -- The protocol involves asking for block identifiers, and then
  -- asking for blocks corresponding to the identifiers of interest.
  --
  -- There are two ways to ask for block identifiers, blocking and
  -- non-blocking. They otherwise have the same semantics.
  --
  -- The protocol maintains a notional FIFO of \"outstanding\" block
  -- identifiers that have been provided but not yet acknowledged. Only
  -- blocks that are outstanding can be requested: they can be
  -- requested in any order, but at most once. Block identifiers are
  -- acknowledged in the same FIFO order they were provided in. The
  -- acknowledgement is included in the same messages used to ask for more
  -- block identifiers.
  data Message (Relay blkid blk blkmd) from to where
    MsgInit ::
      Message (Relay blkid blk blkmd) StInit StIdle
    -- \| Request a non-empty list of block identifiers from the client,
    -- and confirm a number of outstanding block identifiers.
    --
    -- With 'TokBlocking' this is a a blocking operation: the response will
    -- always have at least one block identifier, and it does not expect
    -- a prompt response: there is no timeout. This covers the case when there
    -- is nothing else to do but wait. For example this covers leaf nodes that
    -- rarely, if ever, create and submit a block.
    --
    -- With 'TokNonBlocking' this is a non-blocking operation: the response
    -- may be an empty list and this does expect a prompt response. This
    -- covers high throughput use cases where we wish to pipeline, by
    -- interleaving requests for additional block identifiers with
    -- requests for blocks, which requires these requests not block.
    --
    -- The request gives the maximum number of block identifiers that
    -- can be accepted in the response. This must be greater than zero in the
    -- 'TokBlocking' case. In the 'TokNonBlocking' case either the numbers
    -- acknowledged or the number requested must be non-zero. In either case,
    -- the number requested must not put the total outstanding over the fixed
    -- protocol limit.
    --
    -- The request also gives the number of outstanding block
    -- identifiers that can now be acknowledged. The actual blocks
    -- to acknowledge are known to the peer based on the FIFO order in which
    -- they were provided.
    --
    -- There is no choice about when to use the blocking case versus the
    -- non-blocking case, it depends on whether there are any remaining
    -- unacknowledged blocks (after taking into account the ones
    -- acknowledged in this message):
    --
    -- \* The blocking case must be used when there are zero remaining
    --   unacknowledged blocks.
    --
    -- \* The non-blocking case must be used when there are non-zero remaining
    --   unacknowledged blocks.
    MsgRequestBlkIds ::
      forall (blocking :: StBlockingStyle) blk blkid blkmd.
      SingBlockingStyle blocking ->
      NumBlkIdsToAck ->
      -- \^ Acknowledge this number of outstanding txids
      NumBlkIdsToReq ->
      -- \^ Request up to this number of txids.
      Message (Relay blkid blk blkmd) StIdle (StBlkIds blocking)
    -- \| Reply with a list of block identifiers for available
    -- blocks, along with metadata for each block.
    --
    -- The list must not be longer than the maximum number requested.
    --
    -- In the 'StBlkIds' 'Blocking' state the list must be non-empty while
    -- in the 'StBlkIds' 'NonBlocking' state the list may be empty.
    --
    -- These blocks are added to the notional FIFO of outstanding
    -- block identifiers for the protocol.
    --
    -- TODO: review reference to mempool here
    -- The order in which these block identifiers are returned must be
    -- the order in which they are submitted to the mempool, to preserve
    -- dependent blocks.
    MsgReplyBlkIds ::
      BlockingReplyList blocking (blkid, blkmd) ->
      Message (Relay blkid blk blkmd) (StBlkIds blocking) StIdle
    -- \| Request one or more blocks corresponding to the given
    -- block identifiers.
    --
    -- While it is the responsibility of the replying peer to keep within
    -- pipelining in-flight limits, the sender must also cooperate by keeping
    -- the total requested across all in-flight requests within the limits.
    --
    -- It is an error to ask for block identifiers that were not
    -- previously announced (via 'MsgReplyBlkIds').
    --
    -- It is an error to ask for block identifiers that are not
    -- outstanding or that were already asked for.
    MsgRequestBlks ::
      [blkid] ->
      Message (Relay blkid blk blkmd) StIdle StBlks
    -- \| Reply with the requested blocks, or implicitly discard.
    --
    -- Blocks can become invalid between the time the block
    -- identifier was sent and the block being requested. Invalid
    -- (including committed) blocks do not need to be sent.
    --
    -- Any block identifiers requested but not provided in this reply
    -- should be considered as if this peer had never announced them. (Note
    -- that this is no guarantee that the block is invalid, it may still
    -- be valid and available from another peer).
    MsgReplyBlks ::
      [blk] ->
      Message (Relay blkid blk blkmd) StBlks StIdle
    -- \| Termination message, initiated by the client when the server is
    -- making a blocking call for more block identifiers.
    MsgDone ::
      Message (Relay blkid blk blkmd) (StBlkIds StBlocking) StDone

  type StateAgency StInit = ClientAgency
  type StateAgency (StBlkIds b) = ClientAgency
  type StateAgency StBlks = ClientAgency
  type StateAgency StIdle = ServerAgency
  type StateAgency StDone = NobodyAgency

  type StateToken = SingRelay

instance
  ( NFData blkid
  , NFData blk
  , NFData blkmd
  ) =>
  NFData (Message (Relay blkid blk blkmd) from to)
  where
  rnf MsgInit = ()
  rnf (MsgRequestBlkIds tkbs w1 w2) = rnf tkbs `seq` rnf w1 `seq` rnf w2
  rnf (MsgReplyBlkIds brl) = rnf brl
  rnf (MsgRequestBlks txids) = rnf txids
  rnf (MsgReplyBlks txs) = rnf txs
  rnf MsgDone = ()

instance
  ( MessageSize blkid
  , MessageSize blk
  , MessageSize blkmd
  ) =>
  MessageSize (Message (Relay blkid blk blkmd) from to)
  where
  messageSizeBytes MsgInit = 1
  messageSizeBytes (MsgRequestBlkIds tkbs w1 w2) = messageSizeBytes tkbs + finiteByteSize w1 + finiteByteSize w2
  messageSizeBytes (MsgReplyBlkIds brl) = messageSizeBytes brl
  messageSizeBytes (MsgRequestBlks txids) = sum $ map messageSizeBytes txids
  messageSizeBytes (MsgReplyBlks txs) = sum $ map messageSizeBytes txs
  messageSizeBytes MsgDone = 1

-- | The value level equivalent of 'BlockingStyle'.
--
-- This is also used in 'MsgRequestBlkIds' where it is interpreted (and can be
-- encoded) as a 'Bool' with 'True' for blocking, and 'False' for non-blocking.
data SingBlockingStyle (k :: StBlockingStyle) where
  SingBlocking :: SingBlockingStyle StBlocking
  SingNonBlocking :: SingBlockingStyle StNonBlocking

deriving instance Eq (SingBlockingStyle b)
deriving instance Show (SingBlockingStyle b)

type instance Sing = SingBlockingStyle
instance SingI StBlocking where sing = SingBlocking
instance SingI StNonBlocking where sing = SingNonBlocking

instance NFData (SingBlockingStyle b) where
  rnf SingBlocking = ()
  rnf SingNonBlocking = ()

instance MessageSize (SingBlockingStyle blocking) where
  messageSizeBytes _ = 1

-- | We have requests for lists of things. In the blocking case the
-- corresponding reply must be non-empty, whereas in the non-blocking case
-- and empty reply is fine.
data BlockingReplyList (blocking :: StBlockingStyle) a where
  BlockingReply :: NonEmpty a -> BlockingReplyList StBlocking a
  NonBlockingReply :: [a] -> BlockingReplyList StNonBlocking a

deriving instance Eq a => Eq (BlockingReplyList blocking a)
deriving instance Show a => Show (BlockingReplyList blocking a)

instance NFData a => NFData (BlockingReplyList blocking a) where
  rnf (BlockingReply as) = rnf as
  rnf (NonBlockingReply as) = rnf as

deriving instance
  (Eq blkid, Eq blk, Eq blkmd) =>
  Eq (Message (Relay blkid blk blkmd) from to)

deriving instance
  (Show blkid, Show blk, Show blkmd) =>
  Show (Message (Relay blkid blk blkmd) from to)

instance MessageSize a => MessageSize (BlockingReplyList blocking a) where
  messageSizeBytes (BlockingReply xs) = sum $ fmap messageSizeBytes xs
  messageSizeBytes (NonBlockingReply xs) = sum $ map messageSizeBytes xs

type BlockRelayMessage blkid blk blkmd = Message (Relay blkid blk blkmd)

data RelayProtocolError
  = ProtocolErrorAckedTooManyBlkids
  | ProtocolErrorRequestedNothing
  | ProtocolErrorRequestedTooManyBlkids NumBlkIdsToReq NumBlkIdsToAck
  | ProtocolErrorRequestBlocking
  | ProtocolErrorRequestNonBlocking
  | ProtocolErrorRequestedUnavailableBlk
  deriving (Show)

instance Exception RelayProtocolError

-- | Protocol agent that sends the blocks.
--
--   The implementation is mostly cribbed from
--   ouroboros-netowork:Ouroboros.Network.TxSubmission.Outbound but
--   adapted to use `RelayBuffer` and implemented directly as a
--   TypedProtocol peer.
--
--   Locally keeps track of a window of blkids that the consumer is allowed to ask for.
relayProducer ::
  forall m blk blkid blkmd.
  (MonadSTM m, Ord blkid) =>
  (blk -> blkmd) ->
  -- | Maximum number of unacknowledged blkids allowed
  NumBlkIdsToAck ->
  RelayBuffer m blk blkid ->
  TC.Client (Relay blkid blk blkmd) NonPipelined StIdle m ()
relayProducer blkMetaData maxUnacked (RelayBuffer buffer) = idle Seq.empty zeroTicket
 where
  idle :: StrictSeq (blkid, Ticket) -> Ticket -> TC.Client (Relay blkid blk blkmd) NonPipelined StIdle m ()
  idle !unackedSeq !lastIdx = TC.Await $ \case
    MsgRequestBlkIds blocking ackNo reqNo -> TC.Effect $ do
      when (getNumBlkIdsToAck ackNo > fromIntegral (Seq.length unackedSeq)) $
        throw ProtocolErrorAckedTooManyBlkids

      when
        ( fromIntegral (Seq.length unackedSeq)
            - getNumBlkIdsToAck ackNo
            + getNumBlkIdsToReq reqNo
            > getNumBlkIdsToAck maxUnacked
        )
        $ throw (ProtocolErrorRequestedTooManyBlkids reqNo maxUnacked)

      -- Update our tracking state to remove the number of blkids that the
      -- peer has acknowledged.
      let !unackedSeq' = Seq.drop (fromIntegral ackNo) unackedSeq

      -- Updates our tracking state with any extra blks available.
      let update blks =
            -- These blks should all be fresh
            assert (all (\(BlockWithTicket _ _ idx) -> idx > lastIdx) blks) $
              let !unackedSeq'' =
                    unackedSeq'
                      <> Seq.fromList
                        [(blkid, idx) | BlockWithTicket _ blkid idx <- blks]
                  !lastIdx'
                    | null blks = lastIdx
                    | otherwise = idx
                   where
                    BlockWithTicket _ _ idx = last blks
                  blks' :: [(blkid, blkmd)]
                  blks' = [(blkid, blkMetaData blk) | BlockWithTicket blk blkid _ <- blks]
                  client' = idle unackedSeq'' lastIdx'
               in (blks', client')

      -- Grab info about any new txs after the last tx idx we've seen,
      -- up to the number that the peer has requested.
      case blocking of
        SingBlocking -> do
          when (reqNo == 0) $
            throw ProtocolErrorRequestedNothing
          unless (Seq.null unackedSeq') $
            throw ProtocolErrorRequestBlocking

          blkids <- atomically $ do
            blkq <- readTVar buffer
            let blkids = takeAfterTicket blkq lastIdx
            when (null $ blkids) retry
            pure $ take (fromIntegral reqNo) blkids

          let !(blkids', client') = update blkids
              blkids'' = case NonEmpty.nonEmpty blkids' of
                Just x -> x
                -- Assert blkids is non-empty: we blocked until blkids was non-null,
                -- and we know reqNo > 0, hence `take reqNo blkids` is non-null.
                Nothing -> error "blkidsubmissionOutbound: empty transaction's list"
          return (TC.Yield (MsgReplyBlkIds (BlockingReply blkids'')) client')
        SingNonBlocking -> do
          when (reqNo == 0 && ackNo == 0) $
            throw ProtocolErrorRequestedNothing
          when (Seq.null unackedSeq') $
            throw ProtocolErrorRequestNonBlocking

          blkids <- atomically $ do
            blkq <- readTVar buffer
            let blkids = takeAfterTicket blkq lastIdx
            return (take (fromIntegral reqNo) blkids)

          let !(blkids', client') = update blkids
          pure (TC.Yield (MsgReplyBlkIds (NonBlockingReply blkids')) client')
    MsgRequestBlks blkids -> TC.Effect $ do
      blkq <- atomically $ readTVar buffer

      -- The window size is expected to be small (currently 10) so the find is acceptable.
      -- TODO Andrea: is `10` good enough for freshest first?
      let blkidxs = [find (\(t, _) -> t == blkid) unackedSeq | blkid <- blkids]
          blkidxs' = map snd $ catMaybes blkidxs

      when (any isNothing blkidxs) $
        throw ProtocolErrorRequestedUnavailableBlk

      -- The 'lookupByTicket' call will return nothing if the block is no
      -- longer in the buffer. This is good. Neither the sending nor
      -- receiving side wants to forward blks that are no longer of interest.
      let txs = mapMaybe (lookupByTicket blkq) blkidxs'
          client' = idle unackedSeq lastIdx

      return $ TC.Yield (MsgReplyBlks txs) client'
