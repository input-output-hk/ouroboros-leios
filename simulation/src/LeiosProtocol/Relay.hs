{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module LeiosProtocol.Relay where

import ChanDriver (ProtocolMessage)
import Control.Concurrent.Class.MonadSTM (MonadSTM (..))
import Control.DeepSeq (NFData)
import Control.Exception (Exception, assert, throw)
import Control.Monad (forM_, when)
import Control.Monad.Class.MonadTimer (MonadDelay)
import Data.Bits (Bits, FiniteBits)
import qualified Data.Foldable as Foldable
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe (isJust, isNothing, mapMaybe)
import Data.Monoid (Sum (..))
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as Seq
import Data.Singletons (Sing, SingI (..))
import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word16)
import GHC.Generics (Generic)
import LeiosProtocol.RelayBuffer (RelayBuffer)
import qualified LeiosProtocol.RelayBuffer as RB
import Network.TypedProtocol (
  Agency (ClientAgency, NobodyAgency, ServerAgency),
  IsPipelined (..),
  Protocol (..),
  StateTokenI (..),
 )
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS
import NoThunks.Class (NoThunks)
import Quiet (Quiet (..))

data BlockingStyle
  = StBlocking
  | StNonBlocking
  deriving (Show, Eq)

type SingBlockingStyle :: BlockingStyle -> Type
data SingBlockingStyle blocking where
  SingBlocking :: SingBlockingStyle StBlocking
  SingNonBlocking :: SingBlockingStyle StNonBlocking

deriving instance Show (SingBlockingStyle blocking)

type instance Sing @BlockingStyle = SingBlockingStyle

instance SingI StBlocking where sing = SingBlocking
instance SingI StNonBlocking where sing = SingNonBlocking

withSingIBlockingStyle :: SingBlockingStyle blocking -> (SingI blocking => a) -> a
withSingIBlockingStyle SingBlocking = id
withSingIBlockingStyle SingNonBlocking = id

decideSingBlockingStyle ::
  SingBlockingStyle st ->
  SingBlockingStyle st' ->
  Maybe (st :~: st')
decideSingBlockingStyle SingBlocking SingBlocking = Just Refl
decideSingBlockingStyle SingNonBlocking SingNonBlocking = Just Refl
decideSingBlockingStyle _ _ = Nothing

isBlocking :: SingBlockingStyle blocking -> Bool
isBlocking = isJust . decideSingBlockingStyle SingBlocking

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
type RelayState :: Type -> Type -> Type -> Type
data RelayState id header body
  = -- | Initial protocol message.
    StInit
  | -- | The server (inbound side) has agency; it can either terminate, ask for
    -- transaction identifiers or ask for transactions.
    --
    -- There is no timeout in this state.
    StIdle
  | -- | The client (outbound side) has agency; it must reply with a
    -- list of transaction identifiers that it wishes to submit.
    --
    -- There are two sub-states for this, for blocking and non-blocking cases.
    StHeaders BlockingStyle
  | -- | The client (outbound side) has agency; it must reply with the list of
    -- transactions.
    StBodies
  | -- | Nobody has agency; termination state.
    StDone

data SingRelayState (st :: RelayState id header body) where
  SingStInit :: SingRelayState StInit
  SingStIdle :: SingRelayState StIdle
  SingStHeaders :: Sing blocking -> SingRelayState (StHeaders blocking)
  SingStBodies :: SingRelayState StBodies
  SingStDone :: SingRelayState StDone

decideSingRelayState ::
  SingRelayState st ->
  SingRelayState st' ->
  Maybe (st :~: st')
decideSingRelayState SingStInit SingStInit = Just Refl
decideSingRelayState SingStIdle SingStIdle = Just Refl
decideSingRelayState (SingStHeaders b1) (SingStHeaders b2) =
  fmap (\Refl -> Refl) (decideSingBlockingStyle b1 b2)
decideSingRelayState SingStBodies SingStBodies = Just Refl
decideSingRelayState SingStDone SingStDone = Just Refl
decideSingRelayState _ _ = Nothing

instance StateTokenI StInit where stateToken = SingStInit
instance StateTokenI StIdle where stateToken = SingStIdle
instance SingI blocking => StateTokenI (StHeaders blocking) where stateToken = SingStHeaders sing
instance StateTokenI StBodies where stateToken = SingStBodies
instance StateTokenI StDone where stateToken = SingStDone

decideRelayState ::
  forall (id :: Type) (header :: Type) (body :: Type) (st :: RelayState id header body) (st' :: RelayState id header body).
  (StateTokenI st, StateTokenI st') =>
  Maybe (st :~: st')
decideRelayState = decideSingRelayState stateToken stateToken

newtype WindowShrink = WindowShrink {value :: Word16}
  deriving (Eq, Ord, NFData, Generic)
  deriving newtype (Num, Enum, Real, Integral, Bounded, Bits, FiniteBits, NoThunks)
  deriving (Semigroup) via (Sum Word16)
  deriving (Monoid) via (Sum Word16)
  deriving (Show) via (Quiet WindowShrink)

newtype WindowExpand = WindowExpand {value :: Word16}
  deriving (Eq, Ord, NFData, Generic)
  deriving newtype (Num, Enum, Real, Integral, Bounded, Bits, FiniteBits, NoThunks)
  deriving (Semigroup) via (Sum Word16)
  deriving (Monoid) via (Sum Word16)
  deriving (Show) via (Quiet WindowExpand)

type ResponseList :: BlockingStyle -> Type -> Type
data ResponseList blocking a where
  BlockingResponse :: NonEmpty a -> ResponseList StBlocking a
  NonBlockingResponse :: [a] -> ResponseList StNonBlocking a

deriving instance Eq a => Eq (ResponseList blocking a)
deriving instance Show a => Show (ResponseList blocking a)
deriving instance Functor (ResponseList blocking)
deriving instance Foldable (ResponseList blocking)

data RelayProtocolError
  = ShrankTooMuch WindowSize WindowShrink
  | ExpandTooMuch WindowSize WindowShrink WindowExpand
  | RequestedNoChange
  | RequestedUnknownId
  deriving (Show)

instance Exception RelayProtocolError

-- | There are some constraints of the protocol that are not captured in the
-- types of the messages, but are documented with the messages. Violation
-- of these constraints is also a protocol error. The constraints are intended
-- to ensure that implementations are able to work in bounded space.
instance Protocol (RelayState id header body) where
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
  data Message (RelayState id header body) from to where
    MsgInit ::
      Message (RelayState id header body) StInit StIdle
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
    MsgRequestHeaders ::
      SingBlockingStyle blocking ->
      WindowShrink ->
      WindowExpand ->
      Message (RelayState id header body) StIdle (StHeaders blocking)
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
    MsgRespondHeaders ::
      ResponseList blocking header ->
      Message (RelayState id header body) (StHeaders blocking) StIdle
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
    MsgRequestBodies ::
      [id] ->
      Message (RelayState id header body) StIdle StBodies
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
    MsgResponseBodies ::
      [body] ->
      Message (RelayState id header body) StBodies StIdle
    -- \| Termination message, initiated by the client when the server is
    -- making a blocking call for more block identifiers.
    MsgDone ::
      Message (RelayState id header body) (StHeaders StBlocking) StDone

  type StateAgency StInit = ClientAgency
  type StateAgency StIdle = ServerAgency
  type StateAgency (StHeaders _blocking) = ClientAgency
  type StateAgency StBodies = ClientAgency
  type StateAgency StDone = NobodyAgency

  type StateToken = SingRelayState

deriving instance (Show id, Show header, Show body) => Show (Message (RelayState id header body) from to)

-- finiteByteSize :: (Integral a, FiniteBits b) => b -> a
-- finiteByteSize x = ceiling (realToFrac (finiteBitSize x) / 8 :: Double)

-- instance
--   ( MessageSize id
--   , MessageSize header
--   , MessageSize body
--   ) =>
--   MessageSize (Message (RelayState id header body) from to)
--   where
--   messageSizeBytes MsgInit = 1
--   messageSizeBytes (MsgRequestHeaders blocking windowGrow windowShrink) =
--     messageSizeBytes blocking + finiteByteSize windowGrow + finiteByteSize windowShrink
--   messageSizeBytes (MsgRespondHeaders headers) = messageSizeBytes headers
--   messageSizeBytes (MsgRequestBodies ids) = sum $ map messageSizeBytes ids
--   messageSizeBytes (MsgRespondBodies bodies) = sum $ map messageSizeBytes bodies
--   messageSizeBytes MsgDone = 1

relayMessageLabel :: Message (RelayState id header body) st st' -> String
relayMessageLabel = \case
  MsgInit{} -> "MsgInit"
  MsgRequestHeaders{} -> "MsgRequestHeaders"
  MsgRespondHeaders{} -> "MsgRespondHeaders"
  MsgRequestBodies{} -> "MsgRequestBodies"
  MsgResponseBodies{} -> "MsgResponseBodies"
  MsgDone{} -> "MsgDone"

type RelayMessage id header body = ProtocolMessage (RelayState id header body)

--------------------------------
---- Relay Configuration
--------------------------------

newtype WindowSize = WindowSize {value :: Word16}
  deriving (Eq, Ord, NFData, Generic)
  deriving newtype (Num, Enum, Real, Integral, Bounded, Bits, FiniteBits, NoThunks)
  deriving (Semigroup) via (Sum Word16)
  deriving (Monoid) via (Sum Word16)
  deriving (Show) via (Quiet WindowSize)

newtype RelayConfig = RelayConfig
  { maxWindowSize :: WindowSize
  }

--------------------------------
---- Relay Producer
--------------------------------

data Window id = Window
  { values :: !(StrictSeq (id, RB.Ticket))
  , lastTicket :: !RB.Ticket
  }

emptyWindow :: Window id
emptyWindow = Window Seq.empty (RB.Ticket 0)

newtype RelayProducerState id header body m = RelayProducerState
  { relayBufferVar :: TVar m (RelayBuffer id (header, body))
  }

readEntriesAfterTicket ::
  MonadSTM m =>
  RelayProducerState id header body m ->
  SingBlockingStyle blocking ->
  WindowExpand ->
  RB.Ticket ->
  m (ResponseList blocking (RB.EntryWithTicket id (header, body)))
readEntriesAfterTicket state blocking windowExpand t = atomically $ do
  newEntries <-
    take (fromIntegral windowExpand)
      . (`RB.takeAfterTicket` t)
      <$> readTVar state.relayBufferVar
  assert (and [entry.ticket > t | entry <- newEntries]) $
    case blocking of
      SingBlocking ->
        maybe retry (return . BlockingResponse) (NonEmpty.nonEmpty newEntries)
      SingNonBlocking ->
        return $ NonBlockingResponse newEntries

type RelayProducer id header body st m a = TC.Client (RelayState id header body) 'NonPipelined st m a

relayProducer ::
  forall id header body m.
  (Ord id, MonadSTM m, MonadDelay m) =>
  RelayConfig ->
  RelayProducerState id header body m ->
  RelayProducer id header body 'StIdle m ()
relayProducer config state = idle emptyWindow
 where
  idle :: Window id -> TC.Client (RelayState id header body) 'NonPipelined 'StIdle m ()
  idle !window = TC.Await $ \case
    MsgRequestHeaders blocking windowShrink windowExpand -> TC.Effect $ do
      -- Validate the request:
      -- 1. windowShrink <= windowSize
      let windowSize = fromIntegral (Seq.length window.values)
      when @m (windowShrink.value > windowSize.value) $ do
        throw $ ShrankTooMuch windowSize windowShrink
      -- 2. windowSize - windowShrink + windowExpand <= maxWindowSize
      let newWindowSize = WindowSize $ windowSize.value - windowShrink.value + windowExpand.value
      when (newWindowSize > config.maxWindowSize) $ do
        throw $ ExpandTooMuch windowSize windowShrink windowExpand
      -- 3. windowShrink, windowExpand /= 0 if non-blocking
      --    windowExpand /= 0 if blocking
      when (windowExpand.value == 0 && (isBlocking blocking || windowShrink.value == 0)) $ do
        throw RequestedNoChange
      -- Shrink the window:
      let keptValues =
            Seq.drop (fromIntegral windowShrink) window.values
      -- Find the new entries:
      newEntries <-
        readEntriesAfterTicket state blocking windowExpand window.lastTicket
      let newValues =
            Seq.fromList [(entry.key, entry.ticket) | entry <- Foldable.toList newEntries]
      let newLastTicket = case newValues of
            Seq.Empty -> window.lastTicket
            _ Seq.:|> (_, ticket) -> ticket
      let newWindow =
            Window{values = keptValues <> newValues, lastTicket = newLastTicket}
      let responseList =
            fmap (fst . (.value)) newEntries
      withSingIBlockingStyle blocking $ do
        return $ TC.Yield (MsgRespondHeaders responseList) (idle newWindow)
    MsgRequestBodies ids -> TC.Effect $ do
      -- Check that all ids are in the window:
      forM_ ids $ \id' -> do
        when (isNothing (Seq.findIndexL ((== id') . fst) window.values)) $ do
          throw RequestedUnknownId
      -- Read the bodies from the RelayBuffer:
      relayBuffer <- readTVarIO state.relayBufferVar
      let bodies = mapMaybe (fmap snd . RB.lookup relayBuffer) ids
      return $ TC.Yield (MsgResponseBodies bodies) (idle window)

--------------------------------
---- Relay Consumer
--------------------------------

data RelayConsumerState id header body m = RelayConsumerState {}

type RelayConsumer id header body st m a = TS.Server (RelayState id header body) 'NonPipelined st m a

relayConsumer ::
  forall id header body m.
  (MonadSTM m, MonadDelay m) =>
  RelayConsumerState id header body m ->
  RelayConsumer id header body 'StIdle m ()
relayConsumer = undefined
