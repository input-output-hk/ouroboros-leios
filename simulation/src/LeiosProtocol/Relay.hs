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
import Data.Bits (Bits, FiniteBits (..))
import qualified Data.Foldable as Foldable
import Data.Kind (Type)
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
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
  N (..),
  Nat (..),
  Protocol (..),
  StateTokenI (..),
 )
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS
import NoThunks.Class (NoThunks)
import PraosProtocol.Common
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

instance MessageSize (SingBlockingStyle blocking) where
  messageSizeBytes _ = 1

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

-- | The kind of the body-submission protocol, and the types of the
-- states in the protocol state machine.
--
-- We describe this protocol using the label \"client\" for the peer that is
-- submitting bodies, and \"server\" for the one receiving them. The
-- protocol is however pull based, so it is typically the server that has
-- agency in this protocol. This is the opposite of the chain sync and block
-- fetch protocols, but that makes sense because the information flow is also
-- reversed: submitting bodies rather than receiving headers and blocks.
--
-- Because these client\/server labels are somewhat confusing in this case, we
-- sometimes clarify by using the terms inbound and outbound. This refers to
-- whether bodies are flowing towards a peer or away, and thus indicates
-- what role the peer is playing.
type RelayState :: Type -> Type -> Type -> Type
data RelayState id header body
  = -- | Initial protocol message.
    StInit
  | -- | The server (inbound side) has agency; it can either terminate, ask for
    -- body identifiers or ask for bodies.
    --
    -- There is no timeout in this state.
    StIdle
  | -- | The client (outbound side) has agency; it must reply with a
    -- list of body identifiers that it wishes to submit.
    --
    -- There are two sub-states for this, for blocking and non-blocking cases.
    StHeaders BlockingStyle
  | -- | The client (outbound side) has agency; it must reply with the list of
    -- bodies.
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

instance MessageSize a => MessageSize (ResponseList blocking a) where
  messageSizeBytes = Foldable.sum . fmap messageSizeBytes

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
    MsgRespondBodies ::
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

finiteByteSize :: (Integral a, FiniteBits b) => b -> a
finiteByteSize x = ceiling (realToFrac (finiteBitSize x) / 8 :: Double)

instance
  ( MessageSize id
  , MessageSize header
  , MessageSize body
  ) =>
  MessageSize (Message (RelayState id header body) from to)
  where
  messageSizeBytes MsgInit = 1
  messageSizeBytes (MsgRequestHeaders blocking expand shrink) =
    messageSizeBytes blocking + finiteByteSize expand + finiteByteSize shrink
  messageSizeBytes (MsgRespondHeaders headers) = messageSizeBytes headers
  messageSizeBytes (MsgRequestBodies ids) = sum $ map messageSizeBytes ids
  messageSizeBytes (MsgRespondBodies bodies) = sum $ map messageSizeBytes bodies
  messageSizeBytes MsgDone = 1

relayMessageLabel :: Message (RelayState id header body) st st' -> String
relayMessageLabel = \case
  MsgInit{} -> "MsgInit"
  MsgRequestHeaders{} -> "MsgRequestHeaders"
  MsgRespondHeaders{} -> "MsgRespondHeaders"
  MsgRequestBodies{} -> "MsgRequestBodies"
  MsgRespondBodies{} -> "MsgRespondBodies"
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

newtype RelayProducerSharedState id header body m = RelayProducerSharedState
  { relayBufferVar :: ReadOnly (TVar m (RelayBuffer id (header, body)))
  }

data RelayProducerLocalState id = RelayProducerLocalState
  { window :: !(StrictSeq (id, RB.Ticket))
  , lastTicket :: !RB.Ticket
  }

initRelayProducerLocalState :: RelayProducerLocalState id
initRelayProducerLocalState = RelayProducerLocalState Seq.empty minBound

type RelayProducer id header body st m a = TC.Client (RelayState id header body) 'NonPipelined st m a

relayProducer ::
  forall id header body m.
  (Ord id, MonadSTM m, MonadDelay m) =>
  RelayConfig ->
  RelayProducerSharedState id header body m ->
  RelayProducer id header body 'StIdle m ()
relayProducer config sst = idle initRelayProducerLocalState
 where
  idle :: RelayProducerLocalState id -> TC.Client (RelayState id header body) 'NonPipelined 'StIdle m ()
  idle !lst = TC.Await $ \case
    MsgRequestHeaders blocking shrink expand -> TC.Effect $ do
      -- Validate the request:
      -- 1. shrink <= windowSize
      let windowSize = fromIntegral (Seq.length lst.window)
      when @m (shrink.value > windowSize.value) $ do
        throw $ ShrankTooMuch windowSize shrink
      -- 2. windowSize - shrink + expand <= maxWindowSize
      let newWindowSize = WindowSize $ windowSize.value - shrink.value + expand.value
      when (newWindowSize > config.maxWindowSize) $ do
        throw $ ExpandTooMuch windowSize shrink expand
      -- 3. shrink, expand /= 0 if non-blocking
      --    expand /= 0 if blocking
      when (expand.value == 0 && (isBlocking blocking || shrink.value == 0)) $ do
        throw RequestedNoChange
      -- Shrink the window:
      let keptValues = Seq.drop (fromIntegral shrink) lst.window
      -- Find the new entries:
      newEntries <- readNewEntries sst blocking expand lst.lastTicket
      -- Expand the window:
      let newValues = Seq.fromList [(e.key, e.ticket) | e <- Foldable.toList newEntries]
      let window' = keptValues <> newValues
      let lastTicket' = case newValues of
            Seq.Empty -> lst.lastTicket
            _ Seq.:|> (_, ticket) -> ticket
      let lst' = lst{window = window', lastTicket = lastTicket'}
      let responseList = fmap (fst . (.value)) newEntries
      -- Yield the new entries:
      withSingIBlockingStyle blocking $ do
        return $ TC.Yield (MsgRespondHeaders responseList) (idle lst')
    MsgRequestBodies ids -> TC.Effect $ do
      -- Check that all ids are in the window:
      -- NOTE: This is O(n^2) which is acceptable only if maxWindowSize is small.
      -- TODO: Andrea: is a maxWindowSize of 10 large enough for freshest first?
      forM_ ids $ \id' -> do
        when (isNothing (Seq.findIndexL ((== id') . fst) lst.window)) $ do
          throw RequestedUnknownId
      -- Read the bodies from the RelayBuffer:
      relayBuffer <- readReadOnlyTVarIO sst.relayBufferVar
      let bodies = mapMaybe (fmap snd . RB.lookup relayBuffer) ids
      return $ TC.Yield (MsgRespondBodies bodies) (idle lst)

readNewEntries ::
  MonadSTM m =>
  RelayProducerSharedState id header body m ->
  SingBlockingStyle blocking ->
  WindowExpand ->
  RB.Ticket ->
  m (ResponseList blocking (RB.EntryWithTicket id (header, body)))
readNewEntries sst blocking expand t = atomically $ do
  newEntries <-
    take (fromIntegral expand)
      . (`RB.takeAfterTicket` t)
      <$> readReadOnlyTVar sst.relayBufferVar
  assert (and [entry.ticket > t | entry <- newEntries]) $
    case blocking of
      SingBlocking ->
        case NonEmpty.nonEmpty newEntries of
          Nothing -> retry
          Just newEntries' ->
            return $ BlockingResponse newEntries'
      SingNonBlocking ->
        return $ NonBlockingResponse newEntries

--------------------------------
---- Relay Consumer
--------------------------------
data RelayConsumerConfig id header = RelayConsumerConfig
  { relay :: RelayConfig
  , prioritize :: Map id header -> [id]
  -- ^ returns a subset of keys, in order of what should be fetched first.
  }

newtype RelayConsumerSharedState id header body m = RelayConsumerSharedState
  { relayBufferVar :: ReadOnly (TVar m (RelayBuffer id (header, body)))
  }

-- | Information maintained internally in the 'txSubmissionInbound' server
-- implementation.
type RelayConsumerLocalState :: Type -> Type -> Type -> N -> Type
data RelayConsumerLocalState id header body n = RelayConsumerLocalState
  { pendingRequests :: Nat n
  , pendingExpand :: !WindowExpand
  -- ^ The number of headers that we have requested but
  -- which have not yet been replied to. We need to track this it keep
  -- our requests within the maximum window size.
  , pendingShrink :: !WindowShrink
  -- ^ The number of bodies we can acknowledge on our next request
  -- for more bodies. The number here have already been removed from
  -- 'window'.
  , window :: !(StrictSeq id)
  -- ^ Those bodies (by their identifier) that the client has told
  -- us about, and which we have not yet acknowledged. This is kept in
  -- the order in which the client gave them to us. This is the same order
  -- in which we submit them to the mempool (or for this example, the final
  -- result order). It is also the order we acknowledge in.
  , available :: !(Map id header)
  -- ^ Those bodies (by their identifier) that we can request. These
  -- are a subset of the 'window' that we have not yet
  -- requested. This is not ordered to illustrate the fact that we can
  -- request bodies out of order. We also remember their header.
  , buffer :: !(Map id (Maybe (header, body)))
  -- ^ Bodies we have successfully downloaded but have not yet added
  -- to the mempool or acknowledged. This needed because we can request
  -- bodies out of order but must use the original order when adding
  -- to the mempool or acknowledging bodies.
  --
  -- However, it's worth noting that, in a few situations, some of the
  -- IDs in this 'Map' may be mapped to 'Nothing':
  --
  -- * IDs mapped to 'Nothing' can represent IDs
  --   that were requested, but not received. This can occur because the
  --   client will not necessarily send all of the bodies that we
  --   asked for, but we still need to acknowledge those bodies.
  --
  --   For example, if we request a body that no longer exists in
  --   the client's mempool, the client will just exclude it from the
  --   response. However, we still need to acknowledge it (i.e. remove it
  --   from the 'window') in order to note that we're no
  --   longer awaiting receipt of that body.
  --
  -- * IDs mapped to 'Nothing' can represent bodies
  --   that were not requested from the client because they're already
  --   in the mempool.
  --
  --   For example, if we request some IDs and notice that
  --   some subset of them have are already in the mempool, we wouldn't
  --   want to bother asking for those specific bodies. Therefore,
  --   we would just insert those IDs mapped to 'Nothing' to
  --   the 'buffer' such that those bodies are acknowledged,
  --   but never actually requested.
  }
  deriving (Show, Generic)

initRelayConsumerLocalState :: RelayConsumerLocalState id header body Z
initRelayConsumerLocalState =
  RelayConsumerLocalState
    { pendingRequests = Zero
    , pendingExpand = 0
    , pendingShrink = 0
    , window = Seq.empty
    , available = Map.empty
    , buffer = Map.empty
    }

data Collect id header body
  = CollectHeaders WindowExpand [header]
  | CollectBodies [id] [body]

type RelayConsumer id header body n st m a = TS.Server (RelayState id header body) ('Pipelined n (Collect id header body)) st m a

type RelayConsumerPipelined id header body st m a = TS.ServerPipelined (RelayState id header body) st m a

relayConsumerPipelined ::
  forall id header body m.
  (Ord id, MonadSTM m, MonadDelay m) =>
  RelayConsumerConfig id header ->
  RelayConsumerSharedState id header body m ->
  RelayConsumerPipelined id header body 'StInit m ()
relayConsumerPipelined config sst =
  TS.ServerPipelined $
    TS.Await @_ @('Pipelined TS.Z (Collect id header body)) $ \case
      MsgInit -> idle initRelayConsumerLocalState
 where
  maxHeadersToRequest = 3 :: Word16
  maxBodiesToRequest = 2 :: Word16

  idle ::
    RelayConsumerLocalState id header body n ->
    RelayConsumer id header body n 'StIdle m ()
  idle lst = case lst.pendingRequests of
    Zero
      | canRequestMoreBodies -> do
          -- There are no replies in flight, but we do know some more bodies we
          -- can ask for, so lets ask for them and more headers.
          requestBodies lst
      | otherwise -> do
          -- There's no replies in flight, and we have no more txs we can
          -- ask for so the only remaining thing to do is to ask for more
          -- txids. Since this is the only thing to do now, we make this a
          -- blocking call.
          assert
            ( lst.pendingExpand == 0
                && Seq.null lst.window
                && Map.null lst.available
                && Map.null lst.buffer
            )
            $ requestHeadersBlocking lst
    Succ pendingRequests'
      | canRequestMoreBodies -> do
          -- We have replies in flight and we should eagerly collect them if
          -- available, but there are bodies to request too so we
          -- should not block waiting for replies.
          --
          -- Having requested more bodies, we opportunistically ask
          -- for more headers in a non-blocking way. This is how we pipeline
          -- asking for both bodies and headers.
          --
          -- It's important not to pipeline more requests for headers when we
          -- have no bodies to ask for, since (with no other guard) this will
          -- put us into a busy-polling loop.
          let lst' = lst{pendingRequests = pendingRequests'}
          TS.Collect (Just (requestBodies lst)) (handleResponse lst')
      | otherwise -> do
          -- In this case there is nothing else to do so we block until we
          -- collect a reply.
          let lst' = lst{pendingRequests = pendingRequests'}
          TS.Collect Nothing (handleResponse lst')
   where
    canRequestMoreBodies = not (Map.null lst.available)

  done ::
    RelayConsumerLocalState id header body Z ->
    RelayConsumer id header body Z 'StDone m ()
  done _lst = TS.Done ()

  requestBodies ::
    forall (n :: N).
    RelayConsumerLocalState id header body n ->
    RelayConsumer id header body n 'StIdle m ()
  requestBodies lst = do
    let idsToRequest = take (fromIntegral maxBodiesToRequest) $ config.prioritize lst.available
    let available' = List.foldl' (flip Map.delete) lst.available idsToRequest
    let lst' = lst{pendingRequests = Succ lst.pendingRequests, available = available'}
    TS.YieldPipelined
      (MsgRequestBodies idsToRequest)
      ( TS.ReceiverAwait $ \case
          MsgRespondBodies bodies ->
            TS.ReceiverDone (CollectBodies idsToRequest bodies)
      )
      (requestHeadersNonBlocking lst')

  windowAdjust ::
    forall (n :: N).
    RelayConsumerLocalState id header body n ->
    (WindowShrink, WindowExpand)
  windowAdjust lst = (windowShrink, windowExpand)
   where
    windowSize = WindowSize $ fromIntegral (Seq.length lst.window) + lst.pendingExpand.value
    windowShrink = lst.pendingShrink
    windowExpand = WindowExpand $ maxHeadersToRequest `min` config.relay.maxWindowSize.value - windowSize.value

  requestHeadersNonBlocking ::
    forall (n :: N).
    RelayConsumerLocalState id header body n ->
    RelayConsumer id header body n 'StIdle m ()
  requestHeadersNonBlocking lst = do
    let (windowShrink, windowExpand) = windowAdjust lst
    TS.YieldPipelined
      (MsgRequestHeaders SingNonBlocking windowShrink windowExpand)
      ( TS.ReceiverAwait $ \case
          MsgRespondHeaders (NonBlockingResponse headers) ->
            TS.ReceiverDone (CollectHeaders windowExpand headers)
      )
      ( idle
          lst
            { pendingRequests = Succ lst.pendingRequests
            , pendingShrink = 0
            , pendingExpand = lst.pendingExpand + windowExpand
            }
      )

  requestHeadersBlocking ::
    RelayConsumerLocalState id header body Z ->
    RelayConsumer id header body Z 'StIdle m ()
  requestHeadersBlocking lst = do
    let (windowShrink, windowExpand) = windowAdjust lst
    TS.Yield (MsgRequestHeaders SingBlocking windowShrink windowExpand) $
      assert (lst.pendingExpand == 0) $ do
        let lst' = lst{pendingShrink = 0, pendingExpand = windowExpand}
        TS.Await $ \case
          MsgDone -> done lst'
          MsgRespondHeaders (BlockingResponse headers) ->
            handleResponse lst' $
              CollectHeaders windowExpand (NonEmpty.toList headers)

  handleResponse ::
    forall (n :: N).
    RelayConsumerLocalState id header body n ->
    Collect id header body ->
    RelayConsumer id header body n 'StIdle m ()
  handleResponse lst = \case
    CollectHeaders windowExpand idsAndHeaders -> do
      _
    CollectBodies ids bodies -> do
      _
