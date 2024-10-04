{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module PraosProtocol where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TMVar,
    TVar,
    atomically,
    modifyTVar',
    newTVarIO,
    readTVar,
    readTVarIO,
    retry,
    takeTMVar,
    tryTakeTMVar,
    writeTVar
  ),
 )
import Control.Monad (when)
import Network.TypedProtocol
import Network.TypedProtocol.Peer.Server as TS

--------------------------------
--- Common types
--------------------------------

-- TODO
data Slot
data BlockId
data BlockHeader
type ChainTip = Point

-- TODO: Could points just be the slot?
data Point = Point
  { pointSlot :: Slot
  , pointBlockId :: BlockId
  }

--------------------------------
---- ChainSync
--------------------------------

data ChainSyncState
  = StIdle
  | StCanAwait
  | StMustReply
  | StIntersect
  | StDone

data SingChainSyncState (st :: ChainSyncState) where
  SingStIdle :: SingChainSyncState StIdle
  SingStCanAwait :: SingChainSyncState StCanAwait
  SingStMustReply :: SingChainSyncState StMustReply
  SingStIntersect :: SingChainSyncState StIntersect
  SingStDone :: SingChainSyncState StDone

instance Protocol ChainSyncState where
  data Message ChainSyncState from to where
    MsgRequestNext :: Message ChainSyncState StIdle StCanAwait
    MsgAwaitReply :: Message ChainSyncState StCanAwait StMustReply
    MsgRollForward_StCanAwait ::
      BlockHeader ->
      ChainTip ->
      Message ChainSyncState StCanAwait StIdle
    MsgRollBackward_StCanAwait ::
      Point ->
      ChainTip ->
      Message ChainSyncState StCanAwait StIdle
    MsgRollForward_StMustReply ::
      BlockHeader ->
      ChainTip ->
      Message ChainSyncState StMustReply StIdle
    MsgRollBackward_StMustReply ::
      Point ->
      ChainTip ->
      Message ChainSyncState StMustReply StIdle
    MsgFindIntersect ::
      [Point] ->
      Message ChainSyncState StIdle StIntersect
    MsgIntersectFound ::
      Point ->
      ChainTip ->
      Message ChainSyncState StIntersect StIdle
    MsgIntersectNotFound ::
      ChainTip ->
      Message ChainSyncState StIntersect StIdle
    MsgDone :: Message ChainSyncState StIdle StDone
  type StateAgency StIdle = ClientAgency
  type StateAgency StCanAwait = ServerAgency
  type StateAgency StMustReply = ServerAgency
  type StateAgency StIntersect = ServerAgency
  type StateAgency StDone = NobodyAgency
  type StateToken = SingChainSyncState

instance StateTokenI StIdle where stateToken = SingStIdle
instance StateTokenI StCanAwait where stateToken = SingStCanAwait
instance StateTokenI StMustReply where stateToken = SingStMustReply
instance StateTokenI StIntersect where stateToken = SingStIntersect
instance StateTokenI StDone where stateToken = SingStDone

-- Where the consumer is at, in reading our chain.

type MonadSyncProducer m = MonadSTM m -- TODO

data NodeEvent
  = EvtNewBlock
  | EvtChainSwitch

instance Semigroup NodeEvent where
  _ <> EvtChainSwitch = EvtChainSwitch
  EvtChainSwitch <> _ = EvtChainSwitch
  EvtNewBlock <> EvtNewBlock = EvtNewBlock

data ChainSyncProducerState m = ChainSyncProducerState
  { readPointer :: TVar m Point
  , mailbox :: TMVar m NodeEvent
  , -- TODO: Needs read-only access to the whole chain
    chainTip :: TVar m ChainTip
  }

onPar :: Point -> ChainTip -> Bool
onPar = undefined

nextPointAndHeader :: MonadSyncProducer m => ChainSyncProducerState m -> Point -> STM m (Point, BlockHeader)
nextPointAndHeader = undefined

data Blocking = Blocking | NonBlocking
  deriving (Eq)
data Direction = Forward | Backward
  deriving (Eq)

-- TODO:
-- Check mailbox.
-- If EvtNewBlock, ignore. The point of this message is to wake you up.
-- If EvtChainSwitch, recompute read-pointer, return some information that says a chain switch happened.
checkMail :: MonadSyncProducer m => ChainSyncProducerState m -> Blocking -> STM m Direction
checkMail = undefined

chainSyncProducer ::
  forall m.
  MonadSyncProducer m =>
  ChainSyncProducerState m ->
  TS.Server ChainSyncState NonPipelined StIdle m ()
chainSyncProducer st@ChainSyncProducerState{..} = idle
 where
  idle :: TS.Server ChainSyncState NonPipelined StIdle m ()
  idle = TS.Await $ \case
    MsgDone -> TS.Done ()
    MsgRequestNext -> TS.Effect $ atomically $ do
      dir <- checkMail st NonBlocking
      pos <- readTVar readPointer
      tip <- readTVar chainTip
      if
        | pos `onPar` tip -> do
            return $ TS.Yield MsgAwaitReply mustReply
        | dir == Backward -> do
            return $ TS.Yield (MsgRollBackward_StCanAwait pos tip) idle
        | otherwise -> do
            (nextPos, nextHeader) <- nextPointAndHeader st pos
            writeTVar readPointer nextPos
            return $ TS.Yield (MsgRollForward_StCanAwait nextHeader tip) idle
    MsgFindIntersect points -> undefined

  mustReply :: TS.Server ChainSyncState 'NonPipelined 'StMustReply m ()
  mustReply = TS.Effect $ atomically $ do
    dir <- checkMail st Blocking
    pos <- readTVar readPointer
    tip <- readTVar chainTip
    if
      | pos `onPar` tip -> do
          return mustReply
      | dir == Backward -> do
          return $ TS.Yield (MsgRollBackward_StMustReply pos tip) idle
      | otherwise -> do
          (nextPos, nextHeader) <- nextPointAndHeader st pos
          writeTVar readPointer nextPos
          return $ TS.Yield (MsgRollForward_StMustReply nextHeader tip) idle
