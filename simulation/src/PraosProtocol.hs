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
data SlotNo
data BlockId
data BlockHeader
type ChainTip = Point

data Point = Point BlockId SlotNo -- could be just the slot?

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

data StateCanRoll (st :: ChainSyncState) where
  IsCanAwait :: StateCanRoll StCanAwait
  IsMustReply :: StateCanRoll StMustReply

instance Protocol ChainSyncState where
  data Message ChainSyncState from to where
    MsgRequestNext :: Message ChainSyncState StIdle StCanAwait
    MsgAwaitReply :: Message ChainSyncState StCanAwait StMustReply
    MsgRollForward ::
      StateCanRoll st ->
      BlockHeader ->
      ChainTip ->
      Message ChainSyncState st StIdle
    MsgRollBackward ::
      StateCanRoll st ->
      Point ->
      ChainTip ->
      Message ChainSyncState st StIdle
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

data ReadPointer = ReadPointer {point :: Point, isBackward :: Bool}
type MonadSyncProducer m = MonadSTM m -- TODO

data NodeEvent = NewBlock | ChainSwitch

instance Semigroup NodeEvent where
  _ <> ChainSwitch = ChainSwitch
  ChainSwitch <> _ = ChainSwitch
  NewBlock <> NewBlock = NewBlock

data ChainSyncProducerState m = ChainSyncProducerState
  { readPointer :: TVar m ReadPointer
  , ownChainTip :: TVar m ChainTip -- TODO: Read-only. Make newtype
  , mailbox :: TMVar m NodeEvent
  }

onPar :: Point -> ChainTip -> Bool
onPar = undefined

nextPointAndHeader :: MonadSyncProducer m => ChainSyncProducerState m -> Point -> STM m (Point, BlockHeader)
nextPointAndHeader = undefined

checkMail :: MonadSyncProducer m => ChainSyncProducerState m -> Bool -> STM m ()
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
      checkMail st False
      rp <- readTVar readPointer
      tip <- readTVar ownChainTip
      if
          | point rp `onPar` tip -> do
              when (isBackward rp) $ writeTVar readPointer rp{isBackward = False}
              return $ TS.Yield MsgAwaitReply mustReply
          | isBackward rp -> do
              writeTVar readPointer rp{isBackward = False}
              return $ TS.Yield (MsgRollBackward IsCanAwait (point rp) tip) idle
          | otherwise -> do
              (nextPoint, header) <- nextPointAndHeader st (point rp)
              writeTVar readPointer $ ReadPointer nextPoint False
              return $ TS.Yield (MsgRollForward IsCanAwait header tip) idle
    MsgFindIntersect points -> undefined
  mustReply :: TS.Server ChainSyncState 'NonPipelined 'StMustReply m ()
  mustReply = TS.Effect $ atomically $ do
    checkMail st True
    undefined -- TODO: like MsgRequestNext
