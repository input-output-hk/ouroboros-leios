{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module PraosProtocol.ChainSync where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (..),
 )
import Control.Exception (assert)
import Network.TypedProtocol (
  Agency (ClientAgency, NobodyAgency, ServerAgency),
  IsPipelined (NonPipelined),
  Protocol (..),
  StateTokenI (..),
 )
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS
import PraosProtocol.Types

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
      Tip BlockHeader ->
      Message ChainSyncState StCanAwait StIdle
    MsgRollBackward_StCanAwait ::
      Point BlockHeader ->
      Tip BlockHeader ->
      Message ChainSyncState StCanAwait StIdle
    MsgRollForward_StMustReply ::
      BlockHeader ->
      Tip BlockHeader ->
      Message ChainSyncState StMustReply StIdle
    MsgRollBackward_StMustReply ::
      Point BlockHeader ->
      Tip BlockHeader ->
      Message ChainSyncState StMustReply StIdle
    MsgFindIntersect ::
      [Point BlockHeader] ->
      Message ChainSyncState StIdle StIntersect
    MsgIntersectFound ::
      Point BlockHeader ->
      Tip BlockHeader ->
      Message ChainSyncState StIntersect StIdle
    MsgIntersectNotFound ::
      Tip BlockHeader ->
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

--------------------------------
---- ChainSync Consumer
--------------------------------

-- type ChainConsumer st m a = TC.Client ChainSyncState 'NonPipelined st m a

-- chainConsumer ::
--   forall m.
--   MonadSTM m =>
--   TVar m (Chain BlockHeader) ->
--   ChainConsumer 'StIdle m ()
-- chainConsumer chainVar = initialise
--  where
--   initialise :: ChainConsumer 'StIdle m ()
--   initialise = TC.Effect $ atomically $ do
--     chain <- readTVar chainVar
--     points <- selectPoints recentOffsets chain
--     return $ TC.Yield (MsgFindIntersect points) intersect
--    where
--     recentOffsets :: [Int]
--     recentOffsets = [0, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584]

--   intersect :: ChainConsumer 'StIntersect m ()
--   intersect = TC.Await $ \case
--     MsgIntersectFound point _tip -> _
--     MsgIntersectNotFound tip -> _

--   requestNext :: ChainConsumer 'StIdle m ()
--   requestNext = _

--------------------------------
---- ChainSync Producer
--------------------------------

type ChainProducer st m a = TS.Server ChainSyncState 'NonPipelined st m a

chainProducer ::
  forall m.
  MonadSTM m =>
  FollowerId ->
  TVar m (ChainProducerState Block) ->
  ChainProducer StIdle m ()
chainProducer followerId stVar = idle
 where
  idle :: ChainProducer 'StIdle m ()
  idle = TS.Await $ \case
    MsgDone -> TS.Done ()
    MsgRequestNext -> TS.Effect $ atomically $ do
      st <- readTVar stVar
      assert (followerExists followerId st) $
        case followerInstruction followerId st of
          Nothing -> do
            return $ TS.Yield MsgAwaitReply mustReply
          Just (chainUpdate, st') -> do
            writeTVar stVar st'
            let htip = castTip (headTip (chainState st'))
            case chainUpdate of
              AddBlock block -> do
                let header = blockHeader block
                return $ TS.Yield (MsgRollForward_StCanAwait header htip) idle
              RollBack bpoint -> do
                let hpoint = castPoint bpoint
                return $ TS.Yield (MsgRollBackward_StCanAwait hpoint htip) idle
    MsgFindIntersect points -> intersect points

  mustReply :: ChainProducer 'StMustReply m ()
  mustReply = TS.Effect $ atomically $ do
    st <- readTVar stVar
    assert (followerExists followerId st) $
      case followerInstruction followerId st of
        Nothing -> retry
        Just (chainUpdate, st') -> do
          writeTVar stVar st'
          let htip = castTip (headTip (chainState st'))
          case chainUpdate of
            AddBlock block -> do
              let header = blockHeader block
              return $ TS.Yield (MsgRollForward_StMustReply header htip) idle
            RollBack bpoint -> do
              let hpoint = castPoint bpoint
              return $ TS.Yield (MsgRollBackward_StMustReply hpoint htip) idle

  intersect :: [Point BlockHeader] -> ChainProducer 'StIntersect m ()
  intersect hpoints = TS.Effect $ atomically $ do
    st <- readTVar stVar
    let htip = castTip (headTip (chainState st))
    assert (followerExists followerId st) $
      case findFirstPoint (castPoint <$> hpoints) st of
        Nothing -> do
          return $ TS.Yield (MsgIntersectNotFound htip) idle
        Just bpoint -> do
          let hpoint = castPoint bpoint
          writeTVar stVar $ setFollowerPoint followerId bpoint st
          return $ TS.Yield (MsgIntersectFound hpoint htip) idle
