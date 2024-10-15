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
      Tip Block ->
      Message ChainSyncState StCanAwait StIdle
    MsgRollBackward_StCanAwait ::
      Point Block ->
      Tip Block ->
      Message ChainSyncState StCanAwait StIdle
    MsgRollForward_StMustReply ::
      BlockHeader ->
      Tip Block ->
      Message ChainSyncState StMustReply StIdle
    MsgRollBackward_StMustReply ::
      Point Block ->
      Tip Block ->
      Message ChainSyncState StMustReply StIdle
    MsgFindIntersect ::
      [Point Block] ->
      Message ChainSyncState StIdle StIntersect
    MsgIntersectFound ::
      Point Block ->
      Tip Block ->
      Message ChainSyncState StIntersect StIdle
    MsgIntersectNotFound ::
      Tip Block ->
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

--------------------------------
---- ChainSync Producer
--------------------------------

chainProducer ::
  forall m.
  MonadSTM m =>
  FollowerId ->
  TVar m (ChainProducerState Block) ->
  TS.Server ChainSyncState NonPipelined StIdle m ()
chainProducer followerId stVar = idle
 where
  idle :: TS.Server ChainSyncState NonPipelined StIdle m ()
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
            let tip = headTip (chainState st')
            case chainUpdate of
              AddBlock block -> do
                let header = blockHeader block
                return $ TS.Yield (MsgRollForward_StCanAwait header tip) idle
              RollBack point -> do
                return $ TS.Yield (MsgRollBackward_StCanAwait point tip) idle
    MsgFindIntersect points -> intersect points

  mustReply :: TS.Server ChainSyncState 'NonPipelined 'StMustReply m ()
  mustReply = TS.Effect $ atomically $ do
    st <- readTVar stVar
    assert (followerExists followerId st) $
      case followerInstruction followerId st of
        Nothing -> retry
        Just (chainUpdate, st') -> do
          writeTVar stVar st'
          let tip = headTip (chainState st')
          case chainUpdate of
            AddBlock block -> do
              let header = blockHeader block
              return $ TS.Yield (MsgRollForward_StMustReply header tip) idle
            RollBack point -> do
              return $ TS.Yield (MsgRollBackward_StMustReply point tip) idle

  intersect :: [Point Block] -> TS.Server ChainSyncState 'NonPipelined 'StIntersect m ()
  intersect points = TS.Effect $ atomically $ do
    st <- readTVar stVar
    let tip = headTip (chainState st)
    assert (followerExists followerId st) $
      case findFirstPoint points st of
        Nothing -> do
          return $ TS.Yield (MsgIntersectNotFound tip) idle
        Just point -> do
          writeTVar stVar $ setFollowerPoint followerId point st
          return $ TS.Yield (MsgIntersectFound point tip) idle
