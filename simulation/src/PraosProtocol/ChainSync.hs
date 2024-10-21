{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module PraosProtocol.ChainSync where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (..),
 )
import Control.Exception (assert)
import Data.Maybe (fromMaybe)
import Data.Type.Equality ((:~:) (Refl))
import Network.TypedProtocol (
  Agency (ClientAgency, NobodyAgency, ServerAgency),
  IsPipelined (NonPipelined),
  Protocol (..),
  StateTokenI (..),
 )
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS
import PraosProtocol.Common
import qualified PraosProtocol.Common.Chain as Chain

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

decideSingChainSyncState ::
  SingChainSyncState st ->
  SingChainSyncState st' ->
  Maybe (st :~: st')
decideSingChainSyncState SingStIdle SingStIdle = Just Refl
decideSingChainSyncState SingStCanAwait SingStCanAwait = Just Refl
decideSingChainSyncState SingStMustReply SingStMustReply = Just Refl
decideSingChainSyncState SingStIntersect SingStIntersect = Just Refl
decideSingChainSyncState SingStDone SingStDone = Just Refl
decideSingChainSyncState _ _ = Nothing

decideChainSyncState ::
  forall (st :: ChainSyncState) (st' :: ChainSyncState).
  (StateTokenI st, StateTokenI st') =>
  Maybe (st :~: st')
decideChainSyncState = decideSingChainSyncState stateToken stateToken

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

deriving instance Show (Message ChainSyncState from to)

instance MessageSize (Message ChainSyncState st st') where
  messageSizeBytes = \case
    MsgRequestNext -> 1
    MsgAwaitReply -> 1
    MsgRollForward_StCanAwait hdr tip -> messageSizeBytes hdr + messageSizeBytes tip
    MsgRollBackward_StCanAwait pt tip -> messageSizeBytes pt + messageSizeBytes tip
    MsgRollForward_StMustReply hdr tip -> messageSizeBytes hdr + messageSizeBytes tip
    MsgRollBackward_StMustReply pt tip -> messageSizeBytes pt + messageSizeBytes tip
    MsgFindIntersect pts -> sum (messageSizeBytes <$> pts)
    MsgIntersectFound pt tip -> messageSizeBytes pt + messageSizeBytes tip
    MsgIntersectNotFound tip -> messageSizeBytes tip
    MsgDone -> 1

chainSyncMessageLabel :: Message ChainSyncState st st' -> String
chainSyncMessageLabel = \case
  MsgRequestNext -> "MsgRequestNext"
  MsgAwaitReply -> "MsgAwaitReply"
  MsgRollForward_StCanAwait _ _ -> "MsgRollForward"
  MsgRollBackward_StCanAwait _ _ -> "MsgRollBackward"
  MsgRollForward_StMustReply _ _ -> "MsgRollForward"
  MsgRollBackward_StMustReply _ _ -> "MsgRollBackward"
  MsgFindIntersect _ -> "MsgFindIntersect"
  MsgIntersectFound _ _ -> "MsgIntersectFound"
  MsgIntersectNotFound _ -> "MsgIntersectNotFound"
  MsgDone -> "MsgDone"

instance StateTokenI StIdle where stateToken = SingStIdle
instance StateTokenI StCanAwait where stateToken = SingStCanAwait
instance StateTokenI StMustReply where stateToken = SingStMustReply
instance StateTokenI StIntersect where stateToken = SingStIntersect
instance StateTokenI StDone where stateToken = SingStDone

--------------------------------
---- ChainSync Consumer
--------------------------------

type ChainConsumer st m a = TC.Client ChainSyncState 'NonPipelined st m a

chainConsumer ::
  forall m.
  MonadSTM m =>
  TVar m (Chain BlockHeader) ->
  ChainConsumer 'StIdle m ()
chainConsumer hchainVar = idle True
 where
  -- NOTE: The specification says to do an initial intersection with
  --       exponentially spaced points, and perform binary search to
  --       narrow down the actual intersection point from there on.
  --       However, the real implementation only does the first step.
  idle :: Bool -> ChainConsumer 'StIdle m ()
  idle initialise
    | initialise = TC.Effect $ atomically $ do
        hchain <- readTVar hchainVar
        let recentOffsets = [0, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584]
        let hpoints = Chain.selectPoints recentOffsets hchain
        return $ TC.Yield (MsgFindIntersect hpoints) intersect
    | otherwise = TC.Yield MsgRequestNext canAwait

  intersect :: ChainConsumer 'StIntersect m ()
  intersect = TC.Await $ \case
    MsgIntersectFound hpoint _tip -> rollBackward hpoint
    MsgIntersectNotFound _htip -> rollBackward GenesisPoint

  canAwait :: ChainConsumer 'StCanAwait m ()
  canAwait = TC.Await $ \case
    MsgAwaitReply -> mustReply
    MsgRollForward_StCanAwait header _htip -> rollForward header
    MsgRollBackward_StCanAwait hpoint _htip -> rollBackward hpoint

  mustReply :: ChainConsumer 'StMustReply m ()
  mustReply = TC.Await $ \case
    MsgRollForward_StMustReply header _htip -> rollForward header
    MsgRollBackward_StMustReply hpoint _htip -> rollBackward hpoint

  rollForward :: BlockHeader -> ChainConsumer 'StIdle m ()
  rollForward header =
    TC.Effect $ atomically $ do
      modifyTVar' hchainVar $ Chain.addBlock header
      return $ idle False

  rollBackward :: Point BlockHeader -> ChainConsumer 'StIdle m ()
  rollBackward hpoint =
    TC.Effect $ atomically $ do
      modifyTVar' hchainVar $
        fromMaybe (error "chainConsumer: MsgRollBackward with point not on chain")
          . Chain.rollback hpoint
      return $ idle False

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
            let htip = castTip (Chain.headTip (chainState st'))
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
          let htip = castTip (Chain.headTip (chainState st'))
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
    let htip = castTip (Chain.headTip (chainState st))
    assert (followerExists followerId st) $
      case findFirstPoint (castPoint <$> hpoints) st of
        Nothing -> do
          return $ TS.Yield (MsgIntersectNotFound htip) idle
        Just bpoint -> do
          let hpoint = castPoint bpoint
          writeTVar stVar $ setFollowerPoint followerId bpoint st
          return $ TS.Yield (MsgIntersectFound hpoint htip) idle
