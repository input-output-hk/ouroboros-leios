{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module PraosProtocol.ChainSync where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TVar,
    atomically,
    readTVar,
    retry,
    writeTVar
  ),
 )
import Control.Monad (guard)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (lookup)
import Network.TypedProtocol (
  Agency (ClientAgency, NobodyAgency, ServerAgency),
  IsPipelined (NonPipelined),
  Protocol (..),
  StateTokenI (..),
 )
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS
import Ouroboros.Network.AnchoredFragment (AnchoredFragment)
import qualified Ouroboros.Network.AnchoredFragment as AF
import qualified Ouroboros.Network.Block as OAPI
import Ouroboros.Network.Mock.ConcreteBlock (
  Block (Block),
  BlockBody,
  BlockHeader,
 )
import Ouroboros.Network.Mock.ProducerState (
  ChainProducerState (..),
 )

--------------------------------
---- ChainSync
--------------------------------

data ChainProducerState
  = StIdle
  | StCanAwait
  | StMustReply
  | StIntersect
  | StDone

data SingChainSyncState (st :: ChainProducerState) where
  SingStIdle :: SingChainSyncState StIdle
  SingStCanAwait :: SingChainSyncState StCanAwait
  SingStMustReply :: SingChainSyncState StMustReply
  SingStIntersect :: SingChainSyncState StIntersect
  SingStDone :: SingChainSyncState StDone

instance Protocol ChainProducerState where
  data Message ChainProducerState from to where
    MsgRequestNext :: Message ChainProducerState StIdle StCanAwait
    MsgAwaitReply :: Message ChainProducerState StCanAwait StMustReply
    MsgRollForward_StCanAwait ::
      BlockHeader ->
      Tip ->
      Message ChainProducerState StCanAwait StIdle
    MsgRollBackward_StCanAwait ::
      Point ->
      Tip ->
      Message ChainProducerState StCanAwait StIdle
    MsgRollForward_StMustReply ::
      BlockHeader ->
      Tip ->
      Message ChainProducerState StMustReply StIdle
    MsgRollBackward_StMustReply ::
      Point ->
      Tip ->
      Message ChainProducerState StMustReply StIdle
    MsgFindIntersect ::
      [Point] ->
      Message ChainProducerState StIdle StIntersect
    MsgIntersectFound ::
      Point ->
      Tip ->
      Message ChainProducerState StIntersect StIdle
    MsgIntersectNotFound ::
      Tip ->
      Message ChainProducerState StIntersect StIdle
    MsgDone :: Message ChainProducerState StIdle StDone
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
  ChainProducerState m ->
  TS.Server ChainProducerState NonPipelined StIdle m ()
chainProducer st = idle
 where
  idle :: TS.Server ChainProducerState NonPipelined StIdle m ()
  idle = TS.Await $ \case
    MsgDone -> TS.Done ()
    MsgRequestNext -> TS.Effect $ atomically $ do
      handleLocalEvents NonBlocking >>= \case
        Forward -> do
          tryRollForward >>= \case
            Nothing -> do
              return $ TS.Yield MsgAwaitReply mustReply
            Just header' -> do
              tip <- getChainTip
              return $ TS.Yield (MsgRollForward_StCanAwait header' tip) idle
        Backward -> do
          (point, tip) <- (,) <$> getReadPointer <*> getChainTip
          return $ TS.Yield (MsgRollBackward_StCanAwait point tip) idle
    MsgFindIntersect points -> intersect points

  mustReply :: TS.Server ChainProducerState 'NonPipelined 'StMustReply m ()
  mustReply = TS.Effect $ atomically $ do
    handleLocalEvents Blocking >>= \case
      Forward -> do
        tryRollForward >>= \case
          Nothing -> do
            return mustReply
          Just header' -> do
            tip <- getChainTip
            return $ TS.Yield (MsgRollForward_StMustReply header' tip) idle
      Backward -> do
        (point, tip) <- (,) <$> getReadPointer <*> getChainTip
        return $ TS.Yield (MsgRollBackward_StMustReply point tip) idle

  intersect :: [Point] -> TS.Server ChainProducerState 'NonPipelined 'StIntersect m ()
  intersect points = TS.Effect $ atomically $ do
    -- NOTE: Should not call `handleLocalEvents` since it does not interact with
    --       the read-pointer and cannot handle chain-switch events.
    tip <- getChainTip
    findIntersectionWithPoints tip points >>= \case
      Nothing -> do
        return $ TS.Yield (MsgIntersectNotFound tip) idle
      Just point -> do
        setReadPointer point
        return $ TS.Yield (MsgIntersectFound point tip) idle

  -- Handles all local events that happened since the chain-sync producer last woke up.
  -- If there were only @EvtNewBlock@ events, ignore them. The purpose of this message is to wake blocking producers.
  -- If there were @EvtChainSwitch@ events, update the read-pointer and return the current direction.
  handleLocalEvents :: Blocking -> STM m Direction
  handleLocalEvents shouldBlock = do
    chainSwitched <- didChainSwitch shouldBlock
    if chainSwitched
      then do
        tip <- getChainTip
        point <- getReadPointer
        point' <- unsafeFindIntersection tip point
        if point == point'
          then do
            return Forward
          else do
            setReadPointer point'
            return Backward
      else do
        return Forward

  didChainSwitch :: Blocking -> STM m Bool
  didChainSwitch shouldBlock =
    (== Just EvtChainSwitch) <$> case shouldBlock of
      Blocking -> Just <$> takeTakeOnlyTMVar st . eventsVar
      NonBlocking -> tryTakeTakeOnlyTMVar st . eventsVar

  tryRollForward :: STM m (Maybe BlockHeader)
  tryRollForward = do
    point <- getReadPointer
    getNextPoint point >>= \case
      Nothing -> return Nothing
      Just point' -> do
        header' <- unsafeGetBlockHeader (pointBlockId point')
        setReadPointer point'
        return $ Just header'

  -- Traverse through chain by iterating `getPreviousPoint` on `chainTip`.
  -- For each step, update the intersection status @OnChain@ for each point:
  --
  -- + If a point has status @Yes@, it is known to intersect with the chain.
  -- + If a point has status @Unknown@, it is not known to intersect with the chain.
  -- + If a point is known not to intersect with the chain, it is dropped.
  --
  -- Once any @Point@ is known to intersect with the chain, any less-preferred points are dropped.
  --
  -- If the status of the most-preferred point is @Yes@, return it.
  -- Otherwise, when you reach the genesis block, return Nothing.
  --
  -- NOTE: The order of the points indicates preference and must be maintained.
  findIntersectionWithPoints :: Tip -> [Point] -> STM m (Maybe Point)
  findIntersectionWithPoints chainTip points =
    findIntersectionAcc chainTip (updateIntersectionStatusFor chainTip ((,Unknown) <$> points))
   where
    findIntersectionAcc :: Tip -> [(Point, OnChain)] -> STM m (Maybe Point)
    findIntersectionAcc _tip [] = return Nothing
    findIntersectionAcc _tip ((point, Yes) : _) = return (Just point)
    findIntersectionAcc tip pointsAndStatuses = do
      getPreviousPoint tip >>= \case
        Nothing -> return Nothing
        Just tip' -> findIntersectionAcc tip' (updateIntersectionStatusFor tip' pointsAndStatuses)

    updateIntersectionStatusFor :: Tip -> [(Point, OnChain)] -> [(Point, OnChain)]
    updateIntersectionStatusFor _ [] = []
    updateIntersectionStatusFor _ ((point, Yes) : _pointsAndStatuses) = [(point, Yes)]
    updateIntersectionStatusFor tip ((point, Unknown) : pointsAndStatuses)
      | point == tip = [(point, Yes)]
      | pointSlot tip < pointSlot point = updateIntersectionStatusFor tip pointsAndStatuses
      | otherwise = updateIntersectionStatusFor tip pointsAndStatuses

  getReadPointer :: STM m Point
  getReadPointer = readTVar st . readPointerVar

  setReadPointer :: Point -> STM m ()
  setReadPointer = writeTVar st . readPointerVar

  getChainTip :: STM m Tip
  getChainTip = readReadOnlyTVar st . chainTipVar

  -- PRECONDITION: All block IDs have headers.
  unsafeGetBlockHeader :: BlockId -> STM m BlockHeader
  unsafeGetBlockHeader blockId = do
    headers <- readReadOnlyTVar st . blockHeadersVar
    return $ headers Map.! blockId

  getNextPoint :: Point -> STM m (Maybe Point)
  getNextPoint point = do
    nextPoint <- Map.lookup point <$> (readReadOnlyTVar <=< readReadOnlyTVar) st . chainForwardsVarVar
    chainTip <- getChainTip -- NOTE: Only required for assertion
    assert (isJust nextPoint || point == chainTip) $ return nextPoint

  getPreviousPoint :: Point -> STM m (Maybe Point)
  getPreviousPoint point = do
    headers <- readReadOnlyTVar st . blockHeadersVar
    blockPrevPoint headers <$> unsafeGetBlockHeader (pointBlockId point)

  -- PRECONDITION: All chains share a genesis block.
  unsafeFindIntersection :: Tip -> Tip -> STM m Tip
  unsafeFindIntersection tip1 tip2 =
    findIntersection tip1 tip2 <&> fromMaybe (error "unsafeFindIntersection: Precondition violated")

  findIntersection :: Tip -> Tip -> STM m (Maybe Tip)
  findIntersection tip1 tip2
    | tip1 == tip2 = return (Just tip1)
    | pointSlot tip1 <= pointSlot tip2 = getPreviousPoint tip2 >>= maybe (return Nothing) (findIntersection tip1)
    | otherwise = findIntersection tip2 tip1
