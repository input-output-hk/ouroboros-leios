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

module PraosProtocol where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TMVar,
    TVar,
    atomically,
    putTMVar,
    readTVar,
    tryReadTMVar,
    writeTVar
  ),
 )
import Control.Exception (assert)
import Control.Monad ((<=<))
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (lookup, (!))
import Data.Maybe (fromMaybe, isJust)
import Network.TypedProtocol
import Network.TypedProtocol.Peer.Server as TS

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

--------------------------------
---- ChainSync Producer
--------------------------------

data ChainSyncProducerState m = ChainSyncProducerState
  { readPointerVar :: TVar m Point -- Unique, Read/Write.
  , eventsVar :: TakeOnly (TMVar m ChainSyncProducerEvent) -- Shared, Take-Only.
  , chainTipVar :: ReadOnly (TVar m ChainTip) -- Shared, Read-Only.
  , chainForwardsVarVar :: ReadOnly (TVar m (ReadOnly (TVar m (Map Point Point)))) -- Shared, Read-Only.
  , blockHeadersVar :: ReadOnly (TVar m (Map BlockId BlockHeader)) -- Shared, Read-Only.
  }

-- CONVENTION: Events are named for the recipient.
data ChainSyncProducerEvent
  = EvtNewBlock
  | EvtChainSwitch
  deriving (Eq)

instance Semigroup ChainSyncProducerEvent where
  EvtChainSwitch <> _ = EvtChainSwitch
  _ <> EvtChainSwitch = EvtChainSwitch
  EvtNewBlock <> EvtNewBlock = EvtNewBlock

-- NOTE: To be used by @ChainSyncConsumer@
triggerLocalEvent :: MonadSTM m => TMVar m ChainSyncProducerEvent -> ChainSyncProducerEvent -> STM m ()
triggerLocalEvent evts evt =
  tryReadTMVar evts >>= putTMVar evts . maybe evt (<> evt)

chainSyncProducer ::
  forall m.
  MonadSTM m =>
  ChainSyncProducerState m ->
  TS.Server ChainSyncState NonPipelined StIdle m ()
chainSyncProducer st = idle
 where
  idle :: TS.Server ChainSyncState NonPipelined StIdle m ()
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

  mustReply :: TS.Server ChainSyncState 'NonPipelined 'StMustReply m ()
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

  intersect :: [Point] -> TS.Server ChainSyncState 'NonPipelined 'StIntersect m ()
  intersect points = TS.Effect $ atomically $ do
    -- NOTE: Should not call `handleLocalEvents` since it does not interact with
    --       the read-pointer and cannot handle chain-switch events.
    tip <- getChainTip
    findIntersectionWithPoints tip points >>= \case
      Nothing -> return $ TS.Yield (MsgIntersectNotFound tip) idle
      Just point -> return $ TS.Yield (MsgIntersectFound point tip) idle

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
      Blocking -> Just <$> takeTakeOnlyTMVar st.eventsVar
      NonBlocking -> tryTakeTakeOnlyTMVar st.eventsVar

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
  findIntersectionWithPoints :: ChainTip -> [Point] -> STM m (Maybe Point)
  findIntersectionWithPoints chainTip points =
    findIntersectionAcc chainTip (updateIntersectionStatusFor chainTip ((,Unknown) <$> points))
   where
    findIntersectionAcc :: ChainTip -> [(Point, OnChain)] -> STM m (Maybe Point)
    findIntersectionAcc _tip [] = return Nothing
    findIntersectionAcc _tip ((point, Yes) : _) = return (Just point)
    findIntersectionAcc tip pointsAndStatuses = do
      getPreviousPoint tip >>= \case
        Nothing -> return Nothing
        Just tip' -> findIntersectionAcc tip' (updateIntersectionStatusFor tip' pointsAndStatuses)

    updateIntersectionStatusFor :: ChainTip -> [(Point, OnChain)] -> [(Point, OnChain)]
    updateIntersectionStatusFor _ [] = []
    updateIntersectionStatusFor _ ((point, Yes) : _pointsAndStatuses) = [(point, Yes)]
    updateIntersectionStatusFor tip ((point, Unknown) : pointsAndStatuses)
      | point == tip = [(point, Yes)]
      | pointSlot tip < pointSlot point = updateIntersectionStatusFor tip pointsAndStatuses
      | otherwise = updateIntersectionStatusFor tip pointsAndStatuses

  getReadPointer :: STM m Point
  getReadPointer = readTVar st.readPointerVar

  setReadPointer :: Point -> STM m ()
  setReadPointer = writeTVar st.readPointerVar

  getChainTip :: STM m ChainTip
  getChainTip = readReadOnlyTVar st.chainTipVar

  -- PRECONDITION: All block IDs have headers.
  unsafeGetBlockHeader :: BlockId -> STM m BlockHeader
  unsafeGetBlockHeader blockId = do
    blockHeaders <- readReadOnlyTVar st.blockHeadersVar
    return $ blockHeaders Map.! blockId

  getNextPoint :: Point -> STM m (Maybe Point)
  getNextPoint point = do
    nextPoint <- Map.lookup point <$> (readReadOnlyTVar <=< readReadOnlyTVar) st.chainForwardsVarVar
    chainTip <- getChainTip -- NOTE: Only required for assertion
    assert (isJust nextPoint || point == chainTip) $ return nextPoint

  getPreviousPoint :: Point -> STM m (Maybe Point)
  getPreviousPoint point = blockHeaderParent <$> unsafeGetBlockHeader (pointBlockId point)

  -- PRECONDITION: All chains share a genesis block.
  unsafeFindIntersection :: ChainTip -> ChainTip -> STM m ChainTip
  unsafeFindIntersection tip1 tip2 =
    findIntersection tip1 tip2 <&> fromMaybe (error "unsafeFindIntersection: Precondition violated")

  findIntersection :: ChainTip -> ChainTip -> STM m (Maybe ChainTip)
  findIntersection tip1 tip2
    | tip1 == tip2 = return (Just tip1)
    | pointSlot tip1 <= pointSlot tip2 = getPreviousPoint tip2 >>= maybe (return Nothing) (findIntersection tip1)
    | otherwise = findIntersection tip2 tip1
