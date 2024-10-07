{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE NamedFieldPuns #-}
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
    takeTMVar,
    tryReadTMVar,
    tryTakeTMVar,
    writeTVar
  ),
 )
import Control.Exception (assert)
import Control.Monad ((<=<))
import Control.Monad.Reader (ReaderT (runReaderT), ask)
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (lookup, (!))
import Data.Maybe (fromMaybe, isJust)
import Network.TypedProtocol
import Network.TypedProtocol.Peer.Server as TS
import Numeric.Natural (Natural)

--------------------------------
--- Common types
--------------------------------

-- TODO
newtype Slot = Slot Natural
  deriving (Eq, Ord)
newtype BlockId = BlockId Natural
  deriving (Eq, Ord)
data BlockHeader
data BlockBody
type ChainTip = Point

blockHeaderParent :: BlockHeader -> Maybe Point
blockHeaderParent = undefined

-- TODO: Could points just be the slot?
data Point = Point
  { pointSlot :: Slot
  , pointBlockId :: BlockId
  }
  deriving (Eq, Ord)

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

-- | Readonly TVar.
newtype ReadOnly a = ReadOnly {unReadOnly :: a}

readReadOnlyTVar :: MonadSTM m => ReadOnly (TVar m a) -> STM m a
readReadOnlyTVar = readTVar . unReadOnly

newtype TakeOnly a = TakeOnly {unTakeOnly :: a}

takeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m a
takeTakeOnlyTMVar = takeTMVar . unTakeOnly

tryTakeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m (Maybe a)
tryTakeTakeOnlyTMVar = tryTakeTMVar . unTakeOnly

type MonadChainSyncProducer m = MonadSTM m

type ChainSyncProducer m = STM (ReaderT (ChainSyncProducerState m) m)
type ChainSyncProducerSTM m a = STM (ReaderT (ChainSyncProducerState m) m) a

data ChainSyncProducerState m = ChainSyncProducerState
  { readPointerVar :: TVar m Point -- Unique, Read/Write.
  , eventsVar :: TakeOnly (TMVar m LocalEvent) -- Shared, Take-Only.
  , chainTipVar :: ReadOnly (TVar m ChainTip) -- Shared, Read-Only.
  , chainForwardsVarVar :: ReadOnly (TVar m (ReadOnly (TVar m (Map Point Point)))) -- Shared, Read-Only.
  , blockHeadersVar :: ReadOnly (TVar m (Map BlockId BlockHeader)) -- Shared, Read-Only.
  , blockBodiesVar :: ReadOnly (TVar m (Map BlockId BlockBody)) -- Shared, Read-Only.
  }

data LocalEvent
  = EvtNewBlock
  | EvtChainSwitch
  deriving (Eq)

instance Semigroup LocalEvent where
  EvtChainSwitch <> _ = EvtChainSwitch
  _ <> EvtChainSwitch = EvtChainSwitch
  EvtNewBlock <> EvtNewBlock = EvtNewBlock

-- NOTE: To be used by @ChainSyncConsumer@
triggerLocalEvent :: MonadSTM m => TMVar m LocalEvent -> LocalEvent -> ChainSyncProducerSTM m ()
triggerLocalEvent evts evt = tryReadTMVar evts >>= putTMVar evts . maybe evt (<> evt)

getReadPointer :: MonadSTM m => ChainSyncProducerSTM m Point
getReadPointer = do
  ChainSyncProducerState{readPointerVar} <- ask
  readTVar readPointerVar

setReadPointer :: MonadSTM m => Point -> ChainSyncProducerSTM m ()
setReadPointer point = do
  ChainSyncProducerState{readPointerVar} <- ask
  writeTVar readPointerVar point

getChainTip :: MonadSTM m => ChainSyncProducerSTM m ChainTip
getChainTip = do
  ChainSyncProducerState{chainTipVar} <- ask
  readReadOnlyTVar chainTipVar

unsafeGetBlockHeader :: MonadSTM m => BlockId -> ChainSyncProducerSTM m BlockHeader
unsafeGetBlockHeader blockId = do
  ChainSyncProducerState{blockHeadersVar} <- ask
  blockHeaders <- readReadOnlyTVar blockHeadersVar
  return $ blockHeaders Map.! blockId

getNextPoint :: MonadSTM m => Point -> ChainSyncProducerSTM m (Maybe Point)
getNextPoint point = do
  ChainSyncProducerState{chainForwardsVarVar} <- ask
  nextPoint <- Map.lookup point <$> (readReadOnlyTVar <=< readReadOnlyTVar) chainForwardsVarVar
  chainTip <- getChainTip -- NOTE: Only required for assertion
  assert (isJust nextPoint || point == chainTip) $ return nextPoint

getPreviousPoint :: MonadSTM m => Point -> ChainSyncProducerSTM m (Maybe Point)
getPreviousPoint point = blockHeaderParent <$> unsafeGetBlockHeader (pointBlockId point)

-- PRECONDITION: All chains share a genesis block.
unsafeFindIntersection :: MonadSTM m => ChainTip -> ChainTip -> ChainSyncProducerSTM m ChainTip
unsafeFindIntersection tip1 tip2 =
  findIntersection tip1 tip2 <&> fromMaybe (error "unsafeFindIntersection: Precondition violated")

findIntersection :: MonadSTM m => ChainTip -> ChainTip -> ChainSyncProducerSTM m (Maybe ChainTip)
findIntersection tip1 tip2
  | tip1 == tip2 = return (Just tip1)
  | pointSlot tip1 <= pointSlot tip2 = getPreviousPoint tip2 >>= maybe (return Nothing) (findIntersection tip1)
  | otherwise = findIntersection tip2 tip1

tryRollForward :: MonadSTM m => ChainSyncProducerSTM m (Maybe BlockHeader)
tryRollForward = do
  point <- getReadPointer
  getNextPoint point >>= \case
    Nothing -> return Nothing
    Just point' -> do
      header' <- unsafeGetBlockHeader (pointBlockId point')
      setReadPointer point'
      return $ Just header'

data Blocking = Blocking | NonBlocking
  deriving (Eq)
data Direction = Forward | Backward
  deriving (Eq)

-- Handles all local events that happened since the chain-sync producer last woke up.
-- If there were only @EvtNewBlock@ events, ignore them. The purpose of this message is to wake blocking producers.
-- If there were @EvtChainSwitch@ events, update the read-pointer and return the current direction.
handleLocalEvents :: MonadSTM m => Blocking -> ChainSyncProducerSTM m Direction
handleLocalEvents shouldBlock = do
  chainSwitched <- didChainSwitch -- Blocks if @shouldBlock == Blocking@
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
 where
  didChainSwitch = do
    ChainSyncProducerState{eventsVar} <- ask
    (== Just EvtChainSwitch) <$> case shouldBlock of
      Blocking -> Just <$> takeTakeOnlyTMVar eventsVar
      NonBlocking -> tryTakeTakeOnlyTMVar eventsVar

chainSyncProducer :: forall m. MonadSTM m => TS.Server ChainSyncState NonPipelined StIdle (ChainSyncProducer m) ()
chainSyncProducer = chainSyncProducer_idle
 where
  chainSyncProducer_idle :: TS.Server ChainSyncState NonPipelined StIdle (ChainSyncProducer m) ()
  chainSyncProducer_idle = TS.Await $ \case
    MsgDone -> TS.Done ()
    MsgRequestNext -> TS.Effect $ _
    --  $ do
    --   handleLocalEvents NonBlocking >>= \case
    --     Forward -> do
    --       tryRollForward >>= \case
    --         Nothing -> do
    --           return $ TS.Yield MsgAwaitReply chainSyncProducer_mustReply
    --         Just header' -> do
    --           tip <- getChainTip
    --           return $ TS.Yield (MsgRollForward_StCanAwait header' tip) chainSyncProducer_idle
    --     Backward -> do
    --       (point, tip) <- (,) <$> getReadPointer <*> getChainTip
    --       return $ TS.Yield (MsgRollBackward_StCanAwait point tip) chainSyncProducer_idle
    MsgFindIntersect points -> TS.Effect $ atomically $ do
      -- NOTE: Should not call `handleLocalEvents` since it does not interact with
      --       the read-pointer and cannot handle chain-switch events.
      tip <- getChainTip
      findIntersectionWithPoints tip points >>= \case
        Nothing -> return $ TS.Yield (MsgIntersectNotFound tip) chainSyncProducer_idle
        Just point -> return $ TS.Yield (MsgIntersectFound point tip) chainSyncProducer_idle

  chainSyncProducer_mustReply :: TS.Server ChainSyncState 'NonPipelined 'StMustReply (ChainSyncProducer m) ()
  chainSyncProducer_mustReply = TS.Effect $ atomically $ do
    handleLocalEvents Blocking >>= \case
      Forward -> do
        tryRollForward >>= \case
          Nothing -> do
            return chainSyncProducer_mustReply
          Just header' -> do
            tip <- getChainTip
            return $ TS.Yield (MsgRollForward_StMustReply header' tip) chainSyncProducer_idle
      Backward -> do
        (point, tip) <- (,) <$> getReadPointer <*> getChainTip
        return $ TS.Yield (MsgRollBackward_StMustReply point tip) chainSyncProducer_idle

data OnChain = Yes | Unknown

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
findIntersectionWithPoints :: forall m. MonadSTM m => ChainTip -> [Point] -> ChainSyncProducerSTM m (Maybe Point)
findIntersectionWithPoints chainTip points = findIntersectionAcc chainTip $ updateIntersectionStatusFor chainTip ((,Unknown) <$> points)
 where
  findIntersectionAcc :: ChainTip -> [(Point, OnChain)] -> ChainSyncProducerSTM m (Maybe Point)
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