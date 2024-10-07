{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
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

data ChainSyncProducerState m = ChainSyncProducerState
  { readPointer :: TVar m Point -- Owned, Unique, Read/Write.
  , events :: TakeOnly (TMVar m Event) -- Owned, Shared, Take-Only.
  , chainTip :: ReadOnly (TVar m ChainTip) -- Borrowed, Shared, Read-Only.
  , chainForwards :: ReadOnly (TVar m (ReadOnly (TVar m (Map Point Point)))) -- Borrowed, Shared, Read-Only.
  , blockHeaders :: ReadOnly (TVar m (Map BlockId BlockHeader)) -- Borrowed, Shared, Read-Only.
  , blockBodies :: ReadOnly (TVar m (Map BlockId BlockBody)) -- Borrowed, Shared, Read-Only.
  }

data Event
  = EvtNewBlock
  | EvtChainSwitch
  deriving (Eq)

instance Semigroup Event where
  EvtChainSwitch <> _ = EvtChainSwitch
  _ <> EvtChainSwitch = EvtChainSwitch
  EvtNewBlock <> EvtNewBlock = EvtNewBlock

-- NOTE: To be used by @ChainSyncConsumer@
triggerEvent :: MonadSTM m => TMVar m Event -> Event -> STM m ()
triggerEvent evts evt = tryReadTMVar evts >>= putTMVar evts . maybe evt (<> evt)

getReadPointer :: MonadChainSyncProducer m => ChainSyncProducerState m -> STM m Point
getReadPointer st = readTVar $ readPointer st

setReadPointer :: MonadChainSyncProducer m => ChainSyncProducerState m -> Point -> STM m ()
setReadPointer st = writeTVar $ readPointer st

getChainTip :: MonadChainSyncProducer m => ChainSyncProducerState m -> STM m ChainTip
getChainTip st = readReadOnlyTVar $ chainTip st

getBlockHeader :: MonadChainSyncProducer m => ChainSyncProducerState m -> BlockId -> STM m BlockHeader
getBlockHeader st blockId = (Map.! blockId) <$> readReadOnlyTVar (blockHeaders st)

getBlockBody :: MonadChainSyncProducer m => ChainSyncProducerState m -> BlockId -> STM m BlockBody
getBlockBody st blockId = (Map.! blockId) <$> readReadOnlyTVar (blockBodies st)

getNextPoint :: MonadChainSyncProducer m => ChainSyncProducerState m -> Point -> STM m (Maybe Point)
getNextPoint st point = do
  nextPoint <- Map.lookup point <$> (readReadOnlyTVar <=< readReadOnlyTVar) (chainForwards st)
  chainTip <- getChainTip st -- NOTE: Only required for assertion
  assert (isJust nextPoint || point == chainTip) $ return nextPoint

getPrevPoint :: MonadChainSyncProducer m => ChainSyncProducerState m -> Point -> STM m (Maybe Point)
getPrevPoint st point = blockHeaderParent <$> getBlockHeader st (pointBlockId point)

-- PRECONDITION: All chains share a genesis block.
unsafeFindIntersection :: MonadChainSyncProducer m => ChainSyncProducerState m -> ChainTip -> ChainTip -> STM m ChainTip
unsafeFindIntersection st tip1 tip2 =
  findIntersection st tip1 tip2 <&> fromMaybe (error "unsafeFindIntersection: Precondition violated")

findIntersection :: MonadChainSyncProducer m => ChainSyncProducerState m -> ChainTip -> ChainTip -> STM m (Maybe ChainTip)
findIntersection st tip1 tip2
  | tip1 == tip2 = return (Just tip1)
  | pointSlot tip1 <= pointSlot tip2 = do
      getPrevPoint st tip2 >>= maybe (return Nothing) (findIntersection st tip1)
  | otherwise = findIntersection st tip2 tip1

tryRollForward :: MonadChainSyncProducer m => ChainSyncProducerState m -> STM m (Maybe BlockHeader)
tryRollForward st = do
  point <- getReadPointer st
  getNextPoint st point >>= \case
    Nothing -> return Nothing
    Just point' -> do
      header' <- getBlockHeader st (pointBlockId point')
      setReadPointer st point'
      return $ Just header'

data Blocking = Blocking | NonBlocking
  deriving (Eq)
data Direction = Forward | Backward
  deriving (Eq)

-- TODO:
-- Check local events.
-- If EvtNewBlock, ignore. The point of this message is to wake you up.
-- If EvtChainSwitch, recompute read-pointer, return some information that says a chain switch happened.
catchUp :: forall m. MonadChainSyncProducer m => ChainSyncProducerState m -> Blocking -> STM m Direction
catchUp st@ChainSyncProducerState{events} blocking = do
  chainSwitched <- didChainSwitch
  if not chainSwitched
    then do
      return Forward
    else do
      tip <- getChainTip st
      point <- getReadPointer st
      point' <- unsafeFindIntersection st tip point
      if point == point'
        then do
          return Forward
        else do
          setReadPointer st point'
          return Backward
 where
  didChainSwitch :: STM m Bool
  didChainSwitch =
    (== Just EvtChainSwitch) <$> case blocking of
      Blocking -> Just <$> takeTakeOnlyTMVar events
      NonBlocking -> tryTakeTakeOnlyTMVar events

chainSyncProducer ::
  forall m.
  MonadChainSyncProducer m =>
  ChainSyncProducerState m ->
  TS.Server ChainSyncState NonPipelined StIdle m ()
chainSyncProducer st = chainSyncProducer_idle
 where
  chainSyncProducer_idle :: TS.Server ChainSyncState NonPipelined StIdle m ()
  chainSyncProducer_idle = TS.Await $ \case
    MsgDone -> TS.Done ()
    MsgRequestNext -> TS.Effect $ atomically $ do
      direction <- catchUp st NonBlocking
      case direction of
        Forward -> do
          tryRollForward st >>= \case
            Nothing -> do
              return $ TS.Yield MsgAwaitReply chainSyncProducer_mustReply
            Just header' -> do
              tip <- getChainTip st
              return $ TS.Yield (MsgRollForward_StCanAwait header' tip) chainSyncProducer_idle
        Backward -> do
          point <- getReadPointer st
          tip <- getChainTip st
          return $ TS.Yield (MsgRollBackward_StCanAwait point tip) chainSyncProducer_idle
    MsgFindIntersect points -> TS.Effect $ atomically $ do
      -- NOTE: Should not call `catchUp` since it does not interact with the
      --       read-pointer and cannot handle chain-switch events.
      tip <- getChainTip st
      findIntersectionWithPoints st tip points >>= \case
        Nothing -> return $ TS.Yield (MsgIntersectNotFound tip) chainSyncProducer_idle
        Just point -> return $ TS.Yield (MsgIntersectFound point tip) chainSyncProducer_idle

  chainSyncProducer_mustReply :: TS.Server ChainSyncState 'NonPipelined 'StMustReply m ()
  chainSyncProducer_mustReply = TS.Effect $ atomically $ do
    direction <- catchUp st Blocking
    case direction of
      Forward -> do
        tryRollForward st >>= \case
          Nothing -> do
            return chainSyncProducer_mustReply
          Just header' -> do
            tip <- getChainTip st
            return $ TS.Yield (MsgRollForward_StMustReply header' tip) chainSyncProducer_idle
      Backward -> do
        point <- getReadPointer st
        tip <- getChainTip st
        return $ TS.Yield (MsgRollBackward_StMustReply point tip) chainSyncProducer_idle

-- NOTE: Order of `points` must be maintained.
-- Maintain separate dictionary of point status (yes, no, unknown).
-- Traverse through chain by iterating `getPrevPoint` on `chainTip`.
-- For each step, for each point:
-- If the point is equal to current chain-tip, mark its status as yes.
-- If the point slot is after the current chain-tip slot, mark its status as no.
-- Otherwise, keep its status as unknown.
-- If the point status of any prefix of `points` are all yes/no with at least one yes, then return the first yes.
-- Otherwise, when you reach the genesis block, return Nothing.
findIntersectionWithPoints :: forall m. MonadChainSyncProducer m => ChainSyncProducerState m -> ChainTip -> [Point] -> STM m (Maybe Point)
findIntersectionWithPoints st chainTip points = findIntersectionAcc chainTip $ updateIntersectionStatusFor chainTip ((,False) <$> points)
 where
  findIntersectionAcc :: ChainTip -> [(Point, Bool)] -> STM m (Maybe Point)
  findIntersectionAcc _tip [] = return Nothing
  findIntersectionAcc _tip ((point, True) : _) = return (Just point)
  findIntersectionAcc tip pointsAndStatuses = do
    getPrevPoint st tip >>= \case
      Nothing -> return Nothing
      Just tip' -> findIntersectionAcc tip' (updateIntersectionStatusFor tip' pointsAndStatuses)

  -- The @Bool@ encodes whether the @Point@ is known to intersect with the chain:
  -- + If @True@, it is known to intersect with the chain.
  -- + If @False@, it is not known to intersect with the chain.
  -- + If it is known not to intersect with the chain, the point is dropped.
  -- If any @Point@ is known to intersect with the chain, the suffix can be dropped.
  updateIntersectionStatusFor :: ChainTip -> [(Point, Bool)] -> [(Point, Bool)]
  updateIntersectionStatusFor _ [] = []
  updateIntersectionStatusFor _ ((point, True) : _pointsAndStatuses) = [(point, True)]
  updateIntersectionStatusFor tip ((point, False) : pointsAndStatuses)
    | point == tip = [(point, True)]
    | pointSlot tip < pointSlot point = updateIntersectionStatusFor tip pointsAndStatuses
    | otherwise = updateIntersectionStatusFor tip pointsAndStatuses