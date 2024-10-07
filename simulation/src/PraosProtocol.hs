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
    readTVar,
    takeTMVar,
    tryTakeTMVar,
    writeTVar
  ),
 )
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
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
  deriving (Eq)
data BlockHeader
data BlockBody
newtype ChainId = ChainId Natural
  deriving (Eq, Ord)
type ChainTip = Point

-- TODO: Could points just be the slot?
data Point = Point
  { pointSlot :: Slot
  , pointBlockId :: BlockId
  }
  deriving (Eq)

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

type MonadChainSyncProducer m = MonadSTM m

data ChainSyncProducerState m = ChainSyncProducerState
  { readPointer :: TVar m Point
  , events :: TMVar m LocalEvent
  , chainTip :: TVar m ChainTip
  , headers :: TVar m (Map BlockId BlockHeader)
  }

data LocalEvent
  = EvtNewBlock
  | EvtChainSwitch
  deriving (Eq)

instance Semigroup LocalEvent where
  EvtChainSwitch <> _ = EvtChainSwitch
  _ <> EvtChainSwitch = EvtChainSwitch
  EvtNewBlock <> EvtNewBlock = EvtNewBlock

getReadPointer :: MonadChainSyncProducer m => ChainSyncProducerState m -> STM m Point
getReadPointer st = readTVar $ readPointer st

setReadPointer :: MonadChainSyncProducer m => ChainSyncProducerState m -> Point -> STM m ()
setReadPointer st = writeTVar $ readPointer st

getParent :: MonadChainSyncProducer m => ChainSyncProducerState m -> Point -> STM m (Maybe Point)
getParent st = undefined

getChainTip :: MonadChainSyncProducer m => ChainSyncProducerState m -> STM m ChainTip
getChainTip st = readTVar $ chainTip st

-- PRECONDITION: All chains share a genesis block.
unsafeFindIntersection :: MonadChainSyncProducer m => ChainSyncProducerState m -> ChainTip -> ChainTip -> STM m ChainTip
unsafeFindIntersection st tip1 tip2 =
  findIntersection st tip1 tip2 <&> fromMaybe (error "unsafeFindIntersection: Precondition violated")

findIntersection :: MonadChainSyncProducer m => ChainSyncProducerState m -> ChainTip -> ChainTip -> STM m (Maybe ChainTip)
findIntersection st tip1 tip2
  | tip1 == tip2 = return (Just tip1)
  | pointSlot tip1 <= pointSlot tip2 = do
      getParent st tip2 >>= maybe (return Nothing) (findIntersection st tip1)
  | otherwise = findIntersection st tip2 tip1

getBlockHeader :: MonadChainSyncProducer m => ChainSyncProducerState m -> Point -> STM m BlockHeader
getBlockHeader = undefined

getNextPoint :: MonadChainSyncProducer m => ChainSyncProducerState m -> Point -> STM m (Maybe Point)
getNextPoint = undefined

-- PRECONDITION: readPointer < chainTip
unsafeRollForward :: MonadChainSyncProducer m => ChainSyncProducerState m -> STM m BlockHeader
unsafeRollForward st =
  tryRollForward st <&> fromMaybe (error "unsafeRollForward: Precondition violated")

tryRollForward :: MonadChainSyncProducer m => ChainSyncProducerState m -> STM m (Maybe BlockHeader)
tryRollForward st = do
  point <- getReadPointer st
  getNextPoint st point >>= \case
    Nothing -> return Nothing
    Just point' -> do
      header' <- getBlockHeader st point'
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
      setReadPointer st point'
      return Backward
 where
  didChainSwitch :: STM m Bool
  didChainSwitch = (== Just EvtChainSwitch) <$> maybeLocalEvent

  maybeLocalEvent :: STM m (Maybe LocalEvent)
  maybeLocalEvent = case blocking of
    Blocking -> Just <$> takeTMVar events
    NonBlocking -> tryTakeTMVar events

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
      point <- getReadPointer st
      chainTip <- getChainTip st
      if point == chainTip
        then return $ TS.Yield MsgAwaitReply chainSyncProducer_mustReply
        else case direction of
          Forward -> do
            header' <- unsafeRollForward st
            return $ TS.Yield (MsgRollForward_StCanAwait header' chainTip) chainSyncProducer_idle
          Backward -> do
            return $ TS.Yield (MsgRollBackward_StCanAwait point chainTip) chainSyncProducer_idle
    MsgFindIntersect points -> chainSyncProducer_intersect points

  chainSyncProducer_mustReply :: TS.Server ChainSyncState 'NonPipelined 'StMustReply m ()
  chainSyncProducer_mustReply = TS.Effect $ atomically $ do
    direction <- catchUp st Blocking
    point <- getReadPointer st
    chainTip <- getChainTip st
    if point == chainTip
      then return chainSyncProducer_mustReply
      else case direction of
        Forward -> do
          header' <- unsafeRollForward st
          return $ TS.Yield (MsgRollForward_StMustReply header' chainTip) chainSyncProducer_idle
        Backward -> do
          return $ TS.Yield (MsgRollBackward_StMustReply point chainTip) chainSyncProducer_idle

  chainSyncProducer_intersect :: [Point] -> TS.Server ChainSyncState 'NonPipelined 'StIntersect m ()
  chainSyncProducer_intersect points = TS.Effect $ atomically $ do
    -- NOTE: does not require `catchUp`
    chainTip <- getChainTip st
    findIntersectionWithPoints st chainTip points >>= \case
      Nothing -> return $ TS.Yield (MsgIntersectNotFound chainTip) chainSyncProducer_idle
      Just point -> return $ TS.Yield (MsgIntersectFound point chainTip) chainSyncProducer_idle

-- TODO:
-- Order of `points` must be maintained.
-- Maintain separate dictionary of point status (yes, no, unknown).
-- Traverse through chain by iterating `getParent` on `chainTip`.
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
    getParent st tip >>= \case
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