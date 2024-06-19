{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- FIXME: add explicit exports
--
--
-- Next steps:
-- ===========
--
-- * Implement FFD policy.
-- * Add the notion of capacity.
-- * Add EB production only with IBs so that λ parameter becomes relevant.
-- * ⭐ Connect with the simulation front end and run.
-- * Add other plots: eg latency distribution.
-- * ...
-- * Implement other roles/phase.
module Leios.Model where

import Prelude hiding (init)

import Data.Foldable (for_)
import Control.Applicative (asum)
import Control.Concurrent.Class.MonadSTM.TQueue (TQueue, newTQueueIO, readTQueue)
import Control.Concurrent.Class.MonadSTM.TVar (TVar, check, modifyTVar', newTVarIO, readTVar, writeTVar, modifyTVar')
import Control.Monad (forever)
import Control.Monad.Class.MonadAsync (Async, Concurrently (Concurrently, runConcurrently), MonadAsync, async, race_)
import Control.Monad.Class.MonadSTM (MonadSTM, atomically)
import Control.Monad.Class.MonadTimer (MonadDelay, MonadTimer, threadDelay)
import Control.Monad.Extra (whenM)
import Control.Tracer (Tracer, traceWith)
import qualified Data.Aeson as Aeson
import GHC.Generics (Generic)
import Leios.Trace (mkTracer)
import Text.Pretty.Simple (pPrint)
import Control.Concurrent.Class.MonadSTM.TChan (TChan, newTChanIO, readTChan, writeTChan)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

data RoleType = IBRole | EBRole | Vote1Role | Vote2Role
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

newtype NodeId = NodeId Word
  deriving (Show, Eq, Generic, Ord)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)
  deriving newtype (Enum, Num)

newtype Slot = Slot Word
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)
  deriving newtype (Enum)

data IB
  = IB
  { nodeId :: NodeId
  , slot :: Slot
  }
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

tickSlot :: Slot -> Slot
tickSlot = succ

run ::
  forall m.
  ( Monad m
  , Applicative m
  , MonadAsync m
  , MonadTimer m
  , MonadSTM m
  , MonadDelay m
  ) =>
  Tracer m LeiosEvent ->
  m ()
run tracer = do
  world <- init
  raceAll [register i world >> node i tracer schedule world | i <- [0 .. 2]]
 where
  -- TODO: we need to find a more general and realistic way to model the schedule.
  --
  -- In particular we should add the ledger state needed to determine leadership (eg stake distribution).
  --
  -- Also we would like more than one node to be elected to issue blocks or votes (specially the latter!).
  schedule :: RoleType -> NodeId -> Slot -> m Bool
  schedule _ (NodeId nid) (Slot slot) = pure $ slot `mod` (nid + 1) == 0

type Schedule m = RoleType -> NodeId -> Slot -> m Bool

raceAll ::
  forall t m a.
  (Foldable t, Functor t, MonadAsync m, MonadTimer m) =>
  t (m a) ->
  m a
raceAll = runConcurrently . asum . fmap Concurrently

node ::
  ( Monad m
  , Applicative m
  , MonadSTM m
  , MonadAsync m
  , MonadDelay m
  ) =>
  NodeId ->
  Tracer m LeiosEvent ->
  Schedule m ->
  OutsideWorld m ->
  m ()
node nodeId tracer schedule world = do
  producer `race_` consumer
 where
  producer = do
    clock <- runClock
    forever $ do
      slot <- nextSlot clock
      whenM (hasIBRole slot) $ produceIB slot
      -- traceWith tracer (NextSlot nodeId slot)
      pure ()

  consumer = forever $ do
    msg <- nodeId `receiveFrom` world
    case msg of
      MsgIB ib -> do
        traceWith tracer (ReceivedIB ib nodeId)

  hasIBRole = schedule IBRole nodeId

  produceIB slot = do
    let newIB = IB nodeId slot
    traceWith tracer (ProducedIB newIB)
    MsgIB newIB `sendTo` world

--------------------------------------------------------------------------------
-- Events
--------------------------------------------------------------------------------

-- FIXME: remove the prefix once this goes in a separate module.
data LeiosEvent
  = NextSlot {nsNodeId :: NodeId, nsSlot :: Slot} -- FIXME: temporary, just for testing purposes.
  | ProducedIB {producedIB :: IB}
  | ReceivedIB {receivedIB :: IB, receivedBy :: NodeId }
  deriving (Show, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

--------------------------------------------------------------------------------
-- IO simulation
--------------------------------------------------------------------------------

runIO :: IO ()
runIO = do
  events <- newTQueueIO
  run (mkTracer events) `race_` outputToStdout events
 where
  -- FIXME: temporary
  outputToStdout :: TQueue IO Aeson.Value -> IO ()
  outputToStdout events = forever $ do
    atomically (readTQueue events) >>= pPrint

--------------------------------------------------------------------------------
-- Blockchain Clock
--------------------------------------------------------------------------------

runClock :: (Monad m, MonadSTM m, MonadAsync m, MonadDelay m) => m (Clock m)
runClock = do
  -- FIXME: maybe the slot needs to be determined from the chain start time.
  slotTVar <- newTVarIO (Slot 0)
  lastReadTVar <- newTVarIO Nothing
  a <- async $ tick slotTVar
  pure $
    Clock
      { clockAsync = a
      , slotTVar = slotTVar
      , lastReadTVar = lastReadTVar
      }
 where
  tick slotTVar = forever $ do
    threadDelay 1_000_000
    atomically $ modifyTVar' slotTVar tickSlot

-- | Return the next slot, blocking until its time arrives.
nextSlot :: MonadSTM m => Clock m -> m Slot
nextSlot clock = atomically $ do
  currentSlot <- readTVar (slotTVar clock)
  mLastReadSlot <- readTVar (lastReadTVar clock)
  check (Just currentSlot /= mLastReadSlot)
  writeTVar (lastReadTVar clock) (Just currentSlot)
  pure $ currentSlot

data Clock m
  = Clock
  { clockAsync :: Async m ()
  , slotTVar :: TVar m Slot
  , lastReadTVar :: TVar m (Maybe Slot)
  }

--------------------------------------------------------------------------------
-- (very simple) Outside World Model
--------------------------------------------------------------------------------

data OutsideWorld m =
  OutsideWorld { nodesTChans :: TVar m (Map NodeId (TChan m Msg)) }
  -- FIXME: for IBs we need to implement FFD policy.
  -- TODO: we need to think about the other types of messages. How are the different types of messages prioritized?

data Msg = MsgIB { msgIB :: IB }

init :: forall m .
  (Monad m, MonadSTM m, Applicative m) => m (OutsideWorld m)
init = do
   tchans <- newTVarIO Map.empty
   pure $ OutsideWorld { nodesTChans = tchans }

-- | .
--
-- PRECONDITION: the node should not have been registered.
register :: forall m .
  (Monad m, MonadSTM m) => NodeId -> OutsideWorld m -> m ()
register nodeId world = do
  nodeTChan <- newTChanIO
  -- TODO: we could use broadcast channels.
  atomically $ do
    -- FIXME: assert the 'nodeId' is not registered.
    tchanMap <- readTVar (nodesTChans world)
    modifyTVar' (nodesTChans world) (Map.insert nodeId nodeTChan)

-- | ...
--
-- In this first iteration we assume the message is broadcast to each node.
--
-- NOTE: a node will receive it's own message. We could prevent this by including the senders's id in the function type.
sendTo :: forall m .
  (MonadSTM m) =>
  Msg -> OutsideWorld m -> m ()
sendTo msg world = atomically $ do
  tchansMap <- readTVar (nodesTChans world)
  for_ (Map.elems tchansMap) (`writeTChan` msg)

-- | ...
--
-- PRECONDITION: The node ID must exist.
receiveFrom :: forall m . (MonadSTM m) =>  NodeId -> OutsideWorld m -> m Msg
receiveFrom nodeId world = do
  mTChan <- fmap (Map.lookup nodeId) $ atomically $ readTVar (nodesTChans world)
  case mTChan of
    Nothing -> error $ "Node " <> show nodeId <> " does not exist."
    Just tchan -> do
      atomically $ readTChan tchan
