{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- FIXME: add explicit exports
module Leios.Model where

import Control.Applicative (asum)
import Control.Concurrent.Class.MonadSTM.TQueue (TQueue, newTQueueIO, readTQueue)
import Control.Concurrent.Class.MonadSTM.TVar (TVar, check, modifyTVar', newTVarIO, readTVar, writeTVar)
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

data RoleType = IBRole | EBRole | Vote1Role | Vote2Role
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

newtype NodeId = NodeId Word
  deriving (Show, Eq, Generic)
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
run tracer = raceAll [node i tracer schedule | i <- [0 .. 2]]
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
  m ()
node nodeId tracer schedule = do
  clock <- runClock
  forever $ do
    slot <- nextSlot clock
    whenM (hasIBRole slot) $ produceIB slot
    -- traceWith tracer (NextSlot nodeId slot)
    pure ()
 where
  hasIBRole = schedule IBRole nodeId

  produceIB slot =
    traceWith tracer (ProducedIB (IB nodeId slot))

--------------------------------------------------------------------------------
-- Events
--------------------------------------------------------------------------------

-- FIXME: remove the prefix once this goes in a separate module.
data LeiosEvent
  = NextSlot {nsNodeId :: NodeId, nsSlot :: Slot} -- FIXME: temporary, just for testing purposes.
  | ProducedIB {producedIB :: IB}
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
