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
-- \* ✅ Implement FFD policy.
-- \* ✅ Add the notion of ~~capacity~~ bandwidth.
-- \* Check that after adding capacity when blocks are queued we still deliver the freshest first.
-- \* Add EB production only with IBs so that λ parameter becomes relevant.
-- \* ⭐ Connect with the simulation front end and run.
-- \* Add other plots: eg latency distribution.
-- \* ...
-- \* Implement other roles/phase.
--
-- TODOs:
-- =====
--
-- \* Make the IB size configurable.
module Leios.Model where

import Prelude hiding (init)

import Control.Applicative (asum)
import Control.Concurrent.Class.MonadSTM.TChan (TChan, newTChanIO, readTChan, writeTChan)
import Control.Concurrent.Class.MonadSTM.TQueue (TQueue, newTQueueIO, readTQueue)
import Control.Concurrent.Class.MonadSTM.TVar (TVar, check, modifyTVar', newTVarIO, readTVar, writeTVar)
import Control.Monad (forever)
import Control.Monad.Class.MonadAsync (Async, Concurrently (Concurrently, runConcurrently), MonadAsync, async, race_)
import Control.Monad.Class.MonadSTM (MonadSTM, STM, atomically, retry)
import Control.Monad.Class.MonadTimer (MonadDelay, MonadTimer, threadDelay)
import Control.Monad.Extra (whenM)
import Control.Tracer (Tracer, traceWith)
import qualified Data.Aeson as Aeson
import Data.Foldable (for_)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.PQueue.Max (MaxQueue)
import qualified Data.PQueue.Max as PQueue
import GHC.Generics (Generic)
import Leios.Trace (mkTracer)
import Text.Pretty.Simple (pPrint)

--------------------------------------------------------------------------------
-- FIXME: constants that should be configurable
--------------------------------------------------------------------------------

gNodeBandwidth = BitsPerSecond 100

gIBSize = NumberOfBits 300

--------------------------------------------------------------------------------
-- END FIXME: constants that should be configurable
--------------------------------------------------------------------------------

data RoleType = IBRole | EBRole | Vote1Role | Vote2Role
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

newtype NodeId = NodeId Word
  deriving (Show, Eq, Generic, Ord)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)
  deriving newtype (Enum, Num)

newtype Slot = Slot Word
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)
  deriving newtype (Enum)

tickSlot :: Slot -> Slot
tickSlot = succ

data IB
  = IB
  { nodeId :: NodeId
  , slot :: Slot
  , ib_size :: NumberOfBits
  }
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

instance HasSizeInBits IB where
  size = ib_size

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
  owparamsTV <- newTVarIO $ OWParams $ gNodeBandwidth
  world <- init owparamsTV
  raceAll [register i world >> node i tracer schedule world | i <- [0 .. 1]]
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
    let newIB = IB nodeId slot gIBSize
    traceWith tracer (ProducedIB newIB)
    MsgIB newIB `sendTo` world

--------------------------------------------------------------------------------
-- Events
--------------------------------------------------------------------------------

-- FIXME: remove the prefix once this goes in a separate module.
data LeiosEvent
  = NextSlot {nsNodeId :: NodeId, nsSlot :: Slot} -- FIXME: temporary, just for testing purposes.
  | ProducedIB {producedIB :: IB}
  | ReceivedIB {receivedIB :: IB, receivedBy :: NodeId}
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

data OutsideWorld m
  = OutsideWorld
  { pqsTVar :: TVar m (Map NodeId (PQueueTVar m))
  , paramsTV :: TVar m OWParams
  }

data OWParams = OWParams {nodeBandwidth :: BitsPerSecond}

newtype BitsPerSecond = BitsPerSecond Word
  deriving (Eq, Show, Generic, Ord)

data Msg = MsgIB {msgIB :: IB}

instance HasSizeInBits Msg where
  size (MsgIB ib) = size ib

init ::
  forall m.
  (Monad m, MonadSTM m, Applicative m) =>
  TVar m OWParams ->
  m (OutsideWorld m)
init paramsTV = do
  pqsTVar <- newTVarIO Map.empty
  pure $ OutsideWorld{pqsTVar = pqsTVar, paramsTV = paramsTV}

-- | .
--
-- PRECONDITION: the node should not have been registered.
register ::
  forall m.
  (Monad m, MonadSTM m) =>
  NodeId ->
  OutsideWorld m ->
  m ()
register nodeId world = do
  pqTVar <- newPQueue
  -- TODO: we could use broadcast channels.
  atomically $ do
    -- FIXME: assert the 'nodeId' is not registered.
    modifyTVar' (pqsTVar world) (Map.insert nodeId pqTVar)

-- | ...
--
-- In this first iteration we assume the message is broadcast to each node.
--
-- NOTE: a node will receive it's own message. We could prevent this by including the senders's id in the function type.
sendTo ::
  forall m.
  MonadSTM m =>
  Msg ->
  OutsideWorld m ->
  m ()
sendTo msg world = atomically $ do
  pqsMap <- readTVar (pqsTVar world)
  for_ (Map.elems pqsMap) (insertPQueue msg)

-- | ...
--
-- PRECONDITION: The node ID must exist.
receiveFrom :: forall m. (MonadSTM m, MonadDelay m) => NodeId -> OutsideWorld m -> m Msg
receiveFrom nodeId world = do
  m_pqTVar <- fmap (Map.lookup nodeId) $ atomically $ readTVar (pqsTVar world)
  case m_pqTVar of
    Nothing -> error $ "Node " <> show nodeId <> " does not exist."
    Just pqTVar -> do
      msg <- pop pqTVar
      owNodeBandwidth <- nodeBandwidth <$> (atomically $ readTVar (paramsTV world))
      let msToInt (Microseconds ms) = fromIntegral ms
      threadDelay $ msToInt $ transmissionTime (size msg) owNodeBandwidth
      pure msg

--------------------------------------------------------------------------------
-- A priority queue inside a transactional var
--------------------------------------------------------------------------------

data PQueueTVar m = PQueueTVar {getTQueueTVar :: TVar m (MaxQueue PMsg)}

-- | Wrapper around 'Msg' to implement the priority needed for the priority queue.
newtype PMsg = PMsg Msg

instance Eq PMsg where
  PMsg (MsgIB ib_x) == PMsg (MsgIB ib_y) = slot ib_x == slot ib_y

instance Ord PMsg where
  PMsg (MsgIB ib_x) <= PMsg (MsgIB ib_y) = slot ib_x <= slot ib_y

-- TODO: the 'queue' part can be dropped if these functions are put in a separate module.
newPQueue :: (Functor m, MonadSTM m) => m (PQueueTVar m)
newPQueue = PQueueTVar <$> newTVarIO mempty

insertPQueue :: MonadSTM m => Msg -> PQueueTVar m -> STM m ()
insertPQueue msg pqTVar = do
  modifyTVar' (getTQueueTVar pqTVar) (PQueue.insert (PMsg msg))

-- | Take the message at the front of the queue (eg the freshest IB), and delete it from the queue. If the queue is empty, blocks until a message arrives.
pop :: MonadSTM m => PQueueTVar m -> m Msg
pop pqTVar = atomically $ do
  queue <- readTVar (getTQueueTVar pqTVar)
  case PQueue.getMax queue of
    Nothing -> retry
    Just (PMsg msg) -> do
      writeTVar (getTQueueTVar pqTVar) (PQueue.deleteMax queue)
      pure msg

--------------------------------------------------------------------------------
-- Byte Size Calculations
--------------------------------------------------------------------------------

class HasSizeInBits a where
  size :: a -> NumberOfBits

newtype NumberOfBits = NumberOfBits Word
  deriving (Generic, Show, Eq, Ord)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

newtype Microseconds = Microseconds Word
  deriving (Generic, Show, Eq, Ord)

-- | .
--
-- PRECONDITION: rate =/ 0.
transmissionTime :: NumberOfBits -> BitsPerSecond -> Microseconds
transmissionTime (NumberOfBits nr_bits) (BitsPerSecond rate) = Microseconds $ ceiling $ seconds * 1_000_000
 where
  seconds :: Double
  seconds = (fromIntegral nr_bits) / (fromIntegral rate)
