{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
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
-- \* ✅ Check that after adding capacity when blocks are queued we still deliver the freshest first.
-- \* ✅ Add EB production only with IBs so that λ parameter becomes relevant.
-- \* ✅ Allow to pass paremeters to the simulation.
-- \* ✅ Connect with the simulation front end and run.
-- \* Define a better/more-realistic schedule.
-- \* Add other plots: eg latency distribution.
-- \* ...
-- \* Implement other roles/phase.
--
-- TODOs:
-- =====
--
-- \* Make the IB size configurable.
-- \* Minor: I need to use '_' for certain variable names so that they match the paper. Should I simply use snake case overall?
-- \* Address all the FIXMEs.
--
module Leios.Model where

import Prelude hiding (init)

import Control.Applicative (asum)
import Control.Concurrent.Class.MonadSTM.TChan (TChan, newTChanIO, readTChan, writeTChan)
import Control.Concurrent.Class.MonadSTM.TQueue (TQueue, newTQueueIO, readTQueue)
import Control.Concurrent.Class.MonadSTM.TVar (TVar, check, modifyTVar', newTVarIO, readTVar, readTVarIO, writeTVar)
import Control.Monad (forever, replicateM)
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
import Data.List (partition)
import System.Random (randomR, RandomGen, mkStdGen, split)
import Control.Monad.State (State, get, put, runState)
import Data.Word (Word64)

--------------------------------------------------------------------------------
-- FIXME: constants that should be configurable
--------------------------------------------------------------------------------

g_L = NumberOfSlots 4

g_λ = NumberOfSlices 3

gNodeBandwidth = BitsPerSecond 100

gIBSize = NumberOfBits 300

g_f_I = IBFrequency 0.5

g_f_E = EBFrequency 1

--------------------------------------------------------------------------------
-- Model parameters
--------------------------------------------------------------------------------

-- FIXME: we should add a parameter to determine the number of slots per second (or slot duration).
--
-- TODO: we might want to split this between constants and parameters that can be tweaked at runtime.
data Parameters = Parameters
  { _L :: NumberOfSlots
  -- ^  Slice length.
  , λ :: NumberOfSlices
  -- ^ Number of slices (of size '_L') the diffusion period takes.
  , nodeBandwidth :: BitsPerSecond
  , ibSize :: NumberOfBits
  -- ^ Size of the diffusion block.
  , f_I :: IBFrequency
  , f_E :: EBFrequency
  , initialSeed :: Int
  }
  deriving (Show, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

newtype NumberOfSlots = NumberOfSlots Word
  deriving stock (Generic)
  deriving newtype (Show, Eq, Ord, Num, Aeson.ToJSON, Aeson.FromJSON)

newtype NumberOfSlices = NumberOfSlices Word
  deriving stock (Generic)
  deriving newtype (Show, Eq, Ord, Num, Aeson.ToJSON, Aeson.FromJSON)

newtype BlocksPerSecond = BlocksPerSecond Word
  deriving stock (Generic)
  deriving newtype (Show, Eq, Ord, Aeson.ToJSON, Aeson.FromJSON)

-- We might consider using a smart constructor to make sure it's always in the range [0, 1], but it might be overkill.
newtype NodeStakePercent = NodeStakePercent Double
  deriving stock (Generic)
  deriving newtype (Show)

-- Frequency of IB slots per Praos slots.
newtype IBFrequency = IBFrequency {getIBFrequency ::  Double}
  deriving stock (Generic)
  deriving newtype (Show, Eq, Ord, Aeson.ToJSON, Aeson.FromJSON)

-- Frequency of EB slots per Praos slots.
newtype EBFrequency = EBFrequency Double
  deriving stock (Generic)
  deriving newtype (Show, Eq, Ord, Aeson.ToJSON, Aeson.FromJSON)

--------------------------------------------------------------------------------
-- Model types
--------------------------------------------------------------------------------

data RoleType = IBRole | EBRole | Vote1Role | Vote2Role
  deriving stock (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

newtype NodeId = NodeId Word
  deriving stock (Generic)
  deriving newtype (Show, Eq, Enum, Num, Ord, Aeson.ToJSON, Aeson.FromJSON)

newtype Slot = Slot Word
  deriving stock (Generic)
  deriving newtype (Show, Eq, Ord, Enum, Aeson.ToJSON, Aeson.FromJSON)

tickSlot :: Slot -> Slot
tickSlot = succ

--------------------------------------------------------------------------------
-- Input Blocks
--------------------------------------------------------------------------------

data IB
  = IB
  { ib_slot :: Slot
  , ib_producer :: NodeId
  , ib_size :: NumberOfBits
  }
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

instance HasSizeInBits IB where
  size = ib_size

-- TOOD: for now the IB ref is just the IB itself. Eventually this should become a hash.
newtype IB_Ref = IB_Ref IB
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

ib_ref :: IB -> IB_Ref
ib_ref = IB_Ref -- TODO: eventually this will compute the IB hash.

--------------------------------------------------------------------------------
-- Endorsement Blocks
--------------------------------------------------------------------------------

data EB
  = EB
  { eb_slot :: Slot
  , eb_producer :: NodeId
  , eb_linked_IBs :: [IB_Ref]
  }
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

--------------------------------------------------------------------------------
-- Model
--------------------------------------------------------------------------------

-- TODO: when we connect the model with the server this function should be renamed to something like 'runStandalone'.
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
  TVar m Parameters ->
  m ()
run tracer paramsTVar = do
  world <- init paramsTVar
  params <- readTVarIO paramsTVar
  let totalNodes = 2
      gen = mkStdGen (initialSeed params)
      nodesGens = splitIn totalNodes gen
      -- TODO: for now we don't allow this to be configurable
      stakePercent = NodeStakePercent (1/ fromIntegral totalNodes)
  raceAll
    [ do
        register (NodeId i) world
        let nodeGen = nodesGens !! fromIntegral i
        node (NodeId i) stakePercent nodeGen tracer (schedule totalNodes) world
    | i <- [0 .. totalNodes - 1]
    ]
  where
    splitIn 0 _ = []
    splitIn 1 gen = [gen]
    splitIn n gen = gen0 : splitIn (n-1) gen1
      where
        (gen0, gen1) = split gen

  -- TODO: we need to find a more general and realistic way to model the schedule.
  --
  -- In particular we should add the ledger state needed to determine leadership (eg stake distribution).
  --
  -- Also we would like more than one node to be elected to issue blocks or votes (specially the latter!).
    schedule :: Word -> RoleType -> NodeId -> Slot -> m Bool
    schedule _ IBRole (NodeId nid) (Slot slot) = pure $ slot `mod` (nid + 1) == 0
    schedule totalNodes EBRole _ (Slot slot) = pure $ slot `mod` totalNodes == 0

-- | Determine if the node with the given stake leads.
--
-- We determine this simply by generating a random number @n@ in the
-- interval [0, 1], and returning @True@ iff:
--
-- > n <= asc_I * α
--
-- where @α@ is the given node stake, @f_I@ is the 'IBFrequency' and
--
-- > asc_I = f_I / ceiling f_I
--
leads :: RandomGen g => NodeStakePercent -> IBFrequency -> State g Bool
leads (NodeStakePercent α) (IBFrequency f_I) = do
  generator <- get
  let (n, nextGenerator) = randomR (0, 1) generator
  put nextGenerator
  pure $! n <= asc_I * α
  where
    asc_I = f_I / ceiling' f_I
    ceiling' = fromIntegral . ceiling

-- | Given a number of IB slots, determine if the node with the given
-- stake percent leads on those slots.
leadsMultiple :: RandomGen g => g -> Int -> NodeStakePercent -> IBFrequency -> ([Bool], g)
leadsMultiple generator n stakePercent ibFrequency =
  replicateM n (leads stakePercent ibFrequency) `runState` generator

-- FIXME: for EBs we might want to define this as
--
-- > slot `mod` totalNumberOfNodes == 0

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
  , RandomGen g
  ) =>
  NodeId ->
  NodeStakePercent ->
  g ->
  Tracer m LeiosEvent ->
  Schedule m ->
  OutsideWorld m ->
  m ()
node nodeId nodeStakePercent initialGenerator tracer schedule world = do
  producer `race_` consumer
 where
  producer = do
    clock <- runClock
    let loop generator = do
          slot <- nextSlot clock
          Parameters {f_I} <- getParams world
          let q_I = ceiling $ getIBFrequency f_I -- For practical reasons we want this to be a minimal value.
              (nodeLeads, nextGenerator) = leadsMultiple generator q_I nodeStakePercent f_I
              slotsLed = length $ filter id nodeLeads
          replicateM slotsLed $ produceIB slot
          whenM (hasEBRole slot) $ produceEB slot
          -- traceWith tracer (NextSlot nodeId slot)
          loop nextGenerator
    loop initialGenerator

  consumer = forever $ do
    msg <- nodeId `receiveFrom` world
    case msg of
      MsgIB ib -> do
        -- traceWith tracer (ReceivedIB ib nodeId)
        storeIB nodeId ib world
      MsgEB eb -> do
        traceWith tracer (ReceivedEB eb nodeId)

  produceIB slot = do
    let newIB = IB{ib_slot = slot, ib_producer = nodeId, ib_size = gIBSize}
    traceWith tracer (ProducedIB newIB)
    MsgIB newIB `sendTo` world

  hasEBRole = schedule EBRole nodeId

  produceEB slot = do
    Parameters{_L, λ} <- getParams world
    l_I <- fmap (fmap ib_ref) $ storedIBsBy nodeId world (slice _L slot (λ + 1))
    let newEB = EB{eb_slot = slot, eb_producer = nodeId, eb_linked_IBs = l_I}
    traceWith tracer (ProducedEB newEB)
    MsgEB newEB `sendTo` world

-- | A slice is an interval of slots. @slice _L s x@ returns the slice
-- that is @x@ slices before the slice that contains slot @s@.
--
-- We assume the time to be divided in slots, and the slots to be
-- grouped into slices of length @_L@. The following diagram
-- illustrates the fact that @slice 5 18 2@ should return @1@, because
-- slice @1@ is @2@ slices before slice @3@, which contains slot @18@.
--
-- >
-- >    0     1     2     3
-- > |-----|-----|-----|-----|-----|
-- >                      ↳ s = 18 (slot s is in slice 3)
--
-- In the figure above, @slice _L s x@ will return the interval of slots corresponding to slice 3 [15, 20).
slice :: NumberOfSlots -> Slot -> NumberOfSlices -> Slice
slice (NumberOfSlots _L) (Slot s) (NumberOfSlices x) =
  Slice
    { lb_inclusive = Slot $ (sliceOf s - x) * _L
    , ub_exclusive = Slot $ (sliceOf s - x + 1) * _L
    }
 where
  sliceOf = (`div` _L)

-- | A slice is defined by its lower slot and its (exclusive) upper bound slot.
--
-- See 'isWithin'.
data Slice = Slice
  { lb_inclusive :: Slot
  , ub_exclusive :: Slot
  }
  deriving (Show, Generic)

isWithin :: Slot -> Slice -> Bool
isWithin slot Slice{lb_inclusive, ub_exclusive} =
  lb_inclusive <= slot && slot < ub_exclusive

--------------------------------------------------------------------------------
-- Events
--------------------------------------------------------------------------------

-- FIXME: remove the prefix once this goes in a separate module.
data LeiosEvent
  = NextSlot {nsNodeId :: NodeId, nsSlot :: Slot} -- FIXME: temporary, just for testing purposes.
  | ProducedIB {producedIB :: IB}
  | ReceivedIB {receivedIB :: IB, receivedBy :: NodeId}
  | ProducedEB {producedEB :: EB}
  | ReceivedEB {receivedEB :: EB, receivedBy :: NodeId}
  deriving (Show, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

--------------------------------------------------------------------------------
-- IO simulation
--------------------------------------------------------------------------------

-- | Run the simulation without a webserver. The events are output to
-- the standard output.
runStandalone :: IO ()
runStandalone = do
  let defaultParams =
        Parameters
          { _L = g_L
          , λ = g_λ
          , nodeBandwidth = gNodeBandwidth
          , ibSize = gIBSize
          , f_I = g_f_I
          , f_E = g_f_E
          , initialSeed = 22595838 -- https://xkcd.com/221/. We might want to generate this from the system time, or pass it as parameter.
          }
  paramsTVar <- newTVarIO defaultParams
  events <- newTQueueIO
  run (mkTracer events) paramsTVar `race_` outputToStdout events
 where
  -- FIXME: temporary
  outputToStdout :: TQueue IO Aeson.Value -> IO ()
  outputToStdout events = forever $ do
    atomically (readTQueue events) >>= pPrint

-- runSimulation :: (MonadAsync m, MonadDelay m, MonadSay m)
--   => Tracer m LeiosEvent -> TVar m Parameters -> m ()
-- runSimulation tracer params = run tracer params

--------------------------------------------------------------------------------
-- Blockchain Clock
--------------------------------------------------------------------------------

-- TODO: we might want to add some mechanism to cancel the async tick
-- thread when the thread that has a reference to the returned clock
-- is canceled.
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
  , paramsTVar :: TVar m Parameters
  , storedIBsTVar :: TVar m (Map NodeId [IB])
  -- ^ Downloaded blocks per node
  }

newtype BitsPerSecond = BitsPerSecond Word
  deriving (Eq, Show, Generic, Ord)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

data Msg
  = MsgIB {msgIB :: IB}
  | MsgEB {msgEB :: EB}

instance HasSizeInBits Msg where
  size (MsgIB ib) = size ib
  size (MsgEB eb) = NumberOfBits 1 -- FIXME: for now we assume EB sizes are negligible.

init ::
  forall m.
  (Monad m, MonadSTM m, Applicative m) =>
  TVar m Parameters ->
  m (OutsideWorld m)
init paramsTVar = do
  pqsTVar <- newTVarIO mempty
  storedIBsTVar <- newTVarIO mempty
  pure $ OutsideWorld{pqsTVar = pqsTVar, paramsTVar = paramsTVar, storedIBsTVar = storedIBsTVar}

getParams :: MonadSTM m => OutsideWorld m -> m Parameters
getParams = readTVarIO . paramsTVar

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
      owNodeBandwidth <- nodeBandwidth <$> (atomically $ readTVar (paramsTVar world))
      let msToInt (Microseconds ms) = fromIntegral ms
      threadDelay $ msToInt $ transmissionTime (size msg) owNodeBandwidth
      pure msg

--------------------------------------------------------------------------------
-- Outside World Storage
--------------------------------------------------------------------------------

storeIB :: MonadSTM m => NodeId -> IB -> OutsideWorld m -> m ()
storeIB nodeId ib OutsideWorld{storedIBsTVar} =
  atomically $
    modifyTVar' storedIBsTVar (Map.alter (Just . maybe [ib] (ib :)) nodeId)

-- | Retrieve the downloaded IBs by the given node, which correspond
-- to the given slice. Once retrieved the IBs are deleted.
--
storedIBsBy :: MonadSTM m => NodeId -> OutsideWorld m -> Slice -> m [IB]
storedIBsBy nodeId OutsideWorld{storedIBsTVar} slice = atomically $ do
  storedIBs <- readTVar storedIBsTVar
  case Map.lookup nodeId storedIBs of
    Nothing -> pure []
    Just nodeIdStoredIBs -> do
      let (ibsWithinSlice, ibsOutsideSlice) =
            partition ((`isWithin` slice) . ib_slot) nodeIdStoredIBs
      writeTVar storedIBsTVar (Map.insert nodeId ibsOutsideSlice storedIBs)
      pure ibsWithinSlice

--------------------------------------------------------------------------------
-- A priority queue inside a transactional var
--------------------------------------------------------------------------------

data PQueueTVar m = PQueueTVar {getTQueueTVar :: TVar m (MaxQueue PMsg)}

-- | Wrapper around 'Msg' to implement the priority needed for the priority queue.
newtype PMsg = PMsg Msg

instance Eq PMsg where
  PMsg (MsgIB x) == PMsg (MsgIB y) = ib_slot x == ib_slot y
  PMsg (MsgEB _) == PMsg (MsgEB _) = True -- FIXME: For now EB messages have the same priority
  PMsg (MsgIB _) == PMsg (MsgEB _) = False
  PMsg (MsgEB _) == PMsg (MsgIB _) = False

instance Ord PMsg where
  PMsg (MsgIB x) <= PMsg (MsgIB y) = ib_slot x <= ib_slot y
  PMsg (MsgEB _) <= PMsg (MsgEB _) = True -- FIXME: For now EB messages have the same priority.
  PMsg (MsgIB _) <= PMsg (MsgEB _) = True -- FIXME: For now EB messages take precedence over IB messages.
  PMsg (MsgEB _) <= PMsg (MsgIB _) = False -- FIXME: For now EB messages take precedence over IB messages.

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
