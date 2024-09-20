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
-- \* ✅ Define a better/more-realistic schedule.
-- \* ✅ Add a plot showing: IB created, linked IB, dropped IB x slot.
-- \* Tweak the model parameters.
--
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

import Data.UUID (UUID)
import Control.Applicative (asum)
import Control.Concurrent.Class.MonadSTM.TChan (TChan, newTChanIO, readTChan, writeTChan)
import Control.Concurrent.Class.MonadSTM.TQueue (TQueue, newTQueueIO, readTQueue)
import Control.Concurrent.Class.MonadSTM.TVar (TVar, check, modifyTVar', newTVarIO, readTVar, readTVarIO, writeTVar)
import Control.Monad (foldM, forever, replicateM, replicateM_)
import Control.Monad.Class.MonadAsync (Async, Concurrently (Concurrently, runConcurrently), MonadAsync, async, race_)
import Control.Monad.Class.MonadSTM (MonadSTM, STM, atomically, retry)
import Control.Monad.Class.MonadTimer (MonadDelay, MonadTimer, threadDelay)
import Control.Monad.Extra (whenM)
import Control.Monad.State (State, get, put, runState)
import Control.Tracer (Tracer, traceWith)
import qualified Data.Aeson as Aeson
import Data.Foldable (for_)
import Data.List (partition)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import Data.PQueue.Max (MaxQueue)
import qualified Data.PQueue.Max as PQueue
import Data.Word (Word64)
import GHC.Generics (Generic)
import Leios.Trace (mkTracer)
import System.Random (RandomGen, mkStdGen, random, randomR, split)
import Text.Pretty.Simple (pPrint)

--------------------------------------------------------------------------------
-- Model parameters
--------------------------------------------------------------------------------

-- FIXME: we should add a parameter to determine the number of slots per second (or slot duration).
--
-- TODO: we might want to split this between constants and parameters that can be tweaked at runtime.
data Parameters = Parameters
  { _L            :: NumberOfSlots
  -- ^  Slice length.
  , λ             :: NumberOfSlices
  -- ^ Number of slices (of size '_L') the diffusion period takes.
  , nodeBandwidth :: BitsPerSecond
  , ibSize        :: NumberOfBits
  -- ^ Size of the diffusion block.
  , f_I           :: IBFrequency
  , f_E           :: EBFrequency
  , initialSeed   :: Int
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
newtype IBFrequency = IBFrequency {getIBFrequency :: Double}
  deriving stock (Generic)
  deriving newtype (Show, Eq, Ord, Aeson.ToJSON, Aeson.FromJSON)

-- Frequency of EB slots per Praos slots.
newtype EBFrequency = EBFrequency {getEBFrequency :: Double}
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
  deriving newtype (Show, Eq, Ord, Enum, Num, Aeson.ToJSON, Aeson.FromJSON)

tickSlot :: Slot -> Slot
tickSlot = succ

--------------------------------------------------------------------------------
-- Input Blocks
--------------------------------------------------------------------------------

data IB = IB
  { ib_slot :: Slot
  , ib_producer :: NodeId
  , ib_size :: NumberOfBits
  , ib_UUID :: UUID
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

data EB = EB
  { eb_slot :: Slot
  , eb_producer :: NodeId
  , eb_linked_IBs :: [IB_Ref]
  }
  deriving (Show, Eq, Generic)
  deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

--------------------------------------------------------------------------------
-- Model
--------------------------------------------------------------------------------

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
  TVar m ShouldContinue ->
  m ()
run tracer paramsTVar continueTVar = do
  world <- init paramsTVar
  params <- readTVarIO paramsTVar
  let totalNodes = 2
      gen = mkStdGen (initialSeed params)
      nodesGens = splitIn totalNodes gen
      -- TODO: for now we don't allow this to be configurable
      stakePercent = NodeStakePercent (1 / fromIntegral totalNodes)
  raceAll
    [ do
      register (NodeId i) world
      let nodeGen = nodesGens !! fromIntegral i
      node (NodeId i) stakePercent nodeGen tracer world continueTVar
    | i <- [0 .. totalNodes - 1]
    ]
 where
  splitIn 0 _ = []
  splitIn 1 gen = [gen]
  splitIn n gen = gen0 : splitIn (n - 1) gen1
   where
    (gen0, gen1) = split gen

-- | Determine if the node with the given stake leads.
--
-- We determine this simply by generating a random number @n@ in the
-- interval [0, 1], and returning @True@ iff:
--
-- > n <= asc * α
--
-- where @α@ is the given node stake, @f@ is the frequency of slots and
--
-- > asc = f / ceiling f
leads :: RandomGen g => NodeStakePercent -> Double -> State g Bool
leads (NodeStakePercent α) f_I = do
  generator <- get
  let (n, nextGenerator) = randomR (0, 1) generator
  put nextGenerator
  pure $! n <= asc_I * α
 where
  asc_I = f_I / ceiling' f_I
  ceiling' = fromIntegral . ceiling

-- | Given a number of IB slots, determine if the node with the given
-- stake percent leads on those slots.
leadsMultiple :: RandomGen g => g -> Int -> NodeStakePercent -> Double -> ([Bool], g)
leadsMultiple generator n stakePercent f =
  replicateM n (leads stakePercent f) `runState` generator

raceAll ::
  forall t m a.
  (Foldable t, Functor t, MonadAsync m, MonadTimer m) =>
  t (m a) ->
  m a
raceAll = runConcurrently . asum . fmap Concurrently

data ShouldContinue = Continue | Stop
  deriving (Show, Eq, Generic)

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
  OutsideWorld m ->
  TVar m ShouldContinue ->
  m ()
node nodeId nodeStakePercent initialGenerator tracer world continueTVar = do
  producer `race_` consumer
 where
  producer = do
    clock <- runClock continueTVar
    let loop generator = do
          slot <- nextSlot clock
          traceWith tracer NextSlot{nodeId, slot}
          Parameters{f_I, f_E} <- getParams world
          -- Generate IB blocks
          let (numberOfIBsInThisSlot, generator1) =
                slotsLed generator (getIBFrequency f_I)
          generator2 <- foldM
            produceIB
            generator1
            $ replicate numberOfIBsInThisSlot slot
          -- Generate EB blocks
          let (numberOfEBsInThisSlot, generator3) =
                slotsLed generator2 (getEBFrequency f_E)
          replicateM_ numberOfEBsInThisSlot $ produceEB slot
          -- Continue
          loop generator3
    loop initialGenerator

  consumer = forever $ do
    msg <- nodeId `receiveFrom` world
    case msg of
      MsgIB ib -> do
        -- traceWith tracer (ReceivedIB ib nodeId)
        storeIB nodeId ib world
      MsgEB eb -> do
        traceWith tracer (ReceivedEB eb nodeId)

  slotsLed generator f =
    let
      -- For practical reasons we want this to be a minimal value.
      -- NOTE: What practical reasons?
      q = ceiling f
      (nodeLeads, nextGenerator) =
        leadsMultiple generator q nodeStakePercent f
      in
      (length $ filter id nodeLeads, nextGenerator)

  produceIB generator slot = do
    Parameters{ibSize} <- getParams world
    let
      (uuid,nextGenerator) = random generator
      newIB = IB {
        ib_slot = slot
        , ib_producer = nodeId
        , ib_size = ibSize
        , ib_UUID = uuid
        }
    traceWith tracer (ProducedIB newIB)
    MsgIB newIB `sendTo` world
    pure nextGenerator

  produceEB slot = do
    Parameters{_L, λ} <- getParams world
    l_I <- fmap ib_ref <$> storedIBsBy nodeId world (slice _L slot (λ + 1))
    let newEB = EB{eb_slot = slot, eb_producer = nodeId, eb_linked_IBs = l_I}
    traceWith tracer (ProducedEB newEB)
    MsgEB newEB `sendTo` world

-- | A slice is an interval of slots. @slice _L s x@ returns the slice
-- that is @x@ slices before the slice that contains slot @s@.
--
-- We assume the time to be divided in slots, and the slots to be
-- grouped into slices of length @_L@. The following diagram
-- illustrates the fact that @slice 5 18 2@ should return slide @1@,
-- i.e. interval @[5, 10)@, because slice @1@ is @2@ slices before
-- slice @3@, which contains slot @18@.
--
-- >
-- >    0     1     2     3
-- > |-----|-----|-----|-----|-----|
-- >                      ↳ s = 18 (slot s is in slice 3)
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
  deriving (Show, Eq, Generic)

isWithin :: Slot -> Slice -> Bool
isWithin slot Slice{lb_inclusive, ub_exclusive} =
  lb_inclusive <= slot && slot < ub_exclusive

--------------------------------------------------------------------------------
-- Events
--------------------------------------------------------------------------------

-- FIXME: remove the prefix once this goes in a separate module.
data LeiosEvent
  = NextSlot {nodeId :: NodeId, slot :: Slot} -- FIXME: temporary, just for testing purposes.
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
--
-- Currently, this function does not allow setting the simulation parameters.
runStandalone :: IO ()
runStandalone = do
  let defaultParams =
        Parameters
          { _L = NumberOfSlots 4
          , λ = NumberOfSlices 3
          , nodeBandwidth = BitsPerSecond 100
          , ibSize = NumberOfBits 300
          , f_I = IBFrequency 0.5
          , f_E = EBFrequency 1
          , initialSeed = 22_595_838 -- https://xkcd.com/221/. We might want to generate this from the system time, or pass it as parameter.
          }
  paramsTVar <- newTVarIO defaultParams
  events <- newTQueueIO
  continueTVar <- newTVarIO Continue
  run (mkTracer events) paramsTVar continueTVar `race_` outputToStdout events
 where
  -- FIXME: temporary
  outputToStdout :: TQueue IO Aeson.Value -> IO ()
  outputToStdout events = forever $ do
    atomically (readTQueue events) >>= pPrint

--------------------------------------------------------------------------------
-- Blockchain Clock
--------------------------------------------------------------------------------

-- TODO: we might want to add some mechanism to cancel the async tick
-- thread when the thread that has a reference to the returned clock
-- is canceled.
runClock ::
  (Monad m, MonadSTM m, MonadAsync m, MonadDelay m) =>
  TVar m ShouldContinue ->
  m (Clock m)
runClock continueTVar = do
  -- FIXME: maybe the slot needs to be determined from the chain start time.
  slotTVar <- newTVarIO Nothing
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
    atomically $ do
      shouldContinue <- readTVar continueTVar
      check $ shouldContinue == Continue
      modifyTVar' slotTVar mTickSlot
   where
    mTickSlot Nothing = Just (Slot 0)
    mTickSlot (Just s) = Just (tickSlot s)

-- | Return the next slot, blocking until its time arrives.
nextSlot :: MonadSTM m => Clock m -> m Slot
nextSlot clock = atomically $ do
  currentSlot <- readTVar (slotTVar clock)
  check $ isJust currentSlot
  lastReadSlot <- readTVar (lastReadTVar clock)
  check (currentSlot /= lastReadSlot)
  writeTVar (lastReadTVar clock) currentSlot
  pure $
    fromMaybe
      (error "Impossible! We just checked currentSlot /= Nothing")
      currentSlot

data Clock m = Clock
  { clockAsync :: Async m ()
  , slotTVar :: TVar m (Maybe Slot)
  -- ^ When the clock has not ticked yet this is 'Nothing'
  --
  -- The clock might not have been ticked for the first time because
  -- it started in a paused state (ie the TVar that signals whether
  -- the clock should tick is set to 'Stop'). See 'runClock'.
  , lastReadTVar :: TVar m (Maybe Slot)
  }

--------------------------------------------------------------------------------
-- (very simple) Outside World Model
--------------------------------------------------------------------------------

data OutsideWorld m = OutsideWorld
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
  deriving (Show)

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
-- NOTE: a node will receive it's own message. We could prevent this
-- by including the senders's id in the function type.
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
  m_pqTVar <- Map.lookup nodeId <$> readTVarIO (pqsTVar world)
  case m_pqTVar of
    Nothing -> error $ "Node " <> show nodeId <> " does not exist."
    Just pqTVar -> do
      msg <- pop pqTVar
      owNodeBandwidth <- nodeBandwidth <$> readTVarIO (paramsTVar world)
      threadDelay $ fromIntegral $ transmissionTime (size msg) owNodeBandwidth
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

newtype PQueueTVar m = PQueueTVar {getTQueueTVar :: TVar m (MaxQueue PMsg)}

-- | Wrapper around 'Msg' to implement the priority needed for the priority queue.
newtype PMsg = PMsg Msg
  deriving (Show)

instance Eq PMsg where
  PMsg (MsgIB x) == PMsg (MsgIB y) = ib_slot x == ib_slot y
  PMsg (MsgEB x) == PMsg (MsgEB y) = eb_slot x == eb_slot y
  PMsg (MsgIB _) == PMsg (MsgEB _) = False
  PMsg (MsgEB _) == PMsg (MsgIB _) = False

instance Ord PMsg where
  PMsg (MsgIB x) <= PMsg (MsgIB y) = ib_slot x <= ib_slot y
  PMsg (MsgEB x) <= PMsg (MsgEB y) = eb_slot x <= eb_slot y
  PMsg (MsgIB _) <= PMsg (MsgEB _) = True -- FIXME: For now EB messages take precedence over IB messages.
  PMsg (MsgEB _) <= PMsg (MsgIB _) = False -- FIXME: For now EB messages take precedence over IB messages.

-- TODO: the 'queue' part can be dropped if these functions are put in a separate module.
newPQueue :: (Functor m, MonadSTM m) => m (PQueueTVar m)
newPQueue = PQueueTVar <$> newTVarIO mempty

insertPQueue :: MonadSTM m => Msg -> PQueueTVar m -> STM m ()
insertPQueue msg pqTVar = do
  modifyTVar' (getTQueueTVar pqTVar) (PQueue.insert (PMsg msg))

-- | Take the message at the front of the queue (eg the freshest IB),
-- and delete it from the queue. If the queue is empty, blocks until a
-- message arrives.
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
  deriving newtype (Show, Enum, Num, Real, Integral, Eq, Ord)

-- | .
--
-- PRECONDITION: rate =/ 0.
transmissionTime :: NumberOfBits -> BitsPerSecond -> Microseconds
transmissionTime (NumberOfBits nr_bits) (BitsPerSecond rate) = Microseconds $ ceiling $ seconds * 1_000_000
 where
  seconds :: Double
  seconds = fromIntegral nr_bits / fromIntegral rate
