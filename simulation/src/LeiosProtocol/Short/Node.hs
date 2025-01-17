{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module LeiosProtocol.Short.Node where

import ChanMux
import Control.Category ((>>>))
import Control.Concurrent.Class.MonadMVar
import Control.Concurrent.Class.MonadSTM.TSem
import Control.Exception (assert)
import Control.Monad (forever, guard, when)
import Control.Monad.Class.MonadAsync
import Control.Monad.Class.MonadFork
import Control.Monad.Class.MonadThrow
import Control.Tracer
import Data.Bifunctor
import Data.Coerce (coerce)
import Data.Foldable (forM_)
import Data.Ix (Ix, range)
import Data.List (sort, sortOn)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import LeiosProtocol.Common
import LeiosProtocol.Relay
import qualified LeiosProtocol.RelayBuffer as RB
import LeiosProtocol.Short
import LeiosProtocol.Short.Generate
import qualified LeiosProtocol.Short.Generate as Generate
import LeiosProtocol.TaskMultiQueue
import ModelTCP
import Numeric.Natural (Natural)
import PraosProtocol.BlockFetch (
  BlockFetchControllerState (blocksVar),
  addProducedBlock,
  processWaiting',
 )
import qualified PraosProtocol.Common.Chain as Chain
import qualified PraosProtocol.PraosNode as PraosNode
import STMCompat
import System.Random
import WorkerPool

--------------------------------------------------------------
---- Events
--------------------------------------------------------------

data LeiosEventBlock
  = EventIB !InputBlock
  | EventEB !EndorseBlock
  | EventVote !VoteMsg
  deriving (Show)

data BlockEvent = Generate | Received | EnterState
  deriving (Show)

data LeiosNodeEvent
  = PraosNodeEvent !(PraosNode.PraosNodeEvent RankingBlockBody)
  | LeiosNodeEventCPU !CPUTask
  | LeiosNodeEvent !BlockEvent !LeiosEventBlock
  deriving (Show)

--------------------------------------------------------------
---- Node Config
--------------------------------------------------------------

data LeiosNodeConfig = LeiosNodeConfig
  { leios :: !LeiosConfig
  , rankingBlockFrequencyPerSlot :: !Double
  , nodeId :: !NodeId
  , stake :: !StakeFraction
  , rng :: !StdGen
  -- ^ for block generation
  , baseChain :: !(Chain RankingBlock)
  , rankingBlockPayload :: !Bytes
  -- ^ overall size of txs to include in RBs
  , inputBlockPayload :: !Bytes
  -- ^ overall size of txs to include in IBs
  , processingQueueBound :: !Natural
  , processingCores :: NumCores
  }

data NumCores = Infinite | Finite Int

--------------------------------------------------------------
---- Node State
--------------------------------------------------------------

data LeiosNodeState m = LeiosNodeState
  { praosState :: !(PraosNode.PraosNodeState RankingBlockBody m)
  , relayIBState :: !(RelayIBState m)
  , relayEBState :: !(RelayEBState m)
  , relayVoteState :: !(RelayVoteState m)
  , ibDeliveryTimesVar :: !(TVar m (Map InputBlockId UTCTime))
  , taskQueue :: !(TaskMultiQueue LeiosNodeTask m)
  , waitingForRBVar :: !(TVar m (Map (HeaderHash RankingBlock) [m ()]))
  -- ^ waiting for RB block itself to be validated.
  , waitingForLedgerStateVar :: !(TVar m (Map (HeaderHash RankingBlock) [m ()]))
  -- ^ waiting for ledger state of RB block to be validated.
  , ledgerStateVar :: !(TVar m (Map (HeaderHash RankingBlock) LedgerState))
  , ibsNeededForEBVar :: !(TVar m (Map EndorseBlockId (Set InputBlockId)))
  }

data LeiosNodeTask
  = ValIB
  | ValEB
  | ValVote
  | ValRB
  | ValIH
  | ValRH
  | GenIB
  | GenEB
  | GenVote
  | GenRB
  deriving (Eq, Ord, Ix, Bounded, Show)

type RelayIBState = RelayConsumerSharedState InputBlockId InputBlockHeader InputBlockBody
type RelayEBState = RelayConsumerSharedState EndorseBlockId EndorseBlockId EndorseBlock
type RelayVoteState = RelayConsumerSharedState VoteId VoteId VoteMsg

data LedgerState = LedgerState

data ValidationRequest m
  = ValidateRB !RankingBlock !(m ())
  | ValidateIBS ![(InputBlockHeader, InputBlockBody)] !UTCTime !([(InputBlockHeader, InputBlockBody)] -> STM m ())
  | ValidateEBS ![EndorseBlock] !([EndorseBlock] -> STM m ())
  | ValidateVotes ![VoteMsg] !([VoteMsg] -> STM m ())

--------------------------------------------------------------
--- Messages
--------------------------------------------------------------

type RelayIBMessage = RelayMessage InputBlockId InputBlockHeader InputBlockBody
type RelayEBMessage = RelayMessage EndorseBlockId EndorseBlockId EndorseBlock
type RelayVoteMessage = RelayMessage VoteId VoteId VoteMsg
type PraosMessage = PraosNode.PraosMessage RankingBlockBody

data LeiosMessage
  = RelayIB {fromRelayIB :: !RelayIBMessage}
  | RelayEB {fromRelayEB :: !RelayEBMessage}
  | RelayVote {fromRelayVote :: !RelayVoteMessage}
  | PraosMsg {fromPraosMsg :: !PraosMessage}
  deriving (Show)

data Leios f = Leios
  { protocolIB :: f RelayIBMessage
  , protocolEB :: f RelayEBMessage
  , protocolVote :: f RelayVoteMessage
  , protocolPraos :: PraosNode.Praos RankingBlockBody f
  }

instance MessageSize LeiosMessage where
  messageSizeBytes lm = case lm of
    RelayIB m -> messageSizeBytes m
    RelayEB m -> messageSizeBytes m
    RelayVote m -> messageSizeBytes m
    PraosMsg m -> messageSizeBytes m

instance MuxBundle Leios where
  type MuxMsg Leios = LeiosMessage
  toFromMuxMsgBundle =
    Leios
      { protocolIB = ToFromMuxMsg RelayIB fromRelayIB
      , protocolEB = ToFromMuxMsg RelayEB fromRelayEB
      , protocolVote = ToFromMuxMsg RelayVote fromRelayVote
      , protocolPraos = case toFromMuxMsgBundle @(PraosNode.Praos RankingBlockBody) of
          PraosNode.Praos a b -> PraosNode.Praos (p >>> a) (p >>> b)
      }
   where
    p = ToFromMuxMsg PraosMsg fromPraosMsg

  traverseMuxBundle f (Leios a b c d) = Leios <$> f a <*> f b <*> f c <*> traverseMuxBundle f d

--------------------------------------------------------------

newRelayState ::
  (Ord id, MonadSTM m) =>
  m (RelayConsumerSharedState id header body m)
newRelayState = do
  relayBufferVar <- newTVarIO RB.empty
  inFlightVar <- newTVarIO Set.empty
  return $ RelayConsumerSharedState{relayBufferVar, inFlightVar}

setupRelay ::
  (Ord id, MonadAsync m, MonadSTM m, MonadDelay m, MonadTime m) =>
  RelayConsumerConfig id header body m ->
  RelayConsumerSharedState id header body m ->
  [Chan m (RelayMessage id header body)] ->
  [Chan m (RelayMessage id header body)] ->
  m [m ()]
setupRelay cfg consumerSST followers peers = do
  let producerSST = RelayProducerSharedState{relayBufferVar = asReadOnly consumerSST.relayBufferVar}
  let consumers = map (runRelayConsumer cfg consumerSST) peers
  let producers = map (runRelayProducer cfg.relay producerSST) followers
  return $ consumers ++ producers

type SubmitBlocks m header body =
  [(header, body)] ->
  UTCTime ->
  ([(header, body)] -> STM m ()) ->
  m ()

relayIBConfig ::
  (MonadAsync m, MonadSTM m, MonadDelay m, MonadTime m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  ([InputBlockHeader] -> m ()) ->
  SubmitBlocks m InputBlockHeader InputBlockBody ->
  RelayConsumerConfig InputBlockId InputBlockHeader InputBlockBody m
relayIBConfig _tracer _cfg validateHeaders submitBlocks =
  RelayConsumerConfig
    { relay = RelayConfig{maxWindowSize = 100}
    , headerId = (.id)
    , validateHeaders
    , -- TODO: add prioritization policy to LeiosConfig
      prioritize = sortOn (Down . (.slot)) . Map.elems
    , submitPolicy = SubmitAll
    , maxHeadersToRequest = 100
    , maxBodiesToRequest = 1
    , submitBlocks
    }

relayEBConfig ::
  MonadDelay m =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  SubmitBlocks m EndorseBlockId EndorseBlock ->
  RelayConsumerConfig EndorseBlockId EndorseBlockId EndorseBlock m
relayEBConfig _tracer _cfg submitBlocks =
  RelayConsumerConfig
    { relay = RelayConfig{maxWindowSize = 100}
    , headerId = id
    , validateHeaders = const $ return ()
    , -- TODO: add prioritization policy to LeiosConfig?
      prioritize = sort . Map.elems
    , submitPolicy = SubmitAll
    , maxHeadersToRequest = 100
    , maxBodiesToRequest = 1 -- should we chunk bodies here?
    , submitBlocks
    }

relayVoteConfig ::
  MonadDelay m =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  SubmitBlocks m VoteId VoteMsg ->
  RelayConsumerConfig VoteId VoteId VoteMsg m
relayVoteConfig _tracer _cfg submitBlocks =
  RelayConsumerConfig
    { relay = RelayConfig{maxWindowSize = 100}
    , headerId = id
    , validateHeaders = const $ return ()
    , -- TODO: add prioritization policy to LeiosConfig?
      prioritize = sort . Map.elems
    , submitPolicy = SubmitAll
    , maxHeadersToRequest = 100
    , maxBodiesToRequest = 1 -- should we chunk bodies here?
    , submitBlocks
    }

queueAndWait :: (MonadSTM m, MonadDelay m) => LeiosNodeState m -> LeiosNodeTask -> [CPUTask] -> m ()
queueAndWait _st _lbl [] = return ()
queueAndWait st lbl ds = do
  let l = fromIntegral $ length ds
  sem <- atomically $ do
    sem <- newTSem (1 - l)
    forM_ ds $ \task -> do
      writeTMQueue st.taskQueue lbl (task, atomically $ signalTSem sem)
    return sem
  atomically $ waitTSem sem

newLeiosNodeState ::
  forall m.
  (MonadMVar m, MonadSTM m) =>
  LeiosNodeConfig ->
  m (LeiosNodeState m)
newLeiosNodeState cfg = do
  praosState <- PraosNode.newPraosNodeState cfg.baseChain
  relayIBState <- newRelayState
  relayEBState <- newRelayState
  relayVoteState <- newRelayState
  ibDeliveryTimesVar <- newTVarIO Map.empty
  ibsNeededForEBVar <- newTVarIO Map.empty
  ledgerStateVar <- newTVarIO Map.empty
  waitingForRBVar <- newTVarIO Map.empty
  waitingForLedgerStateVar <- newTVarIO Map.empty
  taskQueue <- atomically $ newTaskMultiQueue cfg.processingQueueBound
  return $ LeiosNodeState{..}

leiosNode ::
  forall m.
  ( MonadMVar m
  , MonadFork m
  , MonadAsync m
  , MonadSTM m
  , MonadTime m
  , MonadDelay m
  , MonadMonotonicTimeNSec m
  , MonadCatch m
  ) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  [Leios (Chan m)] ->
  [Leios (Chan m)] ->
  m [m ()]
leiosNode tracer cfg followers peers = do
  leiosState@LeiosNodeState{..} <- newLeiosNodeState cfg
  let
    traceReceived :: [a] -> (a -> LeiosEventBlock) -> m ()
    traceReceived xs f = mapM_ (traceWith tracer . LeiosNodeEvent Received . f) xs

  let dispatch = dispatchValidation tracer cfg leiosState
  -- tracing for RB already covered in blockFetchConsumer.
  let submitRB rb completion = dispatch $! ValidateRB rb completion
  let submitIB xs deliveryTime completion = do
        traceReceived xs $ EventIB . uncurry InputBlock
        dispatch $! ValidateIBS xs deliveryTime completion
  let submitVote (map snd -> xs) _ completion = do
        traceReceived xs EventVote
        dispatch $! ValidateVotes xs $ completion . map (\v -> (v.id, v))
  let submitEB (map snd -> xs) _ completion = do
        traceReceived xs EventEB
        dispatch $! ValidateEBS xs $ completion . map (\eb -> (eb.id, eb))
  let valHeaderIB =
        queueAndWait leiosState ValIH . map (flip CPUTask "ValIH" . cfg.leios.delays.inputBlockHeaderValidation)
  let valHeaderRB h = do
        let !delay = cfg.leios.praos.headerValidationDelay h
        queueAndWait leiosState ValRH [CPUTask delay "ValRH"]

  praosThreads <-
    PraosNode.setupPraosThreads'
      (contramap PraosNodeEvent tracer)
      cfg.leios.praos
      valHeaderRB
      submitRB
      praosState
      (map protocolPraos followers)
      (map protocolPraos peers)

  ibThreads <-
    setupRelay
      (relayIBConfig tracer cfg valHeaderIB submitIB)
      relayIBState
      (map protocolIB followers)
      (map protocolIB peers)

  ebThreads <-
    setupRelay
      (relayEBConfig tracer cfg submitEB)
      relayEBState
      (map protocolEB followers)
      (map protocolEB peers)

  voteThreads <-
    setupRelay
      (relayVoteConfig tracer cfg submitVote)
      relayVoteState
      (map protocolVote followers)
      (map protocolVote peers)

  let processWaitingForRB =
        processWaiting'
          praosState.blockFetchControllerState.blocksVar
          waitingForRBVar

  let processWaitingForLedgerState =
        processWaiting'
          ledgerStateVar
          waitingForLedgerStateVar

  let processingThreads =
        [ processCPUTasks cfg.processingCores (contramap LeiosNodeEventCPU tracer) leiosState.taskQueue
        , processWaitingForRB
        , processWaitingForLedgerState
        ]

  let blockGenerationThreads = [generator tracer cfg leiosState]

  let computeLedgerStateThreads = [computeLedgerStateThread tracer cfg leiosState]

  -- TODO: expiration times to be decided. At least need EB/IBs to be
  -- around long enough to compute ledger state if they end in RB.
  let pruningThreads = []

  return $
    concat
      [ processingThreads
      , blockGenerationThreads
      , ibThreads
      , ebThreads
      , voteThreads
      , coerce praosThreads
      , computeLedgerStateThreads
      , pruningThreads
      ]

processCPUTasks ::
  (MonadSTM m, MonadDelay m, MonadMonotonicTimeNSec m, MonadFork m, MonadAsync m, MonadCatch m) =>
  NumCores ->
  Tracer m CPUTask ->
  TaskMultiQueue LeiosNodeTask m ->
  m ()
processCPUTasks Infinite tracer queue = forever $ runInfParallelBlocking tracer queue
processCPUTasks (Finite n) tracer queue = newBoundedWorkerPool n [taskSource l | l <- range (minBound, maxBound)]
 where
  taskSource l = do
    (cpu, m) <- readTMQueue queue l
    var <- newEmptyTMVar
    let action = do
          traceWith tracer cpu
          threadDelay (cpuTaskDuration cpu)
          m
    -- TODO: read from var and log exception.
    return $ Task action var

computeLedgerStateThread ::
  forall m.
  (MonadMVar m, MonadFork m, MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  LeiosNodeState m ->
  m ()
computeLedgerStateThread _tracer _cfg st = forever $ do
  _readyLedgerState <- atomically $ do
    blocks <- readTVar st.praosState.blockFetchControllerState.blocksVar
    when (Map.null blocks) retry
    ledgerMissing <- Map.elems . (blocks Map.\\) <$> readTVar st.ledgerStateVar
    when (null ledgerMissing) retry
    ibsNeededForEB <- readTVar st.ibsNeededForEBVar
    let readyLedgerState =
          [ (blockHash rb, LedgerState)
          | rb <- ledgerMissing
          , flip all rb.blockBody.endorseBlocks $ \(ebId, _) ->
              Map.lookup ebId ibsNeededForEB == Just Set.empty
          ]
    when (null readyLedgerState) retry
    modifyTVar' st.ledgerStateVar (`Map.union` Map.fromList readyLedgerState)
    return readyLedgerState
  -- TODO? trace readyLedgerState
  return ()

dispatchValidation ::
  forall m.
  (MonadMVar m, MonadFork m, MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  LeiosNodeState m ->
  ValidationRequest m ->
  m ()
dispatchValidation tracer cfg leiosState req =
  atomically $ mapM_ (uncurry $ writeTMQueue leiosState.taskQueue) =<< go req
 where
  queue = atomically . mapM_ (uncurry $ writeTMQueue leiosState.taskQueue)
  labelTask (tag, (f, m)) = (tag, (f (T.pack (show tag)), m))
  valRB rb m = do
    let !delay = cfg.leios.praos.blockValidationDelay rb
    labelTask (ValRB, (CPUTask delay, m))
  valIB x deliveryTime completion =
    let
      !delay = CPUTask $ cfg.leios.delays.inputBlockValidation (uncurry InputBlock x)
      task = atomically $ do
        completion [x]

        -- NOTE: voting relies on delivery times for IBs
        modifyTVar'
          leiosState.ibDeliveryTimesVar
          (Map.insertWith min (fst x).id deliveryTime)

        -- TODO: likely needs optimization
        modifyTVar' leiosState.ibsNeededForEBVar (Map.map (Set.delete (fst x).id))
     in
      labelTask (ValIB, (delay, task >> traceEnterState [uncurry InputBlock x] EventIB))
  valEB eb completion = labelTask . (ValEB,) . (CPUTask $ cfg.leios.delays.endorseBlockValidation eb,) $ do
    atomically $ do
      completion [eb]
      ibs <- RB.keySet <$> readTVar leiosState.relayIBState.relayBufferVar
      let ibsNeeded = Map.fromList [(eb.id, Set.fromList eb.inputBlocks Set.\\ ibs)]
      modifyTVar' leiosState.ibsNeededForEBVar (`Map.union` ibsNeeded)
    traceEnterState [eb] EventEB
  valVote v completion = labelTask . (ValVote,) . (CPUTask $ cfg.leios.delays.voteMsgValidation v,) $ do
    atomically $ completion [v]
    traceEnterState [v] EventVote

  go :: ValidationRequest m -> STM m [(LeiosNodeTask, (CPUTask, m ()))]
  go x = case x of
    ValidateRB rb completion -> do
      let task = valRB rb completion
      case blockPrevHash rb of
        GenesisHash -> do
          return [task]
        BlockHash prev -> do
          let var =
                assert (rb.blockBody.payload >= 0) $
                  if rb.blockBody.payload == 0
                    then leiosState.waitingForRBVar
                    -- TODO: assumes payload can be validated without content of EB, check with spec.
                    else leiosState.waitingForLedgerStateVar
          modifyTVar' var $ Map.insertWith (++) prev [queue [task]]
          return []
    ValidateIBS ibs deliveryTime completion -> do
      -- NOTE: IBs with an RB reference have to wait for ledger state of that RB.
      let waitingLedgerState =
            Map.fromListWith
              (++)
              [ (rbHash, [queue [valIB ib deliveryTime completion]])
              | ib <- ibs
              , BlockHash rbHash <- [(fst ib).rankingBlock]
              ]

      modifyTVar' leiosState.waitingForLedgerStateVar (`Map.union` waitingLedgerState)

      return [valIB ib deliveryTime completion | ib@(h, _) <- ibs, GenesisHash <- [h.rankingBlock]]
    ValidateEBS ebs completion -> do
      -- NOTE: block references are only inspected during voting.
      return [valEB eb completion | eb <- ebs]
    ValidateVotes vs completion -> do
      return [valVote v completion | v <- vs]
  traceEnterState :: [a] -> (a -> LeiosEventBlock) -> m ()
  traceEnterState xs f = forM_ xs $ traceWith tracer . LeiosNodeEvent EnterState . f

generator ::
  forall m.
  (MonadMVar m, MonadFork m, MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  LeiosNodeState m ->
  m ()
generator tracer cfg st = do
  schedule <- mkSchedule cfg
  let buffers = mkBuffersView cfg st
  let
    withDelay Nothing (_lbl, m) = m
    withDelay (Just d) (lbl, m) = atomically $ writeTMQueue st.taskQueue lbl (d, m)
  let
    submitOne :: (Maybe CPUTask, SomeAction) -> m ()
    submitOne (delay, x) = withDelay delay $
      case x of
        SomeAction Generate.Base rb0 -> (GenRB,) $ do
          rb <- atomically $ do
            ha <- Chain.headAnchor <$> PraosNode.preferredChain st.praosState
            let rb = fixSize cfg.leios $ fixupBlock ha rb0
            addProducedBlock st.praosState.blockFetchControllerState rb
            return rb
          traceWith tracer (PraosNodeEvent (PraosNodeEventGenerate rb))
        SomeAction Generate.Propose ibs -> (GenIB,) $ forM_ ibs $ \ib -> do
          atomically $ modifyTVar' st.relayIBState.relayBufferVar (RB.snoc ib.header.id (ib.header, ib.body))
          traceWith tracer (LeiosNodeEvent Generate (EventIB ib))
        SomeAction Generate.Endorse eb -> (GenEB,) $ do
          atomically $ modifyTVar' st.relayEBState.relayBufferVar (RB.snoc eb.id (eb.id, eb))
          traceWith tracer (LeiosNodeEvent Generate (EventEB eb))
        SomeAction Generate.Vote v -> (GenVote,) $ do
          atomically $ modifyTVar' st.relayVoteState.relayBufferVar (RB.snoc v.id (v.id, v))
          traceWith tracer (LeiosNodeEvent Generate (EventVote v))
  let LeiosNodeConfig{..} = cfg
  blockGenerator $ BlockGeneratorConfig{submit = mapM_ submitOne, ..}

mkBuffersView :: forall m. MonadSTM m => LeiosNodeConfig -> LeiosNodeState m -> BuffersView m
mkBuffersView cfg st = BuffersView{..}
 where
  newRBData = do
    bufferEB <- map snd . RB.values <$> readTVar st.relayEBState.relayBufferVar
    bufferVotes <- map snd . RB.values <$> readTVar st.relayVoteState.relayBufferVar
    -- TODO: cache?
    let votesForEB =
          Map.fromListWith
            Map.union
            [ (eb, Map.singleton v.id v.votes)
            | v <- bufferVotes
            , eb <- v.endorseBlocks
            ]
    let totalVotes = fromIntegral . sum . Map.elems
    let tryCertify eb = do
          votes <- Map.lookup eb.id votesForEB
          guard (cfg.leios.votesForCertificate <= totalVotes votes)
          return $! (eb.id,) $! mkCertificate cfg.leios votes

    -- TODO: cache index of EBs ordered by .slot descending?
    let freshestCertifiedEB = listToMaybe . mapMaybe tryCertify . sortOn (Down . (.slot)) $ bufferEB
    return $
      NewRankingBlockData
        { freshestCertifiedEB
        , txsPayload = cfg.rankingBlockPayload
        }
  newIBData = do
    ledgerState <- readTVar st.ledgerStateVar
    referenceRankingBlock <-
      Chain.headHash . Chain.dropUntil (flip Map.member ledgerState . blockHash)
        <$> PraosNode.preferredChain st.praosState
    let txsPayload = cfg.inputBlockPayload
    return $ NewInputBlockData{referenceRankingBlock, txsPayload}
  ibs = do
    buffer <- readTVar st.relayIBState.relayBufferVar
    times <- readTVar st.ibDeliveryTimesVar
    let generatedCheck r =
          map (.id)
            . filter (\ib -> ib.slot `inRange` r)
            . map fst
            . RB.values
            $ buffer
        receivedByCheck slot =
          filter
            ( maybe False (<= slotTime cfg.leios.praos.slotConfig slot)
                . flip Map.lookup times
            )
        validInputBlocks q = receivedByCheck q.receivedBy $ generatedCheck q.generatedBetween
    return InputBlocksSnapshot{..}
  ebs = do
    buffer <- readTVar st.relayEBState.relayBufferVar
    let validEndorseBlocks r =
          filter (\eb -> eb.slot `inRange` r) . map snd . RB.values $ buffer
    return EndorseBlocksSnapshot{..}

mkSchedule :: MonadSTM m => LeiosNodeConfig -> m (SlotNo -> m [(SomeRole, Word64)])
mkSchedule cfg = mkScheduler cfg.rng rates
 where
  rates slot =
    (map . second . map)
      (nodeRate cfg.stake)
      [ (SomeRole Generate.Propose, inputBlockRate cfg.leios slot)
      , (SomeRole Generate.Endorse, endorseBlockRate cfg.leios slot)
      , (SomeRole Generate.Vote, votingRate cfg.leios slot)
      , (SomeRole Generate.Base, [NetworkRate cfg.rankingBlockFrequencyPerSlot])
      ]
