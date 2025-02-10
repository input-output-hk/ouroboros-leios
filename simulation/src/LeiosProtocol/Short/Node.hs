{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoFieldSelectors #-}

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
import Data.Ix (Ix)
import Data.List (sortOn)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Traversable
import Data.Tuple (swap)
import LeiosProtocol.Common
import LeiosProtocol.Relay
import qualified LeiosProtocol.RelayBuffer as RB
import LeiosProtocol.Short
import LeiosProtocol.Short.Generate
import qualified LeiosProtocol.Short.Generate as Generate
import Numeric.Natural (Natural)
import PraosProtocol.BlockFetch (
  BlockFetchControllerState (blocksVar),
  addProducedBlock,
  processWaiting',
 )
import qualified PraosProtocol.Common.Chain as Chain
import qualified PraosProtocol.PraosNode as PraosNode
import STMCompat
import SimTypes (cpuTask)
import System.Random

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
  , slotConfig :: !SlotConfig
  , nodeId :: !NodeId
  , stake :: !StakeFraction
  , rng :: !StdGen
  -- ^ for block generation
  , baseChain :: !(Chain RankingBlock)
  , processingQueueBound :: !Natural
  , processingCores :: NumCores
  }

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
  , waitingForRBVar :: !(TVar m (Map (HeaderHash RankingBlock) [STM m ()]))
  -- ^ waiting for RB block itself to be validated.
  , waitingForLedgerStateVar :: !(TVar m (Map (HeaderHash RankingBlock) [STM m ()]))
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
type RelayEBState = RelayConsumerSharedState EndorseBlockId (RelayHeader EndorseBlockId) EndorseBlock
type RelayVoteState = RelayConsumerSharedState VoteId (RelayHeader VoteId) VoteMsg

data LedgerState = LedgerState

data ValidationRequest m
  = ValidateRB !RankingBlock !(m ())
  | ValidateIBS ![(InputBlockHeader, InputBlockBody)] !UTCTime !([(InputBlockHeader, InputBlockBody)] -> STM m ())
  | ValidateEBS ![EndorseBlock] !([EndorseBlock] -> STM m ())
  | ValidateVotes ![VoteMsg] !([VoteMsg] -> STM m ())

--------------------------------------------------------------
--- Messages
--------------------------------------------------------------

data RelayHeader id = RelayHeader {id :: !id, slot :: !SlotNo}
  deriving (Show)

instance MessageSize id => MessageSize (RelayHeader id) where
  messageSizeBytes (RelayHeader x y) = messageSizeBytes x + messageSizeBytes y

type RelayIBMessage = RelayMessage InputBlockId InputBlockHeader InputBlockBody
type RelayEBMessage = RelayMessage EndorseBlockId (RelayHeader EndorseBlockId) EndorseBlock
type RelayVoteMessage = RelayMessage VoteId (RelayHeader VoteId) VoteMsg
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
      { protocolIB = ToFromMuxMsg RelayIB (.fromRelayIB)
      , protocolEB = ToFromMuxMsg RelayEB (.fromRelayEB)
      , protocolVote = ToFromMuxMsg RelayVote (.fromRelayVote)
      , protocolPraos = case toFromMuxMsgBundle @(PraosNode.Praos RankingBlockBody) of
          PraosNode.Praos a b -> PraosNode.Praos (p >>> a) (p >>> b)
      }
   where
    p = ToFromMuxMsg PraosMsg (.fromPraosMsg)

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
relayIBConfig _tracer cfg validateHeaders submitBlocks =
  RelayConsumerConfig
    { relay = RelayConfig{maxWindowSize = coerce cfg.leios.ibDiffusion.maxWindowSize}
    , headerId = (.id)
    , validateHeaders
    , prioritize = prioritize cfg.leios.ibDiffusion.strategy (.slot)
    , submitPolicy = SubmitAll
    , maxHeadersToRequest = cfg.leios.ibDiffusion.maxHeadersToRequest
    , maxBodiesToRequest = cfg.leios.ibDiffusion.maxBodiesToRequest
    , submitBlocks
    }

relayEBConfig ::
  MonadDelay m =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  SubmitBlocks m EndorseBlockId EndorseBlock ->
  RelayConsumerConfig EndorseBlockId (RelayHeader EndorseBlockId) EndorseBlock m
relayEBConfig _tracer cfg submitBlocks =
  RelayConsumerConfig
    { relay = RelayConfig{maxWindowSize = coerce cfg.leios.ebDiffusion.maxWindowSize}
    , headerId = (.id)
    , validateHeaders = const $ return ()
    , prioritize = prioritize cfg.leios.ebDiffusion.strategy (.slot)
    , submitPolicy = SubmitAll
    , maxHeadersToRequest = cfg.leios.ebDiffusion.maxHeadersToRequest
    , maxBodiesToRequest = cfg.leios.ebDiffusion.maxBodiesToRequest
    , submitBlocks = \hbs t k ->
        submitBlocks (map (first (.id)) hbs) t (k . map (\(i, b) -> (RelayHeader i b.slot, b)))
    }

relayVoteConfig ::
  MonadDelay m =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  SubmitBlocks m VoteId VoteMsg ->
  RelayConsumerConfig VoteId (RelayHeader VoteId) VoteMsg m
relayVoteConfig _tracer cfg submitBlocks =
  RelayConsumerConfig
    { relay = RelayConfig{maxWindowSize = coerce cfg.leios.voteDiffusion.maxWindowSize}
    , headerId = (.id)
    , validateHeaders = const $ return ()
    , prioritize = prioritize cfg.leios.voteDiffusion.strategy (.slot)
    , submitPolicy = SubmitAll
    , maxHeadersToRequest = cfg.leios.voteDiffusion.maxHeadersToRequest
    , maxBodiesToRequest = cfg.leios.voteDiffusion.maxBodiesToRequest
    , submitBlocks = \hbs t k ->
        submitBlocks (map (first (.id)) hbs) t (k . map (\(i, b) -> (RelayHeader i b.slot, b)))
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
        queueAndWait leiosState ValIH . map (cpuTask "ValIH" cfg.leios.delays.inputBlockHeaderValidation)
  let valHeaderRB h = do
        let !task = cpuTask "ValRH" cfg.leios.praos.headerValidationDelay h
        queueAndWait leiosState ValRH [task]

  praosThreads <-
    PraosNode.setupPraosThreads'
      (contramap PraosNodeEvent tracer)
      cfg.leios.praos
      valHeaderRB
      submitRB
      praosState
      (map (.protocolPraos) followers)
      (map (.protocolPraos) peers)

  ibThreads <-
    setupRelay
      (relayIBConfig tracer cfg valHeaderIB submitIB)
      relayIBState
      (map (.protocolIB) followers)
      (map (.protocolIB) peers)

  ebThreads <-
    setupRelay
      (relayEBConfig tracer cfg submitEB)
      relayEBState
      (map (.protocolEB) followers)
      (map (.protocolEB) peers)

  voteThreads <-
    setupRelay
      (relayVoteConfig tracer cfg submitVote)
      relayVoteState
      (map (.protocolVote) followers)
      (map (.protocolVote) peers)

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
  let pruningThreads = case cfg.leios of
        LeiosConfig{pipeline = SingSplitVote} ->
          [pruneVoteBuffer tracer cfg leiosState]
        _ -> []

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

pruneVoteBuffer ::
  (Monad m, MonadDelay m, MonadTime m, MonadSTM m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  LeiosNodeState m ->
  m ()
pruneVoteBuffer _tracer cfg st = go (toEnum 0)
 where
  go p = do
    let last_vote_recv = snd $ stageRangeOf cfg.leios p VoteRecv
    let last_vote_send = snd $ stageRangeOf cfg.leios p VoteSend
    _ <- waitNextSlot cfg.slotConfig (succ last_vote_recv)
    atomically $ do
      modifyTVar' st.relayVoteState.relayBufferVar $
        RB.filter $
          \RB.EntryWithTicket{value} -> (snd value).slot <= last_vote_send
    go (succ p)

computeLedgerStateThread ::
  forall m.
  (MonadMVar m, MonadFork m, MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  LeiosNodeState m ->
  m ()
computeLedgerStateThread _tracer _cfg st = forever $ do
  _readyLedgerState <- atomically $ do
    -- TODO: this will get more costly as the base chain grows,
    -- however it grows much more slowly than anything else.
    blocks <- readTVar st.praosState.blockFetchControllerState.blocksVar
    when (Map.null blocks) retry
    ledgerState <- readTVar st.ledgerStateVar
    let ledgerMissing = Map.elems $ blocks Map.\\ ledgerState
    when (null ledgerMissing) retry
    let ledgerEligible = flip filter ledgerMissing $ \blk ->
          case blockPrevHash blk of
            GenesisHash -> True
            BlockHash prev -> prev `Map.member` ledgerState
    when (null ledgerEligible) retry

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

adoptIB :: MonadSTM m => LeiosNodeState m -> InputBlock -> UTCTime -> STM m ()
adoptIB leiosState ib deliveryTime = do
  -- NOTE: voting relies on delivery times for IBs
  modifyTVar'
    leiosState.ibDeliveryTimesVar
    (Map.insertWith min ib.id deliveryTime)

  -- TODO: likely needs optimization, although EBs also grow slowly.
  modifyTVar' leiosState.ibsNeededForEBVar (Map.map (Set.delete ib.id))

adoptEB :: MonadSTM m => LeiosNodeState m -> EndorseBlock -> STM m ()
adoptEB leiosState eb = do
  ibs <- RB.keySet <$> readTVar leiosState.relayIBState.relayBufferVar
  let ibsNeeded = Map.fromList [(eb.id, Set.fromList eb.inputBlocks Set.\\ ibs)]
  modifyTVar' leiosState.ibsNeededForEBVar (`Map.union` ibsNeeded)

dispatchValidation ::
  forall m.
  (MonadMVar m, MonadFork m, MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  LeiosNodeState m ->
  ValidationRequest m ->
  m ()
dispatchValidation tracer cfg leiosState req =
  atomically $ queue =<< go req
 where
  queue = mapM_ (uncurry $ writeTMQueue leiosState.taskQueue)
  labelTask (tag, (f, m)) = let !task = f (show tag) in (tag, (task, m))
  valRB rb m = do
    let task prefix = cpuTask prefix cfg.leios.praos.blockValidationDelay rb
    labelTask (ValRB, (task, m))
  valIB x@(uncurry InputBlock -> ib) deliveryTime completion =
    let
      delay prefix = cpuTask prefix cfg.leios.delays.inputBlockValidation ib
      task = atomically $ do
        completion [x]
        adoptIB leiosState ib deliveryTime
     in
      labelTask (ValIB, (delay, task >> traceEnterState [uncurry InputBlock x] EventIB))
  valEB eb completion = labelTask . (ValEB,) . (\p -> cpuTask p cfg.leios.delays.endorseBlockValidation eb,) $ do
    atomically $ do
      completion [eb]
      adoptEB leiosState eb
    traceEnterState [eb] EventEB
  valVote v completion = labelTask . (ValVote,) . (\p -> cpuTask p cfg.leios.delays.voteMsgValidation v,) $ do
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
    withDelay d (lbl, m) = do
      -- cannot print id of generated RB until after it's generated,
      -- the id of the generated block can be found in the generated event emitted at the time the task ends.
      let !c = CPUTask d (T.pack $ show lbl)
      atomically $ writeTMQueue st.taskQueue lbl (c, m)
  let
    submitOne :: (DiffTime, SomeAction) -> m ()
    submitOne (delay, x) = withDelay delay $
      case x of
        SomeAction Generate.Base rb0 -> (GenRB,) $ do
          (rb, newChain) <- atomically $ do
            chain <- PraosNode.preferredChain st.praosState
            let rb = fixSize cfg.leios $ fixupBlock (Chain.headAnchor chain) rb0
            addProducedBlock st.praosState.blockFetchControllerState rb
            return (rb, chain :> rb)
          traceWith tracer (PraosNodeEvent (PraosNodeEventGenerate rb))
          traceWith tracer (PraosNodeEvent (PraosNodeEventNewTip newChain))
        SomeAction Generate.Propose ib -> (GenIB,) $ do
          now <- getCurrentTime
          atomically $ do
            modifyTVar' st.relayIBState.relayBufferVar (RB.snoc ib.header.id (ib.header, ib.body))
            adoptIB st ib now
          traceWith tracer (LeiosNodeEvent Generate (EventIB ib))
        SomeAction Generate.Endorse eb -> (GenEB,) $ do
          atomically $ do
            modifyTVar' st.relayEBState.relayBufferVar (RB.snoc eb.id (RelayHeader eb.id eb.slot, eb))
            adoptEB st eb
          traceWith tracer (LeiosNodeEvent Generate (EventEB eb))
        SomeAction Generate.Vote v -> (GenVote,) $ do
          atomically $ modifyTVar' st.relayVoteState.relayBufferVar (RB.snoc v.id (RelayHeader v.id v.slot, v))
          traceWith tracer (LeiosNodeEvent Generate (EventVote v))
  let LeiosNodeConfig{..} = cfg
  leiosBlockGenerator $ LeiosGeneratorConfig{submit = mapM_ submitOne, ..}

mkBuffersView :: forall m. MonadSTM m => LeiosNodeConfig -> LeiosNodeState m -> BuffersView m
mkBuffersView cfg st = BuffersView{..}
 where
  newRBData = do
    -- This gets called pretty rarely, so doesn't seem worth caching,
    -- though it's getting more expensive as we go.
    chain <- PraosNode.preferredChain st.praosState
    let ebsInChain =
          Set.fromList $
            [ eb | rb <- Chain.chainToList chain, (eb, _) <- rb.blockBody.endorseBlocks
            ]
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
          guard (not $ Set.member eb.id ebsInChain)
          guard (cfg.leios.votesForCertificate <= totalVotes votes)
          return $! (eb.id,) $! mkCertificate cfg.leios votes

    -- TODO: cache index of EBs ordered by .slot descending?
    let freshestCertifiedEB = listToMaybe . mapMaybe tryCertify . sortOn (Down . (.slot)) $ bufferEB
    return $
      NewRankingBlockData
        { freshestCertifiedEB
        , txsPayload = cfg.leios.sizes.rankingBlockLegacyPraosPayloadAvgSize
        }
  newIBData = do
    ledgerState <- readTVar st.ledgerStateVar
    referenceRankingBlock <-
      Chain.headHash . Chain.dropUntil (flip Map.member ledgerState . blockHash)
        <$> PraosNode.preferredChain st.praosState
    let txsPayload = cfg.leios.sizes.inputBlockBodyAvgSize
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
            ( maybe False (<= slotTime cfg.slotConfig slot)
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
mkSchedule cfg = do
  -- For each pipeline, we want to deploy all our votes in a single
  -- message to cut down on traffic, so we pick one slot out of each
  -- active voting range (they are assumed not to overlap).
  votingSlots <- newTVarIO $ pickFromRanges rng1 $ votingRanges cfg.leios
  mkScheduler rng2 (rates votingSlots)
 where
  (rng1, rng2) = split cfg.rng
  calcWins rate = Just $ \sample ->
    if sample <= coerce (nodeRate cfg.stake rate) then 1 else 0
  voteRate = votingRatePerPipeline cfg.leios cfg.stake
  pureRates =
    [ (SomeRole Generate.Propose, inputBlockRate cfg.leios cfg.stake)
    , (SomeRole Generate.Endorse, endorseBlockRate cfg.leios cfg.stake)
    , (SomeRole Generate.Base, const $ calcWins (NetworkRate cfg.leios.praos.blockFrequencyPerSlot))
    ]
  rates votingSlots slot = do
    vote <- atomically $ do
      vs <- readTVar votingSlots
      case vs of
        (sl : sls)
          | sl == slot -> do
              writeTVar votingSlots sls
              pure (Just voteRate)
        _ -> pure Nothing
    pure $ (SomeRole Generate.Vote, vote) : map (fmap ($ slot)) pureRates
  pickFromRanges :: StdGen -> [(SlotNo, SlotNo)] -> [SlotNo]
  pickFromRanges rng0 rs = snd $ mapAccumL f rng0 rs
   where
    f rng r = coerce $ swap $ uniformR (coerce r :: (Word64, Word64)) rng
