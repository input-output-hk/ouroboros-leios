{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module LeiosProtocol.Short.Node where

import ChanMux
import Control.Category ((>>>))
import Control.Concurrent.Class.MonadMVar
import Control.Concurrent.Class.MonadSTM
import Control.Exception (assert)
import Control.Monad (forever, guard, when)
import Control.Monad.Class.MonadAsync
import Control.Monad.Class.MonadFork
import Control.Tracer
import Data.Bifunctor
import Data.Coerce (coerce)
import Data.Foldable (forM_)
import Data.List (sort, sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import LeiosProtocol.Common
import LeiosProtocol.Relay
import qualified LeiosProtocol.RelayBuffer as RB
import LeiosProtocol.Short
import LeiosProtocol.Short.Generate
import qualified LeiosProtocol.Short.Generate as Generate
import ModelTCP
import Numeric.Natural (Natural)
import Ouroboros.Network.Mock.Chain (headHash)
import PraosProtocol.BlockFetch
import PraosProtocol.Common
import PraosProtocol.Common.Chain (headAnchor)
import qualified PraosProtocol.PraosNode as PraosNode
import System.Random

type RelayIBMessage = RelayMessage InputBlockId InputBlockHeader InputBlockBody
type RelayEBMessage = RelayMessage EndorseBlockId EndorseBlockId EndorseBlock
type RelayVoteMessage = RelayMessage VoteId VoteId VoteMsg
type PraosMessage = PraosNode.PraosMessage RankingBlockBody

data LeiosMessage
  = RelayIB {fromRelayIB :: RelayIBMessage}
  | RelayEB {fromRelayEB :: RelayEBMessage}
  | RelayVote {fromRelayVote :: RelayVoteMessage}
  | -- | `BearerMsg` here is a bit ugly, but allows us to not have to split up PraosMessage in the Leios bundle.
    PraosMsg {fromPraosMsg :: PraosMessage}
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

type RelayIBState = RelayConsumerSharedState InputBlockId InputBlockHeader InputBlockBody
type RelayEBState = RelayConsumerSharedState EndorseBlockId EndorseBlockId EndorseBlock
type RelayVoteState = RelayConsumerSharedState VoteId VoteId VoteMsg

data ValidationRequest m
  = ValidateRB !RankingBlock !(m ())
  | ValidateIBS ![(InputBlockHeader, InputBlockBody)] !UTCTime !([(InputBlockHeader, InputBlockBody)] -> STM m ())
  | ValidateEBS ![EndorseBlock] !([EndorseBlock] -> STM m ())
  | ValidateVotes ![VoteMsg] !([VoteMsg] -> STM m ())

data LedgerState = LedgerState

data LeiosNodeState m = LeiosNodeState
  { praosState :: PraosNode.PraosNodeState RankingBlockBody m
  , relayIBState :: RelayIBState m
  , relayEBState :: RelayEBState m
  , relayVoteState :: RelayVoteState m
  , ibDeliveryTimesVar :: TVar m (Map InputBlockId UTCTime)
  , validationQueue :: TBQueue m (ValidationRequest m)
  , waitingForRBVar :: TVar m (Map (HeaderHash RankingBlock) [(DiffTime, m ())])
  -- ^ waiting for RB block itself to be validated.
  , waitingForLedgerStateVar :: TVar m (Map (HeaderHash RankingBlock) [(DiffTime, m ())])
  -- ^ waiting for ledger state of RB block to be validated.
  , ledgerStateVar :: TVar m (Map (HeaderHash RankingBlock) LedgerState)
  , ibsNeededForEBVar :: TVar m (Map EndorseBlockId (Set InputBlockId))
  }

data LeiosNodeConfig = LeiosNodeConfig
  { leios :: LeiosConfig
  , rankingBlockFrequencyPerSlot :: Double
  , nodeId :: NodeId
  , stake :: StakeFraction
  , rng :: StdGen
  -- ^ for block generation
  , baseChain :: Chain RankingBlock
  , rankingBlockPayload :: Bytes
  -- ^ overall size of txs to include in RBs
  , inputBlockPayload :: Bytes
  -- ^ overall size of txs to include in IBs
  , processingQueueBound :: Natural
  }

data LeiosEventBlock
  = EventIB InputBlock
  | EventEB EndorseBlock
  | EventVote VoteMsg
  deriving (Show)

data LeiosNodeEvent
  = PraosNodeEvent (PraosNode.PraosNodeEvent RankingBlockBody)
  | LeiosNodeEventCPU CPUTask
  | LeiosNodeEventGenerate LeiosEventBlock
  | LeiosNodeEventReceived LeiosEventBlock
  | LeiosNodeEventEnterState LeiosEventBlock
  deriving (Show)

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
  SubmitBlocks m InputBlockHeader InputBlockBody ->
  RelayConsumerConfig InputBlockId InputBlockHeader InputBlockBody m
relayIBConfig tracer cfg submitBlocks =
  RelayConsumerConfig
    { relay = RelayConfig{maxWindowSize = 100}
    , headerId = (.id)
    , headerValidationDelay = cfg.leios.delays.inputBlockHeaderValidation
    , threadDelayParallel = threadDelayParallel tracer
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
relayEBConfig tracer _cfg submitBlocks =
  RelayConsumerConfig
    { relay = RelayConfig{maxWindowSize = 100}
    , headerId = id
    , headerValidationDelay = const 0
    , threadDelayParallel = threadDelayParallel tracer
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
relayVoteConfig tracer _cfg submitBlocks =
  RelayConsumerConfig
    { relay = RelayConfig{maxWindowSize = 100}
    , headerId = id
    , headerValidationDelay = const 0
    , threadDelayParallel = threadDelayParallel tracer
    , -- TODO: add prioritization policy to LeiosConfig?
      prioritize = sort . Map.elems
    , submitPolicy = SubmitAll
    , maxHeadersToRequest = 100
    , maxBodiesToRequest = 1 -- should we chunk bodies here?
    , submitBlocks
    }

threadDelayParallel :: MonadDelay m => Tracer m LeiosNodeEvent -> [DiffTime] -> m ()
threadDelayParallel _tracer [] = return ()
threadDelayParallel tracer ds = do
  forM_ ds (traceWith tracer . LeiosNodeEventCPU . CPUTask)
  let d = maximum ds
  when (d >= 0) $ threadDelaySI d

newLeiosNodeState ::
  forall m.
  (MonadMVar m, MonadSTM m) =>
  LeiosNodeConfig ->
  m (LeiosNodeState m)
newLeiosNodeState cfg = do
  praosState <- PraosNode.newPraosNodeState cfg.baseChain
  validationQueue <- newTBQueueIO cfg.processingQueueBound
  relayIBState <- newRelayState
  relayEBState <- newRelayState
  relayVoteState <- newRelayState
  ibDeliveryTimesVar <- newTVarIO Map.empty
  ibsNeededForEBVar <- newTVarIO Map.empty
  ledgerStateVar <- newTVarIO Map.empty
  waitingForRBVar <- newTVarIO Map.empty
  waitingForLedgerStateVar <- newTVarIO Map.empty

  return $ LeiosNodeState{..}

leiosNode ::
  forall m.
  (MonadMVar m, MonadFork m, MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  [Leios (Chan m)] ->
  [Leios (Chan m)] ->
  m ([m ()])
leiosNode tracer cfg followers peers = do
  leiosState@LeiosNodeState{..} <- newLeiosNodeState cfg
  let
    traceReceived :: [a] -> (a -> LeiosEventBlock) -> m ()
    traceReceived xs f = mapM_ (traceWith tracer . LeiosNodeEventReceived . f) xs

  -- tracing for RB already covered in blockFetchConsumer.
  let submitRB rb completion = atomically $ writeTBQueue validationQueue $! ValidateRB rb completion
  let submitIB xs deliveryTime completion = do
        traceReceived xs $ EventIB . uncurry InputBlock
        atomically $ writeTBQueue validationQueue $! ValidateIBS xs deliveryTime $ completion

  let submitVote (map snd -> xs) _ completion = do
        traceReceived xs EventVote
        atomically $ writeTBQueue validationQueue $! ValidateVotes xs $ completion . map (\v -> (v.id, v))

  let submitEB (map snd -> xs) _ completion = do
        traceReceived xs EventEB
        atomically $ writeTBQueue validationQueue $! ValidateEBS xs $ completion . map (\eb -> (eb.id, eb))

  praosThreads <-
    PraosNode.setupPraosThreads'
      (contramap PraosNodeEvent tracer)
      cfg.leios.praos
      submitRB
      praosState
      (map protocolPraos followers)
      (map protocolPraos peers)

  ibThreads <-
    setupRelay
      (relayIBConfig tracer cfg submitIB)
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
        processWaiting
          (contramap LeiosNodeEventCPU tracer)
          Nothing -- unbounded parallelism
          praosState.blockFetchControllerState.blocksVar
          waitingForRBVar

  let processWaitingForLedgerState =
        processWaiting
          (contramap LeiosNodeEventCPU tracer)
          Nothing -- unbounded parallelism
          ledgerStateVar
          waitingForLedgerStateVar

  let processingThreads =
        [ validationDispatcher tracer cfg leiosState
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
      [ coerce praosThreads
      , ibThreads
      , ebThreads
      , voteThreads
      , processingThreads
      , blockGenerationThreads
      , pruningThreads
      , computeLedgerStateThreads
      ]

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

-- TODO: tracing events
validationDispatcher ::
  forall m.
  (MonadMVar m, MonadFork m, MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  LeiosNodeState m ->
  m ()
validationDispatcher tracer cfg leiosState = forever $ do
  -- NOTE: IOSim deschedules the thread after an `atomically`, we
  -- might get more parallelism by reading the whole buffer at once,
  -- collect all resulting delays and do a single
  -- `threadDelayParallel` call.
  req <- atomically $ readTBQueue leiosState.validationQueue
  case req of
    ValidateRB rb completion -> do
      let !delay = cfg.leios.praos.blockValidationDelay rb
      case blockPrevHash rb of
        GenesisHash -> do
          traceWith tracer . LeiosNodeEventCPU . CPUTask $ delay
          threadDelaySI delay
          completion
        BlockHash prev -> atomically $ do
          let var =
                assert (rb.blockBody.payload >= 0) $
                  if rb.blockBody.payload == 0
                    then leiosState.waitingForRBVar
                    -- TODO: assumes payload can be validated without content of EB, check with spec.
                    else leiosState.waitingForLedgerStateVar
          modifyTVar' var $ Map.insertWith (++) prev [(delay, completion)]
    ValidateIBS ibs deliveryTime completion -> do
      -- NOTE: IBs with an RB reference have to wait for ledger state of that RB.
      let valIB x =
            let
              !delay = cfg.leios.delays.inputBlockValidation (uncurry InputBlock x)
              task = atomically $ do
                completion [x]

                -- NOTE: voting relies on delivery times for IBs
                modifyTVar'
                  leiosState.ibDeliveryTimesVar
                  (Map.insertWith min (fst x).id deliveryTime)

                -- TODO: likely needs optimization
                modifyTVar' leiosState.ibsNeededForEBVar (Map.map (Set.delete (fst x).id))
             in
              (delay, task >> traceEnterState [uncurry InputBlock x] EventIB)
      let waitingLedgerState =
            Map.fromListWith
              (++)
              [ (rbHash, [valIB ib])
              | ib <- ibs
              , BlockHash rbHash <- [(fst ib).rankingBlock]
              ]

      atomically $ modifyTVar' leiosState.waitingForLedgerStateVar (`Map.union` waitingLedgerState)

      let (delays, ms) = unzip [valIB ib | ib@(h, _) <- ibs, GenesisHash <- [h.rankingBlock]]
      threadDelayParallel tracer delays
      sequence_ ms
    ValidateEBS ebs completion -> do
      -- NOTE: block references are only inspected during voting.
      threadDelayParallel tracer $ map cfg.leios.delays.endorseBlockValidation ebs
      atomically $ do
        completion ebs
        ibs <- RB.keySet <$> readTVar leiosState.relayIBState.relayBufferVar
        let ibsNeeded = Map.fromList $ map (\eb -> (eb.id, Set.fromList eb.inputBlocks Set.\\ ibs)) ebs
        modifyTVar' leiosState.ibsNeededForEBVar $ (`Map.union` ibsNeeded)
      traceEnterState ebs EventEB
    ValidateVotes vs completion -> do
      threadDelayParallel tracer $ map cfg.leios.delays.voteMsgValidation vs
      atomically $ completion vs
      traceEnterState vs EventVote
 where
  traceEnterState :: [a] -> (a -> LeiosEventBlock) -> m ()
  traceEnterState xs f = forM_ xs $ traceWith tracer . LeiosNodeEventEnterState . f
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
    submitOne :: SomeAction -> m ()
    submitOne x = case x of
      SomeAction Generate.Base rb -> do
        atomically $ addProducedBlock st.praosState.blockFetchControllerState rb
        traceWith tracer (PraosNodeEvent (PraosNodeEventGenerate rb))
      SomeAction Generate.Propose ibs -> forM_ ibs $ \ib -> do
        atomically $ modifyTVar' st.relayIBState.relayBufferVar (RB.snoc ib.header.id (ib.header, ib.body))
        traceWith tracer (LeiosNodeEventGenerate (EventIB ib))
      SomeAction Generate.Endorse eb -> do
        atomically $ modifyTVar' st.relayEBState.relayBufferVar (RB.snoc eb.id (eb.id, eb))
        traceWith tracer (LeiosNodeEventGenerate (EventEB eb))
      SomeAction Generate.Vote v -> do
        atomically $ modifyTVar' st.relayVoteState.relayBufferVar (RB.snoc v.id (v.id, v))
        traceWith tracer (LeiosNodeEventGenerate (EventVote v))
  let LeiosNodeConfig{..} = cfg
  blockGenerator $ BlockGeneratorConfig{submit = mapM_ submitOne, ..}

mkBuffersView :: forall m. MonadSTM m => LeiosNodeConfig -> LeiosNodeState m -> BuffersView m
mkBuffersView cfg st = BuffersView{..}
 where
  newRBData = do
    headAnchor' <- headAnchor <$> PraosNode.preferredChain st.praosState
    bufferEB <- map snd . RB.values <$> readTVar st.relayEBState.relayBufferVar
    bufferVotes <- map snd . RB.values <$> readTVar st.relayVoteState.relayBufferVar
    -- TODO: cache?
    let votesForEB = Map.fromListWith Map.union [(eb, Map.singleton v.id v.votes) | v <- bufferVotes, eb <- v.endorseBlocks]
    -- TODO: certificate construction delay?
    let totalVotes = fromIntegral . sum . Map.elems
    let tryCertify eb = do
          votes <- Map.lookup eb.id votesForEB
          guard (cfg.leios.votesForCertificate <= totalVotes votes)
          return (eb.id, mkCertificate cfg.leios (Map.keysSet votes))
    -- TODO: cache index of EBs ordered by .slot descending?
    let freshestCertifiedEB = listToMaybe . mapMaybe tryCertify . sortOn (Down . (.slot)) $ bufferEB
    return $
      NewRankingBlockData
        { freshestCertifiedEB
        , txsPayload = cfg.rankingBlockPayload
        , headAnchor = headAnchor'
        }
  newIBData = do
    referenceRankingBlock <- headHash <$> PraosNode.preferredChain st.praosState
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
    (map . second . map) (nodeRate cfg.stake) $
      [ (SomeRole Generate.Propose, inputBlockRate cfg.leios slot)
      , (SomeRole Generate.Endorse, endorseBlockRate cfg.leios slot)
      , (SomeRole Generate.Vote, votingRate cfg.leios slot)
      , (SomeRole Generate.Base, [NetworkRate cfg.rankingBlockFrequencyPerSlot])
      ]
