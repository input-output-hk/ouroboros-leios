{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module LeiosProtocol.Short.Node where

import ChanMux
import Control.Concurrent.Class.MonadMVar
import Control.Concurrent.Class.MonadSTM
import Control.Monad (forever, guard, join)
import Control.Monad.Class.MonadAsync
import Control.Monad.Class.MonadFork
import Control.Tracer
import Data.Bifunctor (Bifunctor (first), second)
import Data.Coerce (coerce)
import Data.Foldable (forM_)
import Data.List (sort, sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
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
import PraosProtocol.BlockFetch (addProducedBlock)
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
    PraosMsg {fromPraosMsg :: BearerMsg PraosMessage}

data Leios f = Leios
  { protocolIB :: f RelayIBMessage
  , protocolEB :: f RelayEBMessage
  , protocolVote :: f RelayVoteMessage
  , protocolPraos :: f (BearerMsg PraosMessage)
  -- ^ use newChanMux on (Chan m PraosMessage) to get PraosNode.Praos bundle.
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
      , protocolPraos = ToFromMuxMsg PraosMsg fromPraosMsg
      }
  traverseMuxBundle f (Leios a b c d) = Leios <$> f a <*> f b <*> f c <*> f d

type RelayIBState = RelayConsumerSharedState InputBlockId InputBlockHeader InputBlockBody
type RelayEBState = RelayConsumerSharedState EndorseBlockId EndorseBlockId EndorseBlock
type RelayVoteState = RelayConsumerSharedState VoteId VoteId VoteMsg

data ValidationRequest m
  = ValidateRB RankingBlock (STM m ())
  | ValidateIBS [(InputBlockHeader, InputBlockBody)] ([(InputBlockHeader, InputBlockBody)] -> STM m ())
  | ValidateEBS [EndorseBlock] ([EndorseBlock] -> STM m ())
  | ValidateVotes [VoteMsg] ([VoteMsg] -> STM m ())

data LeiosNodeState m = LeiosNodeState
  { praosState :: PraosNode.PraosNodeState RankingBlockBody m
  , relayIBState :: RelayIBState m
  , relayEBState :: RelayEBState m
  , relayVoteState :: RelayVoteState m
  , ibDeliveryTimesVar :: TVar m (Map InputBlockId UTCTime)
  , validationQueue :: TBQueue m (ValidationRequest m)
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

data LeiosNodeEvent = PraosNodeEvent (PraosNode.PraosNodeEvent RankingBlockBody)
  -- TODO: other events
  deriving (Show)

setupRelay ::
  (Ord id, MonadAsync m, MonadSTM m, MonadDelay m, MonadTime m) =>
  RelayConsumerConfig id header body m ->
  [Chan m (RelayMessage id header body)] ->
  [Chan m (RelayMessage id header body)] ->
  m (RelayConsumerSharedState id header body m, [m ()])
setupRelay cfg followers peers = do
  relayBufferVar <- newTVarIO RB.empty
  inFlightVar <- newTVarIO Set.empty

  let consumerSST = RelayConsumerSharedState{relayBufferVar, inFlightVar}
  let producerSST = RelayProducerSharedState{relayBufferVar = asReadOnly consumerSST.relayBufferVar}
  let consumers = map (runRelayConsumer cfg consumerSST) peers
  let producers = map (runRelayProducer cfg.relay producerSST) followers
  return $ (consumerSST, consumers ++ producers)

leiosNode ::
  forall m.
  (MonadMVar m, MonadFork m, MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m LeiosNodeEvent ->
  LeiosNodeConfig ->
  [Leios (Chan m)] ->
  [Leios (Chan m)] ->
  m ([m ()])
leiosNode tracer cfg followers peers = do
  praosState <- PraosNode.newPraosNodeState cfg.baseChain
  -- TODO: refactor block validation, so we can hook it to `validationQueue`.
  praosThreads <-
    join $
      PraosNode.setupPraosThreads (contramap PraosNodeEvent tracer) cfg.leios.praos praosState
        <$> (mapM (newMuxChan . protocolPraos) followers)
        <*> (mapM (newMuxChan . protocolPraos) peers)
  validationQueue <- newTBQueueIO cfg.processingQueueBound
  ibDeliveryTimesVar <- newTVarIO Map.empty
  let relayIBConfig =
        RelayConsumerConfig
          { relay = RelayConfig{maxWindowSize = 100}
          , headerId = (.id)
          , -- TODO: add prioritization policy to LeiosConfig
            prioritize = sortOn (Down . (.slot)) . Map.elems
          , submitPolicy = SubmitAll
          , maxHeadersToRequest = 100
          , maxBodiesToRequest = 1
          , submitBlocks = \xs deliveryTime completion -> atomically $ do
              writeTBQueue validationQueue $! ValidateIBS xs $ \ys -> do
                completion ys
                modifyTVar'
                  ibDeliveryTimesVar
                  (Map.union $ Map.fromList [(h.id, deliveryTime) | (h, _) <- ys])
          }
  let relayEBConfig =
        RelayConsumerConfig
          { relay = RelayConfig{maxWindowSize = 100}
          , headerId = id
          , -- TODO: add prioritization policy to LeiosConfig?
            prioritize = sort . Map.elems
          , submitPolicy = SubmitAll
          , maxHeadersToRequest = 100
          , maxBodiesToRequest = 1 -- should we chunk bodies here?
          , submitBlocks = \xs _ completion -> atomically $ do
              writeTBQueue validationQueue $!
                ValidateEBS (map snd xs) $
                  completion . map (\eb -> (eb.id, eb))
          }
  let relayVoteConfig =
        RelayConsumerConfig
          { relay = RelayConfig{maxWindowSize = 100}
          , headerId = id
          , -- TODO: add prioritization policy to LeiosConfig?
            prioritize = sort . Map.elems
          , submitPolicy = SubmitAll
          , maxHeadersToRequest = 100
          , maxBodiesToRequest = 1 -- should we chunk bodies here?
          , submitBlocks = \xs _ completion -> atomically $ do
              writeTBQueue validationQueue $!
                ValidateVotes (map snd xs) $
                  completion . map (\v -> (v.id, v))
          }
  (relayIBState, ibThreads) <- setupRelay relayIBConfig (map protocolIB followers) (map protocolIB peers)
  (relayEBState, ebThreads) <- setupRelay relayEBConfig (map protocolEB followers) (map protocolEB peers)
  (relayVoteState, voteThreads) <- setupRelay relayVoteConfig (map protocolVote followers) (map protocolVote peers)
  let leiosState = LeiosNodeState{..}
  let genThreads = [generate leiosState]
  let processingThreads = [processing leiosState]
  let pruningThreads = [] -- TODO: need EB/IBs to be around long enough to validate RBs
  return $
    concat
      [ genThreads
      , processingThreads
      , pruningThreads
      , ibThreads
      , ebThreads
      , voteThreads
      , coerce praosThreads
      ]
 where
  generate :: LeiosNodeState m -> m ()
  generate st = do
    schedule <- mkSchedule cfg
    let buffers = mkBuffersView cfg st
    -- TODO: tracing events
    let
      submitOne :: SomeAction -> m ()
      submitOne x = atomically $ case x of
        SomeAction Generate.Base rb ->
          -- TODO: certificate construction delay?
          addProducedBlock st.praosState.blockFetchControllerState rb
        SomeAction (Generate.Propose _) ib ->
          modifyTVar' st.relayIBState.relayBufferVar (RB.snoc ib.header.id (ib.header, ib.body))
        SomeAction Generate.Endorse eb ->
          modifyTVar' st.relayEBState.relayBufferVar (RB.snoc eb.id (eb.id, eb))
        SomeAction Generate.Vote vs -> forM_ vs $ \v ->
          modifyTVar' st.relayVoteState.relayBufferVar (RB.snoc v.id (v.id, v))
    let LeiosNodeConfig{..} = cfg
    blockGenerator $ BlockGeneratorConfig{submit = mapM_ submitOne, ..}

  -- TODO: validation delays and tracing events.
  processing :: LeiosNodeState m -> m ()
  processing leiosState = forever $ do
    req <- atomically $ readTBQueue leiosState.validationQueue
    case req of
      ValidateRB _rb completion -> do
        -- NOTE: in actual impl. have to wait for previous RB, but
        -- not for its ledger state unless rb.payload > 0.
        atomically $ completion
      ValidateIBS ibs completion -> atomically $ do
        -- NOTE: in actual impl. have to wait for ledger state of referenced RBs.
        completion ibs
      ValidateEBS ebs completion -> do
        -- TODO: only delay for crypto checks, contents used for voting.
        atomically $ completion ebs
      ValidateVotes vs completion -> do
        -- TODO: only delay for crypto checks
        atomically $ completion vs

mkBuffersView :: forall m. MonadSTM m => LeiosNodeConfig -> LeiosNodeState m -> BuffersView m
mkBuffersView cfg st = BuffersView{..}
 where
  newRBData = do
    headAnchor' <- headAnchor <$> PraosNode.preferredChain st.praosState
    bufferEB <- map snd . RB.values <$> readTVar st.relayEBState.relayBufferVar
    bufferVotes <- map snd . RB.values <$> readTVar st.relayVoteState.relayBufferVar
    -- TODO: cache?
    let votesForEB = Map.fromListWith Set.union [(v.endorseBlock, Set.singleton v.id) | v <- bufferVotes]
    let tryCertify eb = do
          votes <- Map.lookup eb.id votesForEB
          guard (cfg.leios.votesForCertificate <= Set.size votes)
          return (eb.id, mkCertificate cfg.leios votes)
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

mkSchedule :: MonadSTM m => LeiosNodeConfig -> m (SlotNo -> m [SomeRole])
mkSchedule cfg = mkScheduler cfg.rng rates
 where
  rates slot =
    (map . second) (nodeRate cfg.stake) . concat $
      [ (map . first) (SomeRole . Generate.Propose) $ inputBlockRate cfg.leios slot
      , map (SomeRole Generate.Endorse,) . maybe [] (: []) $ endorseBlockRate cfg.leios slot
      , map (SomeRole Generate.Vote,) . maybe [] (: []) $ votingRate cfg.leios slot
      , [(SomeRole Generate.Base, NetworkRate cfg.rankingBlockFrequencyPerSlot)]
      ]
