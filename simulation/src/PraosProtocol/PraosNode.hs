{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module PraosProtocol.PraosNode (
  module PraosProtocol.PraosNode,
  PraosNodeEvent (..),
)
where

import Chan
import Control.Exception (assert)
import Control.Monad.Class.MonadAsync (Concurrently (..), MonadAsync (..))
import Control.Monad.Class.MonadFork
import Control.Monad.Class.MonadThrow
import Control.Tracer (Tracer, contramap)
import Data.ByteString (ByteString)
import Data.Coerce (coerce)
import Data.Either (fromLeft, fromRight)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import PraosProtocol.BlockFetch (BlockFetchControllerState, BlockFetchMessage, BlockFetchProducerState (..), PeerId, blockFetchController, initBlockFetchConsumerStateForPeerId, newBlockFetchControllerState, runBlockFetchConsumer, runBlockFetchProducer)
import qualified PraosProtocol.BlockFetch as BlockFetch
import PraosProtocol.BlockGeneration
import PraosProtocol.ChainSync (ChainConsumerState (..), ChainSyncMessage, chainSyncMessageLabel, runChainConsumer, runChainProducer)
import PraosProtocol.Common
import qualified PraosProtocol.Common.Chain as Chain (Chain (..))
import STMCompat
import SimTypes
import System.Random (StdGen)
import TaskMultiQueue

data Praos body f = Praos
  { protocolChainSync :: f ChainSyncMessage
  , protocolBlockFetch :: f (BlockFetchMessage body)
  }

newtype PraosMessage body = PraosMessage (Either ChainSyncMessage (BlockFetchMessage body))
  deriving (Show)

praosMessageLabel :: PraosMessage body -> String
praosMessageLabel (PraosMessage d) =
  either
    (protocolMessage chainSyncMessageLabel)
    (protocolMessage BlockFetch.blockFetchMessageLabel)
    d

instance MessageSize body => MessageSize (PraosMessage body) where
  messageSizeBytes (PraosMessage d) = either messageSizeBytes messageSizeBytes d

instance MessageSize body => ConnectionBundle (Praos body) where
  type BundleMsg (Praos body) = PraosMessage body
  type BundleConstraint (Praos body) = MessageSize
  toFromBundleMsgBundle =
    coerce $
      Praos
        (ToFromBundleMsg Left $ fromLeft $ error "ConnectionBundle Praos: fromLeft")
        (ToFromBundleMsg Right $ fromRight $ error "ConnectionBundle Praos: fromRight")
  traverseConnectionBundle f (Praos x y) = Praos <$> f x <*> f y

data PraosNodeState body m = PraosNodeState
  { blockFetchControllerState :: BlockFetchControllerState body m
  , chainSyncConsumerStates :: Map PeerId (ChainConsumerState m)
  }

preferredChain :: MonadSTM m => PraosNodeState body m -> STM m (Chain (Block body))
preferredChain st = do
  cps <- readTVar st.blockFetchControllerState.cpsVar
  return $ chainState cps

-- Peer requires ChainSyncConsumer and BlockFetchConsumer
addPeer ::
  (IsBody body, MonadSTM m, MonadDelay m) =>
  (BlockHeader -> m ()) ->
  PraosNodeState body m ->
  m (PraosNodeState body m, PeerId)
addPeer f st = do
  chainVar <- newTVarIO Chain.Genesis
  (blockFetchControllerState, peerId) <- BlockFetch.addPeer (asReadOnly chainVar) st.blockFetchControllerState
  let chainSyncConsumerStates = Map.insert peerId (ChainConsumerState chainVar f) st.chainSyncConsumerStates
  return (PraosNodeState{..}, peerId)

runPeer ::
  (IsBody body, Show body, MonadAsync m, MonadSTM m, MonadDelay m) =>
  Tracer m (PraosNodeEvent body) ->
  PraosConfig body ->
  (Block body -> m () -> m ()) ->
  PraosNodeState body m ->
  PeerId ->
  Praos body (Chan m) ->
  [Concurrently m ()]
runPeer tracer cfg f st peerId chan = do
  let chainConsumerState = st.chainSyncConsumerStates Map.! peerId
  let blockFetchConsumerState = initBlockFetchConsumerStateForPeerId tracer peerId st.blockFetchControllerState f
  [ Concurrently $ runChainConsumer tracer cfg (protocolChainSync chan) chainConsumerState
    , Concurrently $ runBlockFetchConsumer tracer cfg (protocolBlockFetch chan) blockFetchConsumerState
    ]

-- Follower requires ChainSyncProducer and BlockFetchProducer
addFollower ::
  (IsBody body, MonadSTM m) =>
  PraosNodeState body m ->
  m (PraosNodeState body m, FollowerId)
addFollower st = atomically $ do
  cps <- readTVar st.blockFetchControllerState.cpsVar
  let (cps', followerId) = initFollower genesisPoint cps
  writeTVar st.blockFetchControllerState.cpsVar cps'
  return (st, followerId)

runFollower ::
  (IsBody body, MonadAsync m, MonadSTM m) =>
  PraosNodeState body m ->
  FollowerId ->
  Praos body (Chan m) ->
  [Concurrently m ()]
runFollower st followerId chan = do
  let chainProducerStateVar = st.blockFetchControllerState.cpsVar
  let blockFetchProducerState = BlockFetchProducerState $ asReadOnly st.blockFetchControllerState.blocksVar
  [ Concurrently $ runChainProducer (protocolChainSync chan) followerId chainProducerStateVar
    , Concurrently $ runBlockFetchProducer (protocolBlockFetch chan) blockFetchProducerState
    ]

repeatM :: Monad m => (st -> m (st, a)) -> Int -> st -> m (st, [a])
repeatM gen = go []
 where
  go acc n st
    | n <= 0 = return (st, reverse acc)
    | otherwise = gen st >>= \(st', x) -> go (x : acc) (n - 1) st'

runPraosNode ::
  (MonadAsync m, MonadSTM m, MonadDelay m) =>
  Tracer m (PraosNodeEvent BlockBody) ->
  PraosConfig BlockBody ->
  Chain (Block BlockBody) ->
  [Praos BlockBody (Chan m)] ->
  [Praos BlockBody (Chan m)] ->
  m ()
runPraosNode tracer cfg chain followers peers = do
  st0 <- PraosNodeState <$> newBlockFetchControllerState chain <*> pure Map.empty
  taskQueue <- atomically $ newTaskMultiQueue @() 100
  let queue = writeTMQueue taskQueue ()
  concurrentlyMany . map runConcurrently =<< setupPraosThreads tracer cfg queue st0 followers peers
 where
  -- Nested children threads are slow with IOSim, this impl forks them all as direct children.
  concurrentlyMany :: MonadAsync m => [m ()] -> m ()
  concurrentlyMany xs = mapM_ wait =<< mapM async xs

setupPraosThreads ::
  (MonadAsync m, MonadSTM m, MonadDelay m) =>
  Tracer m (PraosNodeEvent BlockBody) ->
  PraosConfig BlockBody ->
  ((CPUTask, m ()) -> STM m ()) ->
  PraosNodeState BlockBody m ->
  [Praos BlockBody (Chan m)] ->
  [Praos BlockBody (Chan m)] ->
  m [Concurrently m ()]
setupPraosThreads tracer cfg queue st0 followers peers = do
  (ts, f) <- BlockFetch.setupValidatorThreads cfg st0.blockFetchControllerState queue
  let valHeader h = assert (blockInvariant h) $ do
        let !delay = cfg.headerValidationDelay h
        curry
          (queueAndWait (atomically . queue))
          (CPUTask delay $ T.pack $ "ValidateHeader " ++ show (coerce @_ @Int $ blockHash h))
          (return ())
  (map Concurrently ts ++) <$> setupPraosThreads' tracer cfg valHeader f st0 followers peers

setupPraosThreads' ::
  (IsBody body, Show body, MonadAsync m, MonadSTM m, MonadDelay m) =>
  Tracer m (PraosNodeEvent body) ->
  PraosConfig body ->
  (BlockHeader -> m ()) ->
  (Block body -> m () -> m ()) ->
  PraosNodeState body m ->
  [Praos body (Chan m)] ->
  [Praos body (Chan m)] ->
  m [Concurrently m ()]
setupPraosThreads' tracer cfg valHeader submitFetchedBlock st0 followers peers = do
  (st1, followerIds) <- repeatM addFollower (length followers) st0
  (st2, peerIds) <- repeatM (addPeer valHeader) (length peers) st1
  let controllerThread = Concurrently $ blockFetchController tracer cfg st2.blockFetchControllerState
  let followerThreads = zipWith (runFollower st2) followerIds followers
  let peerThreads = zipWith (runPeer tracer cfg submitFetchedBlock st2) peerIds peers
  return (controllerThread : concat followerThreads <> concat peerThreads)

data PraosNodeConfig = PraosNodeConfig
  { praosConfig :: PraosConfig BlockBody
  , slotConfig :: SlotConfig
  , chain :: Chain (Block BlockBody)
  , blockMarker :: ByteString
  -- ^ bytes to include in block bodies.
  , rng :: StdGen
  , processingCores :: NumCores
  }

newPraosNodeState :: MonadSTM m => Chain (Block body) -> m (PraosNodeState body m)
newPraosNodeState chain = PraosNodeState <$> newBlockFetchControllerState chain <*> pure Map.empty

praosNode ::
  (MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m, MonadCatch m, MonadFork m, MonadMonotonicTimeNSec m) =>
  Tracer m (PraosNodeEvent BlockBody) ->
  PraosNodeConfig ->
  [Praos BlockBody (Chan m)] ->
  [Praos BlockBody (Chan m)] ->
  m [m ()]
praosNode tracer cfg followers peers = do
  st0 <- PraosNodeState <$> newBlockFetchControllerState cfg.chain <*> pure Map.empty
  taskQueue <- atomically $ newTaskMultiQueue @() (defaultQueueBound cfg.processingCores)
  let queue = writeTMQueue taskQueue ()
  praosThreads <- setupPraosThreads tracer cfg.praosConfig queue st0 followers peers
  let cpuTasksProcessors = processCPUTasks cfg.processingCores (contramap PraosNodeEventCPU tracer) taskQueue
  let generationThread =
        praosBlockGenerator
          cfg.rng
          tracer
          cfg.praosConfig
          cfg.slotConfig
          cfg.blockMarker
          st0.blockFetchControllerState.cpsVar
          (BlockFetch.addProducedBlock st0.blockFetchControllerState)
          (queueAndWait (atomically . queue))
  return $ cpuTasksProcessors : generationThread : map runConcurrently praosThreads

queueAndWait ::
  MonadSTM m =>
  ((a, m ()) -> m ()) ->
  (a, m ()) ->
  m ()
queueAndWait queue (d, m) = do
  sem <- newEmptyTMVarIO
  curry queue d $ do
    m
    atomically $ putTMVar sem ()
  atomically $ takeTMVar sem
