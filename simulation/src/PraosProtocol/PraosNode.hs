{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module PraosProtocol.PraosNode (
  module PraosProtocol.PraosNode,
  PraosNodeEvent (..),
)
where

import ChanMux
import Control.Concurrent.Class.MonadSTM
import Control.Monad.Class.MonadAsync
import Control.Tracer
import Data.ByteString (ByteString)
import Data.Coerce (coerce)
import Data.Either (fromLeft, fromRight)
import Data.Map (Map)
import qualified Data.Map as Map
import PraosProtocol.BlockFetch (BlockFetchControllerState, BlockFetchMessage, BlockFetchProducerState (..), PeerId, blockFetchController, initBlockFetchConsumerStateForPeerId, newBlockFetchControllerState, runBlockFetchConsumer, runBlockFetchProducer)
import qualified PraosProtocol.BlockFetch as BlockFetch
import PraosProtocol.BlockGeneration
import PraosProtocol.ChainSync (ChainConsumerState (..), ChainSyncMessage, runChainConsumer, runChainProducer)
import PraosProtocol.Common
import qualified PraosProtocol.Common.Chain as Chain (Chain (..))

data Praos body f = Praos
  { protocolChainSync :: f ChainSyncMessage
  , protocolBlockFetch :: f (BlockFetchMessage body)
  }

newtype PraosMessage body = PraosMessage (Either ChainSyncMessage (BlockFetchMessage body))
  deriving (Show)

instance MessageSize body => MessageSize (PraosMessage body) where
  messageSizeBytes (PraosMessage d) = either messageSizeBytes messageSizeBytes d

instance MuxBundle (Praos body) where
  type MuxMsg (Praos body) = PraosMessage body
  toFromMuxMsgBundle =
    coerce $
      Praos
        (ToFromMuxMsg Left $ fromLeft $ error "MuxBundle Praos: fromLeft")
        (ToFromMuxMsg Right $ fromRight $ error "MuxBundle Praos: fromRight")
  traverseMuxBundle f (Praos x y) = Praos <$> f x <*> f y

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
  PraosNodeState body m ->
  m (PraosNodeState body m, PeerId)
addPeer st = do
  chainVar <- newTVarIO Chain.Genesis
  (blockFetchControllerState, peerId) <- BlockFetch.addPeer (asReadOnly chainVar) st.blockFetchControllerState
  let chainSyncConsumerStates = Map.insert peerId (ChainConsumerState chainVar) st.chainSyncConsumerStates
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
  [ Concurrently $ runChainConsumer cfg (protocolChainSync chan) chainConsumerState
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
  concurrentlyMany . map runConcurrently =<< setupPraosThreads tracer cfg st0 followers peers
 where
  -- Nested children threads are slow with IOSim, this impl forks them all as direct children.
  concurrentlyMany :: MonadAsync m => [m ()] -> m ()
  concurrentlyMany xs = mapM_ wait =<< mapM async xs

setupPraosThreads ::
  (MonadAsync m, MonadSTM m, MonadDelay m) =>
  Tracer m (PraosNodeEvent BlockBody) ->
  PraosConfig BlockBody ->
  PraosNodeState BlockBody m ->
  [Praos BlockBody (Chan m)] ->
  [Praos BlockBody (Chan m)] ->
  m [Concurrently m ()]
setupPraosThreads tracer cfg st0 followers peers = do
  (ts, f) <- BlockFetch.setupValidatorThreads cfg st0.blockFetchControllerState 1 -- TODO: parameter
  (map Concurrently ts ++) <$> setupPraosThreads' tracer cfg f st0 followers peers

setupPraosThreads' ::
  (IsBody body, Show body, MonadAsync m, MonadSTM m, MonadDelay m) =>
  Tracer m (PraosNodeEvent body) ->
  PraosConfig body ->
  (Block body -> m () -> m ()) ->
  PraosNodeState body m ->
  [Praos body (Chan m)] ->
  [Praos body (Chan m)] ->
  m [Concurrently m ()]
setupPraosThreads' tracer cfg submitFetchedBlock st0 followers peers = do
  (st1, followerIds) <- repeatM addFollower (length followers) st0
  (st2, peerIds) <- repeatM addPeer (length peers) st1
  let controllerThread = Concurrently $ blockFetchController tracer st2.blockFetchControllerState
  let followerThreads = zipWith (runFollower st2) followerIds followers
  let peerThreads = zipWith (runPeer tracer cfg submitFetchedBlock st2) peerIds peers
  return (controllerThread : concat followerThreads <> concat peerThreads)

data PraosNodeConfig = PraosNodeConfig
  { praosConfig :: PraosConfig BlockBody
  , blockGeneration :: PacketGenerationPattern
  , chain :: Chain (Block BlockBody)
  , blockMarker :: ByteString
  -- ^ bytes to include in block bodies.
  }

newPraosNodeState :: MonadSTM m => Chain (Block body) -> m (PraosNodeState body m)
newPraosNodeState chain = PraosNodeState <$> newBlockFetchControllerState chain <*> pure Map.empty

praosNode ::
  (MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m (PraosNodeEvent BlockBody) ->
  PraosNodeConfig ->
  [Praos BlockBody (Chan m)] ->
  [Praos BlockBody (Chan m)] ->
  m ([m ()])
praosNode tracer cfg followers peers = do
  st0 <- PraosNodeState <$> newBlockFetchControllerState cfg.chain <*> pure Map.empty
  praosThreads <- setupPraosThreads tracer cfg.praosConfig st0 followers peers
  nextBlock <- mkNextBlock cfg.blockGeneration cfg.blockMarker
  let generationThread =
        blockGenerator
          tracer
          cfg.praosConfig
          st0.blockFetchControllerState.cpsVar
          (BlockFetch.addProducedBlock st0.blockFetchControllerState)
          nextBlock
  return $ map runConcurrently $ Concurrently generationThread : praosThreads
