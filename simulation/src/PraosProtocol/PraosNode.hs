{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module PraosProtocol.PraosNode where

import ChanMux
import Control.Concurrent.Class.MonadSTM
import Control.Monad.Class.MonadAsync
import Control.Tracer
import Data.ByteString (ByteString)
import Data.Coerce (coerce)
import Data.Either (fromLeft, fromRight)
import Data.Foldable (sequenceA_)
import Data.Map (Map)
import qualified Data.Map as Map
import PraosProtocol.BlockFetch (BlockFetchControllerState, BlockFetchMessage, BlockFetchProducerState (..), PeerId, blockFetchController, initBlockFetchConsumerStateForPeerId, newBlockFetchControllerState, runBlockFetchConsumer, runBlockFetchProducer)
import qualified PraosProtocol.BlockFetch as BlockFetch
import PraosProtocol.BlockGeneration
import PraosProtocol.ChainSync (ChainConsumerState (..), ChainSyncMessage, runChainConsumer, runChainProducer)
import PraosProtocol.Common
import qualified PraosProtocol.Common.Chain as Chain (Chain (..))

data Praos f = Praos
  { protocolChainSync :: f ChainSyncMessage
  , protocolBlockFetch :: f BlockFetchMessage
  }

newtype PraosMessage = PraosMessage (Either ChainSyncMessage BlockFetchMessage)
  deriving (Show)

instance MessageSize PraosMessage where
  messageSizeBytes (PraosMessage d) = either messageSizeBytes messageSizeBytes d

instance MuxBundle Praos where
  type MuxMsg Praos = PraosMessage
  toFromMuxMsgBundle =
    coerce $
      Praos
        (ToFromMuxMsg Left $ fromLeft $ error "MuxBundle Praos: fromLeft")
        (ToFromMuxMsg Right $ fromRight $ error "MuxBundle Praos: fromRight")
  traverseMuxBundle f (Praos x y) = Praos <$> f x <*> f y

data PraosNodeState m = PraosNodeState
  { blockFetchControllerState :: BlockFetchControllerState m
  , chainSyncConsumerStates :: Map PeerId (ChainConsumerState m)
  }

-- Peer requires ChainSyncConsumer and BlockFetchConsumer
addPeer ::
  (MonadSTM m, MonadDelay m) =>
  PraosNodeState m ->
  m (PraosNodeState m, PeerId)
addPeer st = do
  chainVar <- newTVarIO Chain.Genesis
  (blockFetchControllerState, peerId) <- BlockFetch.addPeer (asReadOnly chainVar) st.blockFetchControllerState
  let chainSyncConsumerStates = Map.insert peerId (ChainConsumerState chainVar) st.chainSyncConsumerStates
  return (PraosNodeState{..}, peerId)

runPeer ::
  (MonadAsync m, MonadSTM m, MonadDelay m) =>
  Tracer m PraosNodeEvent ->
  PraosConfig ->
  PraosNodeState m ->
  PeerId ->
  Praos (Chan m) ->
  Concurrently m ()
runPeer tracer cfg st peerId chan = do
  let chainConsumerState = st.chainSyncConsumerStates Map.! peerId
  let blockFetchConsumerState = initBlockFetchConsumerStateForPeerId tracer peerId st.blockFetchControllerState
  sequenceA_
    [ Concurrently $ runChainConsumer (protocolChainSync chan) chainConsumerState
    , Concurrently $ runBlockFetchConsumer tracer cfg (protocolBlockFetch chan) blockFetchConsumerState
    ]

-- Follower requires ChainSyncProducer and BlockFetchProducer
addFollower ::
  MonadSTM m =>
  PraosNodeState m ->
  m (PraosNodeState m, FollowerId)
addFollower st = atomically $ do
  cps <- readTVar st.blockFetchControllerState.cpsVar
  let (cps', followerId) = initFollower genesisPoint cps
  writeTVar st.blockFetchControllerState.cpsVar cps'
  return (st, followerId)

runFollower ::
  (MonadAsync m, MonadSTM m) =>
  PraosNodeState m ->
  FollowerId ->
  Praos (Chan m) ->
  Concurrently m ()
runFollower st followerId chan = do
  let chainProducerStateVar = st.blockFetchControllerState.cpsVar
  let blockFetchProducerState = BlockFetchProducerState $ asReadOnly st.blockFetchControllerState.blocksVar
  sequenceA_
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
  Tracer m PraosNodeEvent ->
  PraosConfig ->
  Chain Block ->
  [Praos (Chan m)] ->
  [Praos (Chan m)] ->
  m ()
runPraosNode tracer cfg chain followers peers = do
  st0 <- PraosNodeState <$> newBlockFetchControllerState chain <*> pure Map.empty
  runConcurrently =<< setupPraosThreads tracer cfg st0 followers peers

setupPraosThreads ::
  (MonadAsync m, MonadSTM m, MonadDelay m) =>
  Tracer m PraosNodeEvent ->
  PraosConfig ->
  PraosNodeState m ->
  [Praos (Chan m)] ->
  [Praos (Chan m)] ->
  m (Concurrently m ())
setupPraosThreads tracer cfg st0 followers peers = do
  (st1, followerIds) <- repeatM addFollower (length followers) st0
  (st2, peerIds) <- repeatM addPeer (length peers) st1
  let controllerThread = Concurrently $ blockFetchController tracer st2.blockFetchControllerState
  let followerThreads = zipWith (runFollower st2) followerIds followers
  let peerThreads = zipWith (runPeer tracer cfg st2) peerIds peers
  return $ sequenceA_ (controllerThread : followerThreads <> peerThreads)

data PraosNodeConfig = PraosNodeConfig
  { praosConfig :: PraosConfig
  , blockGeneration :: PacketGenerationPattern
  , chain :: Chain Block
  , blockMarker :: ByteString
  -- ^ bytes to include in block bodies.
  }

praosNode ::
  (MonadAsync m, MonadSTM m, MonadTime m, MonadDelay m) =>
  Tracer m PraosNodeEvent ->
  PraosNodeConfig ->
  [Praos (Chan m)] ->
  [Praos (Chan m)] ->
  m ()
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
  runConcurrently $ sequenceA_ [Concurrently generationThread, praosThreads]
