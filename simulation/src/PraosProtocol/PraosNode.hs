{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}

module PraosProtocol.PraosNode where

import Chan (Chan)
import Control.Concurrent.Class.MonadSTM
import Control.Monad.Class.MonadAsync
import Data.Foldable (sequenceA_)
import Data.Map (Map)
import qualified Data.Map as Map
import PraosProtocol.BlockFetch (BlockFetchControllerState, BlockFetchMessage, BlockFetchProducerState (..), PeerId, blockFetchController, initBlockFetchConsumerStateForPeerId, newBlockFetchControllerState, runBlockFetchConsumer, runBlockFetchProducer)
import qualified PraosProtocol.BlockFetch as BlockFetch
import PraosProtocol.ChainSync (ChainConsumerState (..), ChainSyncMessage, runChainConsumer, runChainProducer)
import PraosProtocol.Common (Block, Chain, FollowerId, asReadOnly, genesisPoint, initFollower)
import qualified PraosProtocol.Common.Chain as Chain (Chain (..))

data Praos f = Praos
  { protocolChainSync :: f ChainSyncMessage
  , protocolBlockFetch :: f BlockFetchMessage
  }

data PraosNodeState m = PraosNodeState
  { blockFetchControllerState :: BlockFetchControllerState m
  , chainSyncConsumerStates :: Map PeerId (ChainConsumerState m)
  }

-- Peer requires ChainSyncConsumer and BlockFetchConsumer
addPeer ::
  MonadSTM m =>
  PraosNodeState m ->
  m (PraosNodeState m, PeerId)
addPeer st = do
  chainVar <- newTVarIO Chain.Genesis
  (blockFetchControllerState, peerId) <- BlockFetch.addPeer (asReadOnly chainVar) st.blockFetchControllerState
  let chainSyncConsumerStates = Map.insert peerId (ChainConsumerState chainVar) st.chainSyncConsumerStates
  return (PraosNodeState{..}, peerId)

runPeer ::
  (MonadAsync m, MonadSTM m) =>
  PraosNodeState m ->
  PeerId ->
  Praos (Chan m) ->
  Concurrently m ()
runPeer st peerId chan = do
  let chainConsumerState = st.chainSyncConsumerStates Map.! peerId
  let blockFetchConsumerState = initBlockFetchConsumerStateForPeerId peerId st.blockFetchControllerState
  sequenceA_
    [ Concurrently $ runChainConsumer (protocolChainSync chan) chainConsumerState
    , Concurrently $ runBlockFetchConsumer (protocolBlockFetch chan) blockFetchConsumerState
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
  (MonadAsync m, MonadSTM m) =>
  Chain Block ->
  [Praos (Chan m)] ->
  [Praos (Chan m)] ->
  m ()
runPraosNode chain followers peers = do
  st0 <- PraosNodeState <$> newBlockFetchControllerState chain <*> pure Map.empty
  (st1, followerIds) <- repeatM addFollower (length followers) st0
  (st2, peerIds) <- repeatM addPeer (length peers) st1
  let controllerThread = Concurrently $ blockFetchController st2.blockFetchControllerState
  let followerThreads = zipWith (runFollower st2) followerIds followers
  let peerThreads = zipWith (runPeer st2) peerIds peers
  runConcurrently $ sequenceA_ (controllerThread : followerThreads <> peerThreads)
