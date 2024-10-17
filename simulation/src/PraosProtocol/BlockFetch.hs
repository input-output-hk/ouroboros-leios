{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoFieldSelectors #-}

module PraosProtocol.BlockFetch where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TVar,
    atomically,
    modifyTVar,
    readTVar,
    retry,
    writeTVar
  ),
 )
import Control.Monad (forM, forever, guard, (<=<))
import Data.Bifunctor (second)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import Network.TypedProtocol (
  Agency (ClientAgency, NobodyAgency, ServerAgency),
  IsPipelined (NonPipelined),
  Protocol (..),
  StateTokenI (..),
 )
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS
import Ouroboros.Network.AnchoredFragment (AnchoredFragment)
import qualified Ouroboros.Network.AnchoredFragment as AF
import qualified Ouroboros.Network.Block as OAPI

import PraosProtocol.Types (Block (..), BlockBody, BlockHeader, Blocks, Chain, ChainProducerState (..), ReadOnly, blockPrevPoint, headPoint, headerPoint, intersectChains, readReadOnlyTVar, selectChain, toAnchoredFragment)

type BlockId = OAPI.HeaderHash Block
type Point = OAPI.Point Block

data BlockFetchState
  = StIdle
  | StBusy
  | StStreaming
  | StDone

data SingBlockFetchState (st :: BlockFetchState) where
  SingStIdle :: SingBlockFetchState StIdle
  SingStBusy :: SingBlockFetchState StBusy
  SingStStreaming :: SingBlockFetchState StStreaming
  SingStDone :: SingBlockFetchState StDone

instance Protocol BlockFetchState where
  data Message BlockFetchState from to where
    MsgRequestRange :: Point -> Point -> Message BlockFetchState StIdle StBusy
    MsgNoBlocks :: Message BlockFetchState StBusy StIdle
    MsgStartBatch :: Message BlockFetchState StBusy StStreaming
    MsgBlock :: BlockBody -> Message BlockFetchState StStreaming StStreaming
    MsgBatchDone :: Message BlockFetchState StStreaming StIdle
    MsgClientDone :: Message BlockFetchState StIdle StDone
  type StateAgency StIdle = ClientAgency
  type StateAgency StBusy = ServerAgency
  type StateAgency StStreaming = ServerAgency
  type StateAgency StDone = NobodyAgency
  type StateToken = SingBlockFetchState

instance StateTokenI StIdle where stateToken = SingStIdle
instance StateTokenI StBusy where stateToken = SingStBusy
instance StateTokenI StStreaming where stateToken = SingStStreaming
instance StateTokenI StDone where stateToken = SingStDone

--------------------------------
--- BlockFetch Server
--------------------------------

data BlockProducerState m = BlockProducerState
  { blocksVar :: ReadOnly (TVar m Blocks) -- Shared, Read-Only.
  }

resolveRange :: MonadSTM m => BlockProducerState m -> Point -> Point -> STM m (Maybe [BlockBody])
resolveRange st start end = do
  blocks <- readReadOnlyTVar st.blocksVar
  let resolveRangeAcc :: [BlockBody] -> Point -> Maybe [BlockBody]
      resolveRangeAcc acc p | start == p = Just acc
      resolveRangeAcc _acc OAPI.GenesisPoint = Nothing
      resolveRangeAcc acc p@(OAPI.BlockPoint pSlot pHash)
        | OAPI.pointSlot start > OAPI.pointSlot p = Nothing
        | otherwise = do
            Block{..} <- Map.lookup pHash blocks
            guard $ OAPI.blockSlot blockHeader == pSlot
            resolveRangeAcc (blockBody : acc) =<< blockPrevPoint blocks blockHeader
  return $ reverse <$> resolveRangeAcc [] end

blockProducer ::
  forall m.
  MonadSTM m =>
  BlockProducerState m ->
  TS.Server BlockFetchState NonPipelined StIdle m ()
blockProducer st = idle
 where
  idle :: TS.Server BlockFetchState NonPipelined StIdle m ()
  idle = TS.Await $ \case
    MsgRequestRange start end -> TS.Effect $ atomically $ do
      mblocks <- resolveRange st start end
      case mblocks of
        Nothing -> return $ TS.Yield MsgNoBlocks idle
        Just blocks -> return $ TS.Yield MsgStartBatch (streaming blocks)
    MsgClientDone -> TS.Done ()

  streaming :: [BlockBody] -> TS.Server BlockFetchState NonPipelined StStreaming m ()
  streaming [] = TS.Yield MsgBatchDone idle
  streaming (block : blocks) = TS.Yield (MsgBlock block) (streaming blocks)

--------------------------------
--- BlockFetch Client
--------------------------------

newtype BlockRequest
  = BlockRequest {blockRequestFragments :: [AnchoredFragment BlockHeader]}
  deriving (Show)
  deriving newtype (Semigroup) -- TODO: we could merge the fragments.

fragmentRange :: AnchoredFragment BlockHeader -> (Point, Point)
fragmentRange fr = (OAPI.castPoint $ AF.headPoint fr, OAPI.castPoint $ AF.lastPoint fr)

blockRequestPoints :: BlockRequest -> [Point]
blockRequestPoints (BlockRequest frs) = concatMap (map headerPoint . AF.toOldestFirst) $ frs

data BlockConsumerState m = BlockConsumerState
  { blockRequestVar :: TVar m BlockRequest -- Shared, Read-Write.
  , addFetchedBlock :: Block -> m () -- this should include validation.
  -- or should it be the whole fragment at once?
  }

blockConsumer ::
  forall m.
  MonadSTM m =>
  BlockConsumerState m ->
  TC.Client BlockFetchState NonPipelined StIdle m ()
blockConsumer BlockConsumerState{..} = idle
 where
  -- \| does not support preemption of in-flight requests.
  blockRequest :: STM m (AnchoredFragment BlockHeader)
  blockRequest = do
    BlockRequest rs <- readTVar blockRequestVar
    case rs of
      [] -> retry
      (r : rs') -> do
        writeTVar blockRequestVar (BlockRequest rs')
        return r

  idle :: TC.Client BlockFetchState NonPipelined StIdle m ()
  idle = TC.Effect $ atomically $ do
    fr <- blockRequest
    let range@(start, end) = fragmentRange fr
    return $ TC.Yield (MsgRequestRange start end) $ busy range fr

  busy :: (Point, Point) -> AnchoredFragment BlockHeader -> TC.Client BlockFetchState NonPipelined StBusy m ()
  busy range fr = TC.Await $ \case
    MsgNoBlocks -> idle -- TODO: adversarial? should signal to block fetch controller?
    MsgStartBatch -> streaming range $ AF.toOldestFirst fr

  streaming :: (Point, Point) -> [BlockHeader] -> TC.Client BlockFetchState NonPipelined StStreaming m ()
  streaming range headers = TC.Await $ \msg ->
    case (msg, headers) of
      (MsgBatchDone, []) -> idle -- TODO: signal someone?
      (MsgBlock block, header : headers') -> TC.Effect $ do
        addFetchedBlock (Block header block)
        return (streaming range headers')
      (MsgBatchDone, _ : _) -> TC.Effect $ error "TooFewBlocks" -- TODO
      (MsgBlock _, []) -> TC.Effect $ error "TooManyBlocks" -- TODO

--------------------------------------------
---- BlockFetch controller
--------------------------------------------

longestChainSelection ::
  forall block header m.
  ( OAPI.HasHeader block
  , OAPI.HasHeader header
  , OAPI.HeaderHash block ~ OAPI.HeaderHash header
  , MonadSTM m
  ) =>
  [(PeerId, ReadOnly (TVar m (Maybe (Chain header))))] ->
  ReadOnly (TVar m (ChainProducerState block)) ->
  (block -> header) ->
  STM m (Maybe (PeerId, AnchoredFragment header))
longestChainSelection candidateChainVars cpsVar getHeader = do
  candidateChains <- mapM (\(pId, v) -> fmap (pId,) <$> readReadOnlyTVar v) candidateChainVars
  cps <- readReadOnlyTVar cpsVar
  let
    chain = fmap getHeader cps.chainState
    -- using foldl' since @selectChain@ is left biased
    aux (mpId, c1) (pId, c2) =
      let c = selectChain c1 c2
       in if headPoint c == headPoint c1
            then (mpId, c1)
            else (Just pId, c2)
    (selectedPeer, chain') = List.foldl' aux (Nothing, chain) (catMaybes candidateChains)
  return $ do
    peerId <- selectedPeer
    let af = toAnchoredFragment chain'
    (peerId,) <$> case intersectChains chain chain' of
      Nothing -> pure af
      Just point -> snd <$> AF.splitAfterPoint af point

type PeerId = Int

-- | Note:
--    * a block is added to RequestVar and InFlightVar at the same time.
--    * the block is removed from blockRequestVar when the consumer starts fetching
--      the corresponding fragment.
--    * the block is removed from blocksInFlightVar when it reaches the
--      "ChainDB" i.e. blockBodiesVar, or the consumer encountered a
--      problem when fetching it. TODO!
data PeerStatus m = PeerStatus
  { blockRequestVar :: TVar m BlockRequest
  , blocksInFlightVar :: TVar m (Set Point)
  , peerChainVar :: ReadOnly (TVar m (Maybe (Chain BlockHeader)))
  }

data BlockControllerState m = BlockControllerState
  { blocksVar :: ReadOnly (TVar m Blocks) -- Shared, Read-Only.
  , peers :: Map PeerId (PeerStatus m)
  , cpsVar :: ReadOnly (TVar m (ChainProducerState Block))
  }

blockFetchController :: forall m. MonadSTM m => BlockControllerState m -> m ()
blockFetchController BlockControllerState{..} = forever (atomically makeRequests)
 where
  makeRequests :: STM m ()
  makeRequests = do
    let peerChainVars = (map (second (.peerChainVar)) $ Map.toList peers)
    (peerId, fr) <- maybe retry pure =<< longestChainSelection peerChainVars cpsVar blockHeader

    req <- filterInFlight <=< filterFetched $ fr
    addRequest peerId req

  filterFetched :: AnchoredFragment BlockHeader -> STM m BlockRequest
  filterFetched fr = do
    blocks <- readReadOnlyTVar blocksVar
    pure $ filterBR ((`Map.notMember` blocks) . OAPI.blockHash) (BlockRequest [fr])

  filterBR :: (BlockHeader -> Bool) -> BlockRequest -> BlockRequest
  filterBR p = BlockRequest . concatMap (AF.filter p) . (.blockRequestFragments)
  filterInFlight :: BlockRequest -> STM m BlockRequest
  filterInFlight br = do
    in_flights <- forM (Map.elems peers) $ \peer -> do
      readTVar peer.blocksInFlightVar
    pure $ List.foldl' (flip $ \s -> filterBR ((`Set.notMember` s) . headerPoint)) br in_flights
  addRequest :: PeerId -> BlockRequest -> STM m ()
  addRequest _pId (BlockRequest []) = retry
  addRequest pId br = do
    case Map.lookup pId peers of
      Nothing -> error "addRequest: no such peer"
      Just PeerStatus{..} -> do
        modifyTVar blocksInFlightVar (`Set.union` Set.fromList (blockRequestPoints br))
        modifyTVar blockRequestVar (<> br)
