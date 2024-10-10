{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module PraosProtocol.BlockFetch where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TVar,
    atomically,
    readTVar,
    retry,
    writeTVar
  ),
 )
import Control.Monad (guard)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (lookup)
import Network.TypedProtocol
import qualified Network.TypedProtocol.Peer.Client as TC
import qualified Network.TypedProtocol.Peer.Server as TS

import Ouroboros.Network.AnchoredFragment (AnchoredFragment)
import qualified Ouroboros.Network.AnchoredFragment as AF
import qualified Ouroboros.Network.Block as OAPI
import Ouroboros.Network.Mock.ConcreteBlock

import PraosProtocol.Types (ReadOnly, readReadOnlyTVar)

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

data BlockFetchServerState m = BlockFetchProducerState
  { blockHeadersVar :: ReadOnly (TVar m (Map BlockId BlockHeader)) -- Shared, Read-Only.
  , blockBodiesVar :: ReadOnly (TVar m (Map BlockId BlockBody)) -- Shared, Read-Only.
  }

resolveRange :: MonadSTM m => BlockFetchServerState m -> Point -> Point -> STM m (Maybe [BlockBody])
resolveRange st start end = do
  headers <- readReadOnlyTVar st.blockHeadersVar
  bodies <- readReadOnlyTVar st.blockBodiesVar
  let
    blockPrevPoint hdr = case OAPI.blockPrevHash hdr of
      OAPI.GenesisHash -> pure OAPI.GenesisPoint
      OAPI.BlockHash hsh -> OAPI.castPoint . OAPI.blockPoint <$> Map.lookup hsh headers
    go acc p | start == p = Just acc
    go _acc OAPI.GenesisPoint = Nothing
    go acc p@(OAPI.BlockPoint pSlot pHash)
      | OAPI.pointSlot start > OAPI.pointSlot p = Nothing
      | otherwise = do
          hdr <- Map.lookup pHash headers
          guard $ OAPI.blockSlot hdr == pSlot
          bdy <- Map.lookup pHash bodies
          go (bdy : acc) =<< blockPrevPoint hdr

  return $ reverse <$> go [] end

blockFetchServer ::
  forall m.
  MonadSTM m =>
  BlockFetchServerState m ->
  TS.Server BlockFetchState NonPipelined StIdle m ()
blockFetchServer st = idle
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
  streaming (blk : blks) = TS.Yield (MsgBlock blk) (streaming blks)

--------------------------------
--- BlockFetch Client
--------------------------------

newtype FetchRequest
  = FetchRequest {fetchRequestFragments :: [AnchoredFragment BlockHeader]}
  deriving (Show)

fragmentRange :: AnchoredFragment BlockHeader -> (Point, Point)
fragmentRange = undefined

data BlockFetchClientState m = BlockFetchClientState
  { fetchRequestsVar :: TVar m FetchRequest -- Shared, Read-Write.
  , addFetchedBlock :: Block -> m () -- this should include validation.
  -- or should it be the whole fragment at once?
  }

blockFetchClient ::
  forall m.
  MonadSTM m =>
  BlockFetchClientState m ->
  TC.Client BlockFetchState NonPipelined StIdle m ()
blockFetchClient BlockFetchClientState{..} = idle
 where
  -- \| does not support preemption of in-flight requests.
  fetchRequest :: STM m (AnchoredFragment BlockHeader)
  fetchRequest = do
    FetchRequest rs <- readTVar fetchRequestsVar
    case rs of
      [] -> retry
      (r : rs') -> do
        writeTVar fetchRequestsVar (FetchRequest rs')
        return r
  idle :: TC.Client BlockFetchState NonPipelined StIdle m ()
  idle = TC.Effect $ atomically $ do
    fr <- fetchRequest
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
        -- TODO: check hash?
        addFetchedBlock (Block header block)
        return (streaming range headers')
      (MsgBatchDone, _ : _) -> TC.Effect $ error "TooFewBlocks" -- TODO
      (MsgBlock _, []) -> TC.Effect $ error "TooManyBlocks" -- TODO
