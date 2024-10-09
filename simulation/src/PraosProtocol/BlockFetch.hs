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
    atomically
  ),
 )
import Control.Monad (guard)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map (lookup)
import Network.TypedProtocol
import Network.TypedProtocol.Peer.Server as TS

import PraosProtocol.Types

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

data BlockFetchServerState m = BlockFetchProducerState
  { blockHeadersVar :: ReadOnly (TVar m (Map BlockId BlockHeader)) -- Shared, Read-Only.
  , blockBodiesVar :: ReadOnly (TVar m (Map BlockId BlockBody)) -- Shared, Read-Only.
  }

resolveRange :: MonadSTM m => BlockFetchServerState m -> Point -> Point -> STM m (Maybe [BlockBody])
resolveRange st start end = do
  headers <- readReadOnlyTVar st.blockHeadersVar
  bodies <- readReadOnlyTVar st.blockBodiesVar
  let go acc p
        | start == p = Just []
        | otherwise = do
            hdr <- Map.lookup p.pointBlockId headers
            guard $ blockHeaderSlot hdr == p.pointSlot
            p' <- blockHeaderParent hdr
            b <- Map.lookup p.pointBlockId bodies
            go (b : acc) p'

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
