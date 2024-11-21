{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoFieldSelectors #-}

module LeiosProtocol.Short.Generate where

import Control.Monad.State

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (..),
 )
import Control.Exception (assert)
import Data.Kind
import Data.Traversable (forM)
import LeiosProtocol.Common
import LeiosProtocol.Short hiding (Stage (..))
import PraosProtocol.Common (fixupBlock, mkPartialBlock)

data BuffersView m = BuffersView
  { newRBData :: STM m NewRankingBlockData
  , newIBData :: STM m NewInputBlockData
  , ibs :: STM m InputBlocksSnapshot
  , ebs :: STM m EndorseBlocksSnapshot
  }

data Role :: Type -> Type where
  Base :: Role RankingBlock
  Propose :: [SubSlotNo] -> Role [InputBlock]
  Endorse :: Role EndorseBlock
  Vote :: Role [VoteMsg]

data SomeRole :: Type where
  SomeRole :: Role a -> SomeRole

data SomeAction :: Type where
  SomeAction :: Role a -> a -> SomeAction

waitNextSlot :: (Monad m, MonadTime m, MonadDelay m) => LeiosConfig -> m SlotNo
waitNextSlot cfg = do
  now <- getCurrentTime
  let slot =
        assert (cfg.praos.slotConfig.duration == 1) $
          toEnum (ceiling $ now `diffUTCTime` cfg.praos.slotConfig.start)
  let tgt = slotTime cfg.praos.slotConfig slot
  threadDelayNDT (tgt `diffUTCTime` now)
  return slot

data BlockGeneratorConfig m = BlockGeneratorConfig
  { leios :: LeiosConfig
  , nodeId :: NodeId
  , buffers :: BuffersView m
  , schedule :: SlotNo -> m [SomeRole]
  , submit :: [SomeAction] -> m ()
  }

blockGenerator ::
  forall m.
  (MonadSTM m, MonadDelay m, MonadTime m) =>
  BlockGeneratorConfig m ->
  m ()
blockGenerator BlockGeneratorConfig{..} = go 0
 where
  go !blkId = do
    slot <- waitNextSlot leios
    roles <- schedule slot
    (actions, blkId') <- runStateT (mapM (execute slot) roles) blkId
    submit actions
    go blkId'
  execute slot (SomeRole r) = SomeAction r <$> execute' slot r
  execute' :: SlotNo -> Role a -> StateT Int m a
  execute' slot Base = do
    rbData <- lift $ atomically $ buffers.newRBData
    let body = uncurry (mkRankingBlockBody leios) rbData.freshestCertifiedEB rbData.txsPayload
    -- TODO: maybe submit should do the fixupBlock.
    return $! fixupBlock @_ @RankingBlock rbData.headAnchor (mkPartialBlock slot body)
  execute' slot (Propose subs) = do
    forM subs $ \sub -> do
      i <- nextBlkId InputBlockId
      ibData <- lift $ atomically $ buffers.newIBData
      let header = mkInputBlockHeader leios i slot sub nodeId ibData.referenceRankingBlock
      return $! mkInputBlock leios header ibData.txsPayload
  execute' slot Endorse = do
    i <- nextBlkId EndorseBlockId
    ibs <- lift $ atomically $ buffers.ibs
    return $! mkEndorseBlock leios i slot nodeId $ inputBlocksToEndorse leios slot ibs
  execute' slot Vote = do
    votingFor <- lift $ atomically $ do
      ibs <- buffers.ibs
      ebs <- buffers.ebs
      pure $ endorseBlocksToVoteFor leios slot ibs ebs
    forM votingFor $ \eb -> do
      i <- nextBlkId VoteId
      return $! mkVoteMsg leios i slot nodeId eb
  nextBlkId :: (NodeId -> Int -> a) -> StateT Int m a
  nextBlkId f = do
    i <- get
    put $! i + 1
    return $ f nodeId i
