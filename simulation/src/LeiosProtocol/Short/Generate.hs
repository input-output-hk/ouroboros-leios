{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoFieldSelectors #-}

module LeiosProtocol.Short.Generate where

import Control.Exception (assert)
import Control.Monad (forM)
import Control.Monad.State (
  MonadState (get, put),
  MonadTrans (lift),
  StateT (runStateT),
  gets,
  runState,
 )
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import LeiosProtocol.Common
import LeiosProtocol.Short hiding (Stage (..))
import STMCompat
import System.Random (StdGen, uniformR)

--------------------------------------------------------------------------------

{-# ANN module ("HLint: ignore Use <$>" :: String) #-}

--------------------------------------------------------------------------------

data BuffersView m = BuffersView
  { newRBData :: STM m NewRankingBlockData
  , newIBData :: STM m NewInputBlockData
  , ibs :: STM m InputBlocksSnapshot
  , ebs :: STM m EndorseBlocksSnapshot
  }

data Role :: Type -> Type where
  Base :: Role RankingBlock
  Propose :: Role [InputBlock]
  Endorse :: Role EndorseBlock
  Vote :: Role VoteMsg

data SomeRole :: Type where
  SomeRole :: Role a -> SomeRole

data SomeAction :: Type where
  SomeAction :: Role a -> a -> SomeAction

mkScheduler :: MonadSTM m => StdGen -> (SlotNo -> [(SomeRole, [NodeRate])]) -> m (SlotNo -> m [(SomeRole, Word64)])
mkScheduler rng0 rates = do
  let sampleRate (NodeRate lambda) = do
        (sample, rng') <- gets $ uniformR (0, 1)
        put $! rng'
        -- TODO: check poisson dist. math.
        let prob = lambda * exp (-lambda)
        pure $ sample <= prob
      sampleRates (role, rs) = do
        wins <- fromIntegral . length . filter id <$> mapM sampleRate rs
        return [(role, wins) | wins >= 1]
  rngVar <- newTVarIO rng0
  let sched slot = atomically $ do
        rng <- readTVar rngVar
        let (acts, rng1) = flip runState rng . fmap concat . mapM sampleRates $ rates slot
        writeTVar rngVar rng1
        return acts
  return sched

-- | @waitNextSlot cfg targetSlot@ waits until the beginning of
-- @targetSlot@ if that's now or in the future, otherwise the closest slot.
waitNextSlot :: (Monad m, MonadTime m, MonadDelay m) => LeiosConfig -> SlotNo -> m SlotNo
waitNextSlot cfg targetSlot = do
  now <- getCurrentTime
  let targetSlotTime = slotTime cfg.praos.slotConfig targetSlot
  let slot
        | now <= targetSlotTime = targetSlot
        | otherwise = assert (nextSlotIndex >= 0) $ toEnum nextSlotIndex
       where
        nextSlotIndex =
          assert (cfg.praos.slotConfig.duration == 1) $
            ceiling $
              now `diffUTCTime` cfg.praos.slotConfig.start
  let tgt = slotTime cfg.praos.slotConfig slot
  threadDelayNDT (tgt `diffUTCTime` now)
  return slot

data BlockGeneratorConfig m = BlockGeneratorConfig
  { leios :: LeiosConfig
  , nodeId :: NodeId
  , buffers :: BuffersView m
  , schedule :: SlotNo -> m [(SomeRole, Word64)]
  , submit :: [(Maybe CPUTask, SomeAction)] -> m ()
  }

blockGenerator ::
  forall m.
  (MonadSTM m, MonadDelay m, MonadTime m) =>
  BlockGeneratorConfig m ->
  m ()
blockGenerator BlockGeneratorConfig{..} = go (0, 0)
 where
  go (!blkId, !tgtSlot) = do
    slot <- waitNextSlot leios tgtSlot
    roles <- schedule slot
    (actions, blkId') <- runStateT (mapM (execute slot) roles) blkId
    submit actions
    go (blkId', slot + 1)
  execute slot (SomeRole r, wins) = assert (wins >= 1) $ second (SomeAction r) <$> execute' slot r wins
  execute' :: SlotNo -> Role a -> Word64 -> StateT Int m (Maybe CPUTask, a)
  execute' slot Base _wins = do
    rbData <- lift $ atomically buffers.newRBData
    let meb = rbData.freshestCertifiedEB
    let !task = CPUTask $ maybe 0 (leios.delays.certificateCreation . snd) meb
    let body = mkRankingBlockBody leios nodeId meb rbData.txsPayload
    let !rb = mkPartialBlock slot body
    return (Just task, rb)
  execute' slot Propose wins =
    (Nothing,) <$> do
      ibData <- lift $ atomically buffers.newIBData
      forM [toEnum $ fromIntegral sub | sub <- [0 .. wins - 1]] $ \sub -> do
        i <- nextBlkId InputBlockId
        let header = mkInputBlockHeader leios i slot sub nodeId ibData.referenceRankingBlock
        return $! mkInputBlock leios header ibData.txsPayload
  execute' slot Endorse _wins =
    (Nothing,) <$> do
      i <- nextBlkId EndorseBlockId
      ibs <- lift $ atomically buffers.ibs
      return $! mkEndorseBlock leios i slot nodeId $ inputBlocksToEndorse leios slot ibs
  execute' slot Vote votes =
    (Nothing,) <$> do
      votingFor <- lift $ atomically $ do
        ibs <- buffers.ibs
        ebs <- buffers.ebs
        pure $ endorseBlocksToVoteFor leios slot ibs ebs
      i <- nextBlkId VoteId
      return $! mkVoteMsg leios i slot nodeId votes votingFor
  nextBlkId :: (NodeId -> Int -> a) -> StateT Int m a
  nextBlkId f = do
    i <- get
    put $! i + 1
    return $ f nodeId i
