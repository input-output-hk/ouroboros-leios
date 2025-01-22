{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  Propose :: Role InputBlock
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
waitNextSlot :: (Monad m, MonadTime m, MonadDelay m) => SlotConfig -> SlotNo -> m SlotNo
waitNextSlot slotConfig targetSlot = do
  now <- getCurrentTime
  let targetSlotTime = slotTime slotConfig targetSlot
  let slot
        | now <= targetSlotTime = targetSlot
        | otherwise = assert (nextSlotIndex >= 0) $ toEnum nextSlotIndex
       where
        nextSlotIndex =
          assert (slotConfig.duration == 1) $
            ceiling $
              now `diffUTCTime` slotConfig.start
  let tgt = slotTime slotConfig slot
  threadDelayNDT (tgt `diffUTCTime` now)
  return slot

data BlockGeneratorConfig m = BlockGeneratorConfig
  { leios :: LeiosConfig
  , slotConfig :: SlotConfig
  , nodeId :: NodeId
  , buffers :: BuffersView m
  , schedule :: SlotNo -> m [(SomeRole, Word64)]
  , submit :: [(DiffTime, SomeAction)] -> m ()
  }

blockGenerator ::
  forall m.
  (MonadSTM m, MonadDelay m, MonadTime m) =>
  BlockGeneratorConfig m ->
  m ()
blockGenerator BlockGeneratorConfig{..} = go (0, 0)
 where
  go (!blkId, !tgtSlot) = do
    slot <- waitNextSlot slotConfig tgtSlot
    roles <- schedule slot
    (actions, blkId') <- runStateT (concat <$> mapM (execute slot) roles) blkId
    submit actions
    go (blkId', slot + 1)
  execute slot (SomeRole r, wins) = assert (wins >= 1) $ (map . second) (SomeAction r) <$> execute' slot r wins
  execute' :: SlotNo -> Role a -> Word64 -> StateT Int m [(DiffTime, a)]
  execute' slot Base _wins = do
    rbData <- lift $ atomically buffers.newRBData
    let meb = rbData.freshestCertifiedEB
    let body = mkRankingBlockBody leios nodeId meb rbData.txsPayload
    let !rb = mkPartialBlock slot body
    let !task = leios.praos.blockGenerationDelay rb
    return [(task, rb)]
  execute' slot Propose wins = do
    ibData <- lift $ atomically buffers.newIBData
    forM [toEnum $ fromIntegral sub | sub <- [0 .. wins - 1]] $ \sub -> do
      i <- nextBlkId InputBlockId
      let header = mkInputBlockHeader leios i slot sub nodeId ibData.referenceRankingBlock
      let !ib = mkInputBlock leios header ibData.txsPayload
      let !task = leios.delays.inputBlockGeneration ib
      return (task, ib)
  execute' slot Endorse _wins = do
    i <- nextBlkId EndorseBlockId
    ibs <- lift $ atomically buffers.ibs
    let !eb = mkEndorseBlock leios i slot nodeId $ inputBlocksToEndorse leios slot ibs
    let !task = leios.delays.endorseBlockGeneration eb
    return [(task, eb)]
  execute' slot Vote votes = do
    votingFor <- lift $ atomically $ do
      ibs <- buffers.ibs
      ebs <- buffers.ebs
      pure $ endorseBlocksToVoteFor leios slot ibs ebs
    i <- nextBlkId VoteId
    let voteMsg = mkVoteMsg leios i slot nodeId votes votingFor
    let !task = leios.delays.voteMsgGeneration voteMsg
    return [(task, voteMsg)]
  nextBlkId :: (NodeId -> Int -> a) -> StateT Int m a
  nextBlkId f = do
    i <- get
    put $! i + 1
    return $ f nodeId i
