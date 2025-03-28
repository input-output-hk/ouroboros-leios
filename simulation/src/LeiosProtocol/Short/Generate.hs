{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoFieldSelectors #-}

module LeiosProtocol.Short.Generate where

import Control.Exception (assert)
import Control.Monad (forM)
import Control.Monad.State (
  MonadState (get, put),
  MonadTrans (lift),
  StateT,
 )
import Data.Bifunctor (Bifunctor (..))
import Data.Kind (Type)
import Data.List
import Data.Maybe
import Data.Ord
import LeiosProtocol.Common
import LeiosProtocol.Config
import LeiosProtocol.Short hiding (Stage (..))
import qualified LeiosProtocol.Short as Short
import STMCompat

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

data LeiosGeneratorConfig m = LeiosGeneratorConfig
  { leios :: LeiosConfig
  , slotConfig :: SlotConfig
  , nodeId :: NodeId
  , buffers :: BuffersView m -- TODO: add SlotNo argument so expired blocks can be filtered out by the views.
  , schedule :: SlotNo -> m [(SomeRole, Word64)]
  , submit :: [(DiffTime, SomeAction)] -> m ()
  }

leiosBlockGenerator ::
  forall m.
  (MonadSTM m, MonadDelay m, MonadTime m) =>
  LeiosGeneratorConfig m ->
  m ()
leiosBlockGenerator LeiosGeneratorConfig{..} =
  blockGenerator $
    BlockGeneratorConfig
      { execute = \slot -> do
          roles <- lift $ schedule slot
          actions <- concat <$> mapM (execute slot) roles
          lift $ submit actions
      , slotConfig
      }
 where
  execute slot (SomeRole r, wins) = assert (wins >= 1) $ (map . second) (SomeAction r) <$> execute' slot r wins
  execute' :: SlotNo -> Role a -> Word64 -> StateT Int m [(DiffTime, a)]
  execute' slot Base _wins = do
    rbData <- lift $ atomically buffers.newRBData
    let meb = rbData.certifiedEBforRBAt slot
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
    referencedEBs <- case leios.variant of
      Short -> pure []
      Full -> do
        ebs <- lift $ atomically buffers.ebs
        let p = case leios of
              LeiosConfig{pipeline = _ :: SingPipeline p} ->
                pipelineOf @p leios Short.Endorse slot
        let chooseEB =
              fmap (.id)
                . listToMaybe
                . sortOn (Down . length . (.inputBlocks))
        pure $
          mapMaybe (chooseEB . snd) $
            endorseBlocksToReference leios p ebs (\_ _ -> True)
    let endorsedIBs = inputBlocksToEndorse leios slot ibs
    let !eb = mkEndorseBlock leios i slot nodeId referencedEBs endorsedIBs
    let !task = leios.delays.endorseBlockGeneration eb
    return [(task, eb)]
  execute' slot Vote votes = do
    votingFor <- lift $ atomically $ do
      ibs <- buffers.ibs
      ebs <- buffers.ebs
      pure $ endorseBlocksToVoteFor leios slotConfig slot ibs ebs
    i <- nextBlkId VoteId
    let voteMsg = mkVoteMsg leios i slot nodeId votes (map (.id) votingFor)
    let !task = leios.delays.voteMsgGeneration voteMsg votingFor
    return [(task, voteMsg)]
  nextBlkId :: (NodeId -> Int -> a) -> StateT Int m a
  nextBlkId f = do
    i <- get
    put $! i + 1
    return $ f nodeId i
