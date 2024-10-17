{-# LANGUAGE NamedFieldPuns #-}

module PraosProtocol.BlockGeneration where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TVar,
    atomically,
    readTVar
  ),
 )
import Control.Monad (forever, when)
import Control.Monad.Class.MonadTimer.SI (MonadDelay)

import Cardano.Slotting.Slot (WithOrigin (..))
import Ouroboros.Network.Mock.ConcreteBlock (fixupBlock, mkPartialBlock)

import PraosProtocol.Types

-- | Returns a block that can extend the chain.
--   PRECONDITION: the SlotNo is ahead of the chain tip.
mkBlock :: Chain Block -> SlotNo -> BlockBody -> Block
mkBlock c sl body = fixupBlock (headAnchor c) (mkPartialBlock sl body)

blockGenerator ::
  (MonadSTM m, MonadDelay m, MonadTime m) =>
  SlotConfig ->
  TVar m (ChainProducerState Block) ->
  (Block -> STM m ()) ->
  m (SlotNo, BlockBody) ->
  m ()
blockGenerator slotConfig cpsVar addBlockSt nextBlock = forever $ go
 where
  go = do
    (sl, body) <- nextBlock
    waitForSlot sl
    atomically $ do
      chain <- chainState <$> readTVar cpsVar
      when (headSlot chain <= At sl) $
        addBlockSt (mkBlock chain sl body)
  waitForSlot sl = do
    let tgt = slotTime slotConfig sl
    now <- getCurrentTime
    threadDelayNDT (tgt `diffUTCTime` now)
