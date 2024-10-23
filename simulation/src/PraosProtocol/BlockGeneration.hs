{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module PraosProtocol.BlockGeneration where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (..),
 )
import Control.Monad (forever, when)
import Control.Monad.Class.MonadTimer.SI (MonadDelay)
import Data.ByteString as BS
import Data.ByteString.Char8 as BS8
import System.Random (StdGen, uniformR)

import Cardano.Slotting.Slot (WithOrigin (..))

import ChanTCP (Bytes)
import Data.Word (Word64)

import PraosProtocol.Common
import qualified PraosProtocol.Common.Chain as Chain

-- | Returns a block that can extend the chain.
--   PRECONDITION: the SlotNo is ahead of the chain tip.
mkBlock :: Chain Block -> SlotNo -> BlockBody -> Block
mkBlock c sl body = fixupBlock (Chain.headAnchor c) (mkPartialBlock sl body)

type SlotGap = Word64

data PacketGenerationPattern
  = NoPacketGeneration
  | UniformGenerationPattern Bytes SlotGap
  | PoissonGenerationPattern Bytes StdGen Double

mkBody :: Bytes -> ByteString -> SlotNo -> BlockBody
mkBody _sz prefix (SlotNo w) = BlockBody $ pad $ BS.append prefix $ BS8.pack (show w)
 where
  -- MessageSize for BlockBody is fixed, so we do not need padding.
  pad s = s

mkNextBlock ::
  forall m.
  MonadSTM m =>
  PacketGenerationPattern ->
  ByteString ->
  m (Maybe (m (SlotNo, BlockBody)))
mkNextBlock NoPacketGeneration _ = return Nothing
mkNextBlock (UniformGenerationPattern sz gap) prefix = do
  stVar <- newTVarIO (SlotNo 0)
  let
    go = atomically $ do
      last_sl <- readTVar stVar
      let
        !sl = SlotNo $ (unSlotNo last_sl + gap :: Word64)
      writeTVar stVar sl
      let body = mkBody sz prefix sl
      return (sl, body)
  return $ Just go
mkNextBlock (PoissonGenerationPattern sz rng0 lambda) prefix = do
  stVar <- newTVarIO (SlotNo 0, rng0)
  let go = atomically $ do
        (last_sl, rng) <- readTVar stVar

        let (u, !rng') = uniformR (0, 1) rng
            gap = round ((-log u) * lambda :: Double) :: Word64

        let !sl' = SlotNo $ unSlotNo last_sl + gap
        writeTVar stVar (sl', rng')
        let body = mkBody sz prefix sl'
        return (sl', body)
  return $ Just go

blockGenerator ::
  (MonadSTM m, MonadDelay m, MonadTime m) =>
  SlotConfig ->
  TVar m (ChainProducerState Block) ->
  (Block -> STM m ()) ->
  Maybe (m (SlotNo, BlockBody)) ->
  m ()
blockGenerator _slotConfig _cpsVar _addBlockSt Nothing = return ()
blockGenerator slotConfig cpsVar addBlockSt (Just nextBlock) = forever $ go
 where
  go = do
    (sl, body) <- nextBlock
    waitForSlot sl
    atomically $ do
      chain <- chainState <$> readTVar cpsVar
      when (Chain.headSlot chain <= At sl) $
        addBlockSt (mkBlock chain sl body)
  waitForSlot sl = do
    let tgt = slotTime slotConfig sl
    now <- getCurrentTime
    threadDelayNDT (tgt `diffUTCTime` now)

slotConfigFromNow :: MonadTime m => m SlotConfig
slotConfigFromNow = do
  start <- getCurrentTime
  return $ SlotConfig{start, duration = 1}
