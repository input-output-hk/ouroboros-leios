{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module PraosProtocol.BlockGeneration where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TVar,
    atomically,
    newTVar,
    readTVar,
    writeTVar
  ),
 )
import Control.Monad (forever, when)
import Control.Monad.Class.MonadTimer.SI (MonadDelay)
import Data.ByteString as BS
import System.Random (StdGen, uniformR)

import Cardano.Slotting.Slot (WithOrigin (..))
import Codec.Serialise
import Ouroboros.Network.Mock.ConcreteBlock (BlockBody (..), fixupBlock, mkPartialBlock)

import ChanTCP (Bytes)
import Data.Word (Word64)
import PraosProtocol.Types

-- | Returns a block that can extend the chain.
--   PRECONDITION: the SlotNo is ahead of the chain tip.
mkBlock :: Chain Block -> SlotNo -> BlockBody -> Block
mkBlock c sl body = fixupBlock (headAnchor c) (mkPartialBlock sl body)

type SlotGap = Word64

data PacketGenerationPattern
  = NoPacketGeneration
  | UniformGenerationPattern Bytes SlotGap
  | PoissonGenerationPattern Bytes StdGen Double

mkBody :: Bytes -> ByteString -> SlotNo -> BlockBody
mkBody sz prefix (SlotNo w) = BlockBody $ pad $ BS.append prefix $ BS.toStrict (serialise w)
 where
  pad s = BS.append s (BS.replicate (fromIntegral sz - BS.length s) 0)

mkNextBlock ::
  forall m.
  MonadSTM m =>
  PacketGenerationPattern ->
  ByteString ->
  m (Maybe (m (SlotNo, BlockBody)))
mkNextBlock NoPacketGeneration _ = return Nothing
mkNextBlock (UniformGenerationPattern sz gap) prefix = do
  stVar <- atomically $ newTVar (SlotNo 0)
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
  stVar <- atomically $ newTVar (SlotNo 0, rng0)
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
  (Maybe (m (SlotNo, BlockBody))) ->
  m ()
blockGenerator _slotConfig _cpsVar _addBlockSt Nothing = return ()
blockGenerator slotConfig cpsVar addBlockSt (Just nextBlock) = forever $ go
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
