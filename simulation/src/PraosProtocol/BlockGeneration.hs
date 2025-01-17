{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module PraosProtocol.BlockGeneration where

import Cardano.Slotting.Slot (WithOrigin (..))
import Control.Monad (forever)
import Control.Tracer
import Data.ByteString as BS
import Data.ByteString.Char8 as BS8
import Data.Function (fix)
import Data.Word (Word64)
import PraosProtocol.Common
import qualified PraosProtocol.Common.Chain as Chain
import STMCompat
import System.Random (StdGen, uniformR)

-- | Returns a block that can extend the chain.
--   PRECONDITION: the SlotNo is ahead of the chain tip.
mkBlock :: IsBody body => Chain (Block body) -> SlotNo -> body -> Block body
mkBlock c sl body = fixupBlock (Chain.headAnchor c) (mkPartialBlock sl body)

type SlotGap = Word64

data PacketGenerationPattern
  = NoPacketGeneration
  | UniformGenerationPattern SlotGap
  | PoissonGenerationPattern StdGen Double

mkBody :: PraosConfig BlockBody -> ByteString -> SlotNo -> BlockBody
mkBody cfg prefix (SlotNo w) = fix $ \b ->
  BlockBody
    { bodyTag = BS.append prefix $ BS8.pack (show w)
    , bodyMessageSize = cfg.bodySize b
    }

mkNextBlock ::
  forall m.
  MonadSTM m =>
  PraosConfig BlockBody ->
  PacketGenerationPattern ->
  ByteString ->
  m (Maybe (m (SlotNo, BlockBody)))
mkNextBlock _cfg NoPacketGeneration _ = return Nothing
mkNextBlock cfg (UniformGenerationPattern gap) prefix = do
  stVar <- newTVarIO (SlotNo 0)
  let
    go = atomically $ do
      last_sl <- readTVar stVar
      let
        !sl = SlotNo (unSlotNo last_sl + gap :: Word64)
      writeTVar stVar sl
      let body = mkBody cfg prefix sl
      return (sl, body)
  return $ Just go
mkNextBlock cfg (PoissonGenerationPattern rng0 lambda) prefix = do
  stVar <- newTVarIO (SlotNo 0, rng0)
  let go = atomically $ do
        (last_sl, rng) <- readTVar stVar

        let (u, !rng') = uniformR (0, 1) rng
            gap = round ((-log u) * lambda :: Double) :: Word64

        let !sl' = SlotNo $ unSlotNo last_sl + gap
        writeTVar stVar (sl', rng')
        let body = mkBody cfg prefix sl'
        return (sl', body)
  return $ Just go

blockGenerator ::
  (IsBody body, MonadSTM m, MonadDelay m, MonadTime m) =>
  Tracer m (PraosNodeEvent body) ->
  PraosConfig body ->
  SlotConfig ->
  TVar m (ChainProducerState (Block body)) ->
  (Block body -> STM m ()) ->
  Maybe (m (SlotNo, body)) ->
  m ()
blockGenerator _tracer _praosConfig _ _cpsVar _addBlockSt Nothing = return ()
blockGenerator tracer praosConfig slotConfig cpsVar addBlockSt (Just nextBlock) = forever go
 where
  go = do
    (sl, body) <- nextBlock
    waitForSlot sl
    let !delay = praosConfig.blockGenerationDelay $ mkPartialBlock sl body
    traceWith tracer (PraosNodeEventCPU $ CPUTask delay "Block generation")
    mblk <- atomically $ do
      chain <- chainState <$> readTVar cpsVar
      let block = case mkBlock chain sl body of
            Block h b -> Block (h{headerMessageSize = praosConfig.headerSize}) b
      if Chain.headSlot chain <= At sl
        then addBlockSt block >> return (Just (block, chain))
        else return Nothing
    case mblk of
      Nothing -> return ()
      Just (blk, chain) -> do
        traceWith tracer (PraosNodeEventGenerate blk)
        traceWith tracer (PraosNodeEventNewTip (chain Chain.:> blk))
  waitForSlot sl = do
    let tgt = slotTime slotConfig sl
    now <- getCurrentTime
    threadDelayNDT (tgt `diffUTCTime` now)
