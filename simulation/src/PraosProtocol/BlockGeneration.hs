{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module PraosProtocol.BlockGeneration where

import Cardano.Slotting.Slot (WithOrigin (..))
import Control.Monad.Trans
import Control.Tracer
import Data.ByteString as BS
import Data.ByteString.Char8 as BS8
import Data.Foldable (forM_)
import Data.Function (fix)
import PraosProtocol.Common
import qualified PraosProtocol.Common.Chain as Chain
import STMCompat
import System.Random (StdGen)

-- | Returns a block that can extend the chain.
--   PRECONDITION: the SlotNo is ahead of the chain tip.
mkBlock :: IsBody body => Chain (Block body) -> SlotNo -> body -> Block body
mkBlock c sl body = fixupBlock (Chain.headAnchor c) (mkPartialBlock sl body)

mkBody :: PraosConfig BlockBody -> ByteString -> SlotNo -> BlockBody
mkBody cfg prefix (SlotNo w) = fix $ \b ->
  BlockBody
    { bodyTag = BS.append prefix $ BS8.pack (show w)
    , bodyMessageSize = cfg.bodySize b
    }

praosBlockGenerator ::
  (IsBody body, MonadSTM m, MonadDelay m, MonadTime m, body ~ BlockBody) =>
  StdGen ->
  Tracer m (PraosNodeEvent body) ->
  PraosConfig body ->
  SlotConfig ->
  ByteString ->
  TVar m (ChainProducerState (Block body)) ->
  (Block body -> STM m ()) ->
  ((CPUTask, m ()) -> m ()) ->
  m ()
praosBlockGenerator rng tracer praosConfig slotConfig prefix cpsVar addBlockSt queue = do
  sched <- mkScheduler rng (const $ pure [((), Just $ \p -> if p <= praosConfig.blockFrequencyPerSlot then 1 else 0)])
  blockGenerator
    BlockGeneratorConfig{slotConfig, execute = execute sched, initial = 0 :: Int}
 where
  execute sched sl = lift $ do
    wins <- sched sl
    forM_ wins $ \_ -> do
      let body = mkBody praosConfig prefix sl
      let !delay = praosConfig.blockGenerationDelay $ mkPartialBlock sl body
      let !cpuTask = CPUTask delay "Block generation"
      curry queue cpuTask $ do
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
