{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PraosProtocol.Common (
  AnchoredFragment,
  Chain,
  Blocks,
  headerPoint,
  blockPrevPoint,
  setFollowerPoint,
  module Block,
  module ConcreteBlock,
  module ProducerState,
  ReadOnly (..),
  readReadOnlyTVar,
  TakeOnly (..),
  takeTakeOnlyTMVar,
  tryTakeTakeOnlyTMVar,
  SlotConfig (..),
  slotTime,
  MessageSize (..),
  kilobytes,
  module TimeCompat,
) where

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (
    STM,
    TMVar,
    TVar,
    readTVar,
    takeTMVar,
    tryTakeTMVar
  ),
 )
import Control.Exception (assert)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Ouroboros.Network.Block as Block
import Ouroboros.Network.Mock.ConcreteBlock as ConcreteBlock
import Ouroboros.Network.Mock.ProducerState as ProducerState
import PraosProtocol.Common.AnchoredFragment (AnchoredFragment)
import PraosProtocol.Common.Chain (Chain, pointOnChain)

import ChanTCP (MessageSize (..))
import SimTCPLinks (kilobytes)
import TimeCompat

--------------------------------
--- Common types
--------------------------------

instance MessageSize BlockBody where
  messageSizeBytes _ = kilobytes 95

instance MessageSize BlockHeader where
  messageSizeBytes _ = kilobytes 1

-- TODO: Refactor to provide sizes for basic types.

instance MessageSize (Tip block) where
  messageSizeBytes _ = {- slot no -} 8 + {- hash -} 32 + {- block no -} 8

instance MessageSize (Point block) where
  messageSizeBytes _ = {- hash -} 32 + {- slot no -} 8

type Blocks = Map (HeaderHash Block) Block

headerPoint :: BlockHeader -> Point Block
headerPoint = castPoint . blockPoint

blockPrevPoint :: (HasFullHeader b, HeaderHash b ~ HeaderHash Block) => Blocks -> b -> Maybe (Point Block)
blockPrevPoint blks header = case blockPrevHash header of
  GenesisHash -> pure GenesisPoint
  BlockHash hash -> castPoint . blockPoint <$> Map.lookup hash blks

setFollowerPoint :: FollowerId -> Point Block -> ChainProducerState Block -> ChainProducerState Block
setFollowerPoint followerId point st@ChainProducerState{..} =
  assert (pointOnChain point chainState) $
    st{chainFollowers = Map.adjust setFollowerPoint' followerId chainFollowers}
 where
  setFollowerPoint' :: FollowerState Block -> FollowerState Block
  setFollowerPoint' followerState = followerState{followerPoint = point}

data SlotConfig = SlotConfig {start :: UTCTime, duration :: NominalDiffTime}

slotTime :: SlotConfig -> SlotNo -> UTCTime
slotTime SlotConfig{start, duration} sl = (fromIntegral (unSlotNo sl) * duration) `addUTCTime` start

--------------------------------
---- Common Utility Types
--------------------------------

-- | Readonly TVar.
newtype ReadOnly a = ReadOnly {unReadOnly :: a}

readReadOnlyTVar :: MonadSTM m => ReadOnly (TVar m a) -> STM m a
readReadOnlyTVar ReadOnly{unReadOnly} = readTVar unReadOnly

newtype TakeOnly a = TakeOnly {unTakeOnly :: a}

takeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m a
takeTakeOnlyTMVar TakeOnly{unTakeOnly} = takeTMVar unTakeOnly

tryTakeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m (Maybe a)
tryTakeTakeOnlyTMVar TakeOnly{unTakeOnly} = tryTakeTMVar unTakeOnly
