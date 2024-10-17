{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module PraosProtocol.Types (
  Blocks,
  headerPoint,
  blockPrevPoint,
  setFollowerPoint,
  module Block,
  module Chain,
  module ConcreteBlock,
  module ProducerState,
  ReadOnly (..),
  readReadOnlyTVar,
  TakeOnly (..),
  takeTakeOnlyTMVar,
  tryTakeTakeOnlyTMVar,
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
import Ouroboros.Network.Mock.Chain as Chain hiding (
  findFirstPoint,
 )
import Ouroboros.Network.Mock.ConcreteBlock as ConcreteBlock (
  Block (..),
  BlockBody,
  BlockHeader,
 )
import Ouroboros.Network.Mock.ProducerState as ProducerState hiding (
  addBlock,
  applyChainUpdate,
  applyChainUpdates,
  rollback,
 )

--------------------------------
--- Common types
--------------------------------

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

--------------------------------
---- Common Utility Types
--------------------------------

-- data OnChain = Yes | Unknown
-- data Blocking = Blocking | NonBlocking
-- deriving (Eq)
-- data Direction = Forward | Backward
-- deriving (Eq)

-- | Readonly TVar.
newtype ReadOnly a = ReadOnly {unReadOnly :: a}

readReadOnlyTVar :: MonadSTM m => ReadOnly (TVar m a) -> STM m a
readReadOnlyTVar ReadOnly{unReadOnly} = readTVar unReadOnly

newtype TakeOnly a = TakeOnly {unTakeOnly :: a}

takeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m a
takeTakeOnlyTMVar TakeOnly{unTakeOnly} = takeTMVar unTakeOnly

tryTakeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m (Maybe a)
tryTakeTakeOnlyTMVar TakeOnly{unTakeOnly} = tryTakeTMVar unTakeOnly
