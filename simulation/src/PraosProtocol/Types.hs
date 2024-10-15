{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module PraosProtocol.Types (
  BlockBodies,
  BlockHeaders,
  blockPrevPoint,
  setFollowerPoint,
  module Block,
  module Chain,
  module ConcreteBlock,
  module ProducerState,
  ReadOnly,
  readReadOnlyTVar,
  TakeOnly,
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
import Ouroboros.Network.Block as Block (
  HeaderHash,
  Point,
  SlotNo,
  Tip,
 )
import qualified Ouroboros.Network.Block as OAPI
import Ouroboros.Network.Mock.Chain as Chain hiding (
  addBlock,
  applyChainUpdate,
  applyChainUpdates,
  findFirstPoint,
  rollback,
 )
import Ouroboros.Network.Mock.ConcreteBlock as ConcreteBlock (
  Block (..),
  BlockBody,
  BlockHeader,
 )
import Ouroboros.Network.Mock.ProducerState as ProducerState

--------------------------------
--- Common types
--------------------------------

type BlockHeaders = Map (HeaderHash Block) BlockHeader
type BlockBodies = Map (HeaderHash Block) BlockBody

blockPrevPoint :: BlockHeaders -> BlockHeader -> Maybe (Point Block)
blockPrevPoint headers header = case OAPI.blockPrevHash header of
  OAPI.GenesisHash -> pure OAPI.GenesisPoint
  OAPI.BlockHash hash -> OAPI.castPoint . OAPI.blockPoint <$> Map.lookup hash headers

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
