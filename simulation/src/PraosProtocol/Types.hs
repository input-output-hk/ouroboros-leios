{-# LANGUAGE NamedFieldPuns #-}

module PraosProtocol.Types (
  HeaderHash,
  Point,
  SlotNo,
  Tip,
  blockPrevPoint,
  ReadOnly,
  readReadOnlyTVar,
  TakeOnly,
  takeTakeOnlyTMVar,
  tryTakeTakeOnlyTMVar,
  module ConcreteBlock,
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
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Ouroboros.Network.Block as OAPI
import Ouroboros.Network.Mock.ConcreteBlock as ConcreteBlock (
  Block,
  BlockBody,
  BlockHeader,
 )

--------------------------------
--- Common types
--------------------------------

-- TODO
type HeaderHash = OAPI.HeaderHash ConcreteBlock.Block
type Point = OAPI.Point ConcreteBlock.Block
type SlotNo = OAPI.SlotNo
type Tip = OAPI.Tip

blockPrevPoint :: Map HeaderHash BlockHeader -> BlockHeader -> Maybe Point
blockPrevPoint headers header = case OAPI.blockPrevHash header of
  OAPI.GenesisHash -> pure OAPI.GenesisPoint
  OAPI.BlockHash hash -> OAPI.castPoint . OAPI.blockPoint <$> Map.lookup hash headers

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
