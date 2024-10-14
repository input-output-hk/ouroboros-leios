module PraosProtocol.Types where

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
import Ouroboros.Network.Mock.ConcreteBlock (
  Block (Block),
  BlockBody,
  BlockHeader,
 )

--------------------------------
--- Common types
--------------------------------

-- TODO
type BlockId = OAPI.HeaderHash Block
type Point = OAPI.Point Block
type Slot = OAPI.SlotNo
type ChainTip = Point

pointBlockId :: Point -> BlockId
pointBlockId = undefined

pointSlot :: Point -> Slot
pointSlot = undefined

blockPrevPoint :: Map BlockId BlockHeader -> BlockHeader -> Maybe Point
blockPrevPoint headers header = case OAPI.blockPrevHash header of
  OAPI.GenesisHash -> pure OAPI.GenesisPoint
  OAPI.BlockHash hash -> OAPI.castPoint . OAPI.blockPoint <$> Map.lookup hash headers

--------------------------------
---- Common Utility Types
--------------------------------

data OnChain = Yes | Unknown

data Blocking = Blocking | NonBlocking
  deriving (Eq)

data Direction = Forward | Backward
  deriving (Eq)

-- | Readonly TVar.
newtype ReadOnly a = ReadOnly {unReadOnly :: a}

readReadOnlyTVar :: MonadSTM m => ReadOnly (TVar m a) -> STM m a
readReadOnlyTVar = readTVar . unReadOnly

newtype TakeOnly a = TakeOnly {unTakeOnly :: a}

takeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m a
takeTakeOnlyTMVar = takeTMVar . unTakeOnly

tryTakeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m (Maybe a)
tryTakeTakeOnlyTMVar = tryTakeTMVar . unTakeOnly
