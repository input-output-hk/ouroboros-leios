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

import Numeric.Natural (Natural)

--------------------------------
--- Common types
--------------------------------

-- TODO
newtype Slot = Slot Natural
  deriving (Eq, Ord)
newtype BlockId = BlockId Natural
  deriving (Eq, Ord)
data BlockHeader
data BlockBody
type ChainTip = Point

blockHeaderParent :: BlockHeader -> Maybe Point
blockHeaderParent = undefined

-- TODO: Could points just be the slot?
data Point = Point
  { pointSlot :: Slot
  , pointBlockId :: BlockId
  }
  deriving (Eq, Ord)

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
