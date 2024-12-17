{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module STMUtils (
  ReadOnly,
  asReadOnly,
  readReadOnlyTVar,
  readReadOnlyTVarIO,
  TakeOnly,
  asTakeOnly,
  takeTakeOnlyTMVar,
  tryTakeTakeOnlyTMVar,
) where

import Control.Concurrent.Class.MonadSTM (MonadSTM (..))

--------------------------------
---- Common Utility Types
--------------------------------

-- | Readonly TVar.
newtype ReadOnly a = ReadOnly {unReadOnly :: a}

asReadOnly :: a -> ReadOnly a
asReadOnly = ReadOnly

readReadOnlyTVar :: MonadSTM m => ReadOnly (TVar m a) -> STM m a
readReadOnlyTVar ReadOnly{unReadOnly} = readTVar unReadOnly

readReadOnlyTVarIO :: MonadSTM m => ReadOnly (TVar m a) -> m a
readReadOnlyTVarIO ReadOnly{unReadOnly} = readTVarIO unReadOnly

newtype TakeOnly a = TakeOnly {unTakeOnly :: a}

asTakeOnly :: a -> TakeOnly a
asTakeOnly = TakeOnly

takeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m a
takeTakeOnlyTMVar TakeOnly{unTakeOnly} = takeTMVar unTakeOnly

tryTakeTakeOnlyTMVar :: MonadSTM m => TakeOnly (TMVar m a) -> STM m (Maybe a)
tryTakeTakeOnlyTMVar TakeOnly{unTakeOnly} = tryTakeTMVar unTakeOnly
