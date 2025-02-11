module Chan.Core where

data Chan m a = Chan
  { readChan :: m a
  , writeChan :: a -> m ()
  }
