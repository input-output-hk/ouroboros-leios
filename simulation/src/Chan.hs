module Chan where

-- THIS IS A CHANGE

data Chan m a = Chan
  { readChan :: m a
  , writeChan :: a -> m ()
  }
