module Chan where

data Chan m a = Chan {
                  readChan  :: m a,
                  writeChan :: a -> m ()
                }
