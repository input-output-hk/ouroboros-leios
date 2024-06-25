module Main where

import Control.Concurrent.Class.MonadSTM (newTQueueIO, newTVarIO)
import Control.Monad.Class.MonadAsync (race_)
import Leios.Server (runServer)
import Leios.Trace (mkTracer)

-- FIXME: import explicitly
import Leios.Model
import qualified Leios.Model as Model

main :: IO ()
main = do
  params <- newTVarIO defaultParams
  events <- newTQueueIO
  Model.run (mkTracer events) params
   `race_` runServer params events
 where
   defaultParams =
        Parameters
          { _L = NumberOfSlots 4
          , λ = NumberOfSlices 3
          , nodeBandwidth = BitsPerSecond 1000
          , ibSize = NumberOfBits 300
          , f_I = error "this needs to be properly defined still"
          , f_E = error "this needs to be properly defined still"
          }
