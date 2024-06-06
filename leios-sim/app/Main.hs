module Main where

import Control.Concurrent.Class.MonadSTM (newTQueueIO, newTVarIO)
import Control.Monad.Class.MonadAsync (race_)
import Leios.Node (Params (..), runSimulation)
import Leios.Server (runServer)
import Leios.Trace (mkTracer)

main :: IO ()
main = do
  params <- newTVarIO baseParams
  events <- newTQueueIO
  runSimulation (mkTracer events) params
    `race_` runServer params events
 where
  baseParams =
    Params
      { λ = 12
      , capacity = 10
      , seed = 42
      , initialRound = 10
      }
