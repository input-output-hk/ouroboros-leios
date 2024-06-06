module Leios.Trace where

import Control.Concurrent.Class.MonadSTM (MonadSTM, TQueue, atomically, writeTQueue)
import Control.Tracer (Tracer (..), emit)
import Data.Aeson (ToJSON, Value, toJSON)

mkTracer :: (MonadSTM m, ToJSON a) => TQueue m Value -> Tracer m a
mkTracer events =
  Tracer $ emit (atomically . writeTQueue events . toJSON)
