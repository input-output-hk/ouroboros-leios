{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}

module TimeCompat (
  DiffTime,
  MonadTime (getCurrentTime),
  MonadDelay,
  MonadMonotonicTimeNSec,
  getMonotonicTime,
  Time (Time),
  diffTimeToSeconds,
  secondsToDiffTime,
  addTime,
  diffTime,
  threadDelay,
)
where

import Control.Exception (assert)
import Control.Monad.Class.MonadTime (MonadMonotonicTimeNSec, MonadTime (getCurrentTime))
import qualified Control.Monad.Class.MonadTime as MonadTime (MonadMonotonicTimeNSec (getMonotonicTimeNSec))
import Control.Monad.Class.MonadTimer (MonadDelay)
import qualified Control.Monad.Class.MonadTimer as MonadTimer (MonadDelay (threadDelay))
import Data.Aeson.Types (FromJSON, ToJSON)
import Data.Word (Word64)

newtype Nano = Nano Word64
  deriving stock (Show)
  deriving newtype (Eq, Ord, Num, Real, Enum, Integral)
  deriving newtype (ToJSON, FromJSON)

newtype DiffTime = DiffTime Nano
  deriving newtype (Show, Eq, Ord, Num, Real, Enum, Integral)
  deriving newtype (ToJSON, FromJSON)

newtype Time = Time DiffTime
  deriving newtype (Show, Eq, Ord)
  deriving newtype (ToJSON, FromJSON)

addTime :: DiffTime -> Time -> Time
addTime dt (Time t) = Time (dt + t)

diffTime :: Time -> Time -> DiffTime
diffTime (Time t1) (Time t2) = assert (t1 > t2) $ t1 - t2

diffTimeToSeconds :: DiffTime -> Double
diffTimeToSeconds (DiffTime dt) = (* 1e-9) . fromIntegral @Nano @Double $ dt

secondsToDiffTime :: Double -> DiffTime
secondsToDiffTime dt = DiffTime . round @Double @Nano $ dt * 1e9

threadDelay :: MonadDelay m => DiffTime -> m ()
threadDelay (DiffTime dt) = MonadTimer.threadDelay . round @Double @Int . (* 1e-3) . fromIntegral @Nano @Double $ dt

getMonotonicTime :: MonadMonotonicTimeNSec m => m DiffTime
getMonotonicTime = DiffTime . Nano <$> MonadTime.getMonotonicTimeNSec
