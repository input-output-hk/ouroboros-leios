{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PackageImports #-}
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
  threadDelayNDT,
  UTCTime,
  NominalDiffTime,
  diffUTCTime,
  waitUntil,
  addUTCTime,
  seTimeCompat,
)
where

import Control.Monad (when)
import Control.Monad.IOSim (SimEvent)
import qualified Control.Monad.IOSim as IOSim (SimEvent (seTime))
import Data.Aeson.Types (FromJSON, ToJSON)
import Data.Coerce (coerce)
import Data.Fixed
import Data.Word (Word64)
import "io-classes" Control.Monad.Class.MonadTime (MonadMonotonicTimeNSec, MonadTime (getCurrentTime), NominalDiffTime, UTCTime, addUTCTime, diffUTCTime)
import qualified "io-classes" Control.Monad.Class.MonadTime as MonadTime (MonadMonotonicTimeNSec (getMonotonicTimeNSec))
import "io-classes" Control.Monad.Class.MonadTimer (MonadDelay)
import qualified "io-classes" Control.Monad.Class.MonadTimer as MonadTimer (MonadDelay (threadDelay))
import qualified "si-timers" Control.Monad.Class.MonadTime.SI as SI (DiffTime, Time (Time))

seTimeCompat :: SimEvent -> Time
seTimeCompat = Time . realToFrac @SI.DiffTime @DiffTime . coerce @SI.Time @SI.DiffTime . IOSim.seTime

newtype Nano = Nano Word64
  deriving stock (Show)
  deriving newtype (Eq, Ord, Num, Real, Enum, Integral)
  deriving newtype (ToJSON, FromJSON)

newtype Seconds = Seconds Double
  deriving stock (Show)
  deriving newtype (Eq, Ord, Num, Real, Enum, Fractional, RealFrac)
  deriving newtype (ToJSON, FromJSON)

newtype DiffTime = DiffTime Seconds
  deriving newtype (Eq, Ord, Num, Real, Enum, Fractional, RealFrac)
  deriving newtype (ToJSON, FromJSON)

instance Show DiffTime where
  show d = showFixed True (realToFrac d :: Pico) ++ "s"

newtype Time = Time DiffTime
  deriving newtype (Show, Eq, Ord)
  deriving newtype (ToJSON, FromJSON)

diffTimeToSeconds :: DiffTime -> Double
diffTimeToSeconds = coerce

secondsToDiffTime :: Double -> DiffTime
secondsToDiffTime = coerce

addTime :: DiffTime -> Time -> Time
addTime dt (Time t) = Time (dt + t)

diffTime :: Time -> Time -> DiffTime
diffTime (Time t1) (Time t2) = t1 - t2

threadDelay :: MonadDelay m => DiffTime -> m ()
threadDelay = MonadTimer.threadDelay . round . (* 1e6)

threadDelayNDT :: MonadDelay m => NominalDiffTime -> m ()
threadDelayNDT = MonadTimer.threadDelay . round . (* 1e6)

getMonotonicTime :: MonadMonotonicTimeNSec m => m Time
getMonotonicTime =
  Time . DiffTime . (* 1e-9) . fromIntegral . Nano <$> MonadTime.getMonotonicTimeNSec

waitUntil :: (MonadMonotonicTimeNSec m, MonadDelay m) => Time -> m ()
waitUntil endtime = do
  now <- getMonotonicTime
  let delay = endtime `diffTime` now
  when (delay > 0) (threadDelay delay)
