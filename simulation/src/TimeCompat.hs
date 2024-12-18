module TimeCompat (
  DiffTime,
  MonadTime (getCurrentTime),
  MonadDelay (threadDelay),
  MonadMonotonicTime (getMonotonicTime),
  Time (Time),
  UTCTime,
  NominalDiffTime,
  diffTimeToSeconds,
  addTime,
  addUTCTime,
  diffTime,
  diffUTCTime,
  threadDelaySI,
  threadDelayNDT,
)
where

import Control.Monad.Class.MonadTime.SI (
  DiffTime,
  MonadMonotonicTime (getMonotonicTime),
  MonadTime (getCurrentTime),
  NominalDiffTime,
  Time (..),
  UTCTime,
  addTime,
  addUTCTime,
  diffTime,
  diffUTCTime,
 )
import Control.Monad.Class.MonadTimer (MonadDelay (threadDelay))
import Data.Time.Clock (diffTimeToPicoseconds)

diffTimeToSeconds :: DiffTime -> Double
diffTimeToSeconds = (* 1e-12) . fromIntegral . diffTimeToPicoseconds

threadDelaySI :: MonadDelay m => DiffTime -> m ()
threadDelaySI = threadDelay . round . (* 1e6)

threadDelayNDT :: MonadDelay m => NominalDiffTime -> m ()
threadDelayNDT = threadDelay . round . (* 1e6)
