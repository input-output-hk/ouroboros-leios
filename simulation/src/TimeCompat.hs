{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NumericUnderscores #-}

module TimeCompat (
  -- Legacy interfact
  module Control.Monad.Class.MonadTime.SI,
  threadDelayNDT,
  threadDelaySI,
  MonadDelay,
  -- Int-as-Micros API
  Microseconds (..),
  threadDelayMS,
) where

import Control.Monad.Class.MonadTime.SI
import Control.Monad.Class.MonadTimer (MonadDelay (..))

newtype Microseconds = Microseconds {getMicroseconds :: Int}
  deriving newtype (Eq, Ord, Show, Enum, Num, Real, Integral)

threadDelayMS :: MonadDelay m => Microseconds -> m ()
threadDelayMS micros = threadDelay (getMicroseconds micros)

-- | Suspends the current thread for a given amount of time.
threadDelayNDT :: MonadDelay m => NominalDiffTime -> m ()
threadDelayNDT = threadDelay . round . (1_000_000 *)

-- | Suspends the current thread for a given amount of time.
threadDelaySI :: MonadDelay m => DiffTime -> m ()
threadDelaySI = threadDelay . round . (1_000_000 *)
