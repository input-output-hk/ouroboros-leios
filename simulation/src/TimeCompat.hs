{-# LANGUAGE NumericUnderscores #-}

module TimeCompat (
  module Control.Monad.Class.MonadTime.SI,
  threadDelayNDT,
  threadDelaySI,
  MonadDelay,
) where

import Control.Monad.Class.MonadTime.SI
import Control.Monad.Class.MonadTimer (MonadDelay (..))

-- | Suspends the current thread for a given amount of time.
threadDelayNDT :: MonadDelay m => NominalDiffTime -> m ()
threadDelayNDT = threadDelay . round . (1_000_000 *)

-- | Suspends the current thread for a given amount of time.
threadDelaySI :: MonadDelay m => DiffTime -> m ()
threadDelaySI = threadDelay . round . (1_000_000 *)
