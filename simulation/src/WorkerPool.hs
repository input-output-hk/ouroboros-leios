{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTSyntax #-}

module WorkerPool where

-- \| A simple simulation of a worker pool with either bounded or unbounded
-- CPU resources.
--
-- The intention is to use this where we need to model CPU resources being
-- used, such as validating network messages.
--
-- The idea is we (statically) have several sources of work (each modelled as
-- an STM action that either blocks or gives us a work item to do) and the
-- worker pool continuously pulls work from these sources and executes them.
--
-- In the unbounded CPU resource approach, each task is executed as soon as it
-- is made available from one of the sources.
--
-- In the bounded CPU resource approach, we run N threads to repeatedly grab
-- work and execute it. Thus there are at most N tasks executing concurrently
-- and the total task CPU throughput is N * time. In this approach, the order
-- of the sources is relevant: when there are multiple tasks available, new
-- tasks are

import Control.Monad
import Control.Monad.Class.MonadAsync
import Control.Monad.Class.MonadThrow
import STMCompat

data Task m where
  Task :: m a -> !(TMVar m (Either SomeException a)) -> Task m

type TaskSource m = STM m (Task m)

newBoundedWorkerPool ::
  (MonadAsync m, MonadCatch m, MonadSTM m) =>
  Int ->
  [TaskSource m] ->
  m ()
newBoundedWorkerPool n sources =
  replicateConcurrentlyOn_ n worker
 where
  worker = forever $ do
    Task task resultVar <- atomically $ foldr orElse retry sources
    result <- try task
    atomically $ writeTMVar resultVar result

replicateConcurrentlyOn_ :: (MonadThrow m, MonadAsync m) => Int -> m () -> m ()
replicateConcurrentlyOn_ n action =
  void $
    bracket
      (forM [0 .. n - 1] $ \i -> asyncOn i action)
      cancelMany
      waitAny

-- newUnboundedWorkerPool :: MonadSTM m => [STM m (m ())] -> m ()
-- newUnboundedWorkerPool _sources = undefined

cancelMany :: MonadAsync m => [Async m a] -> m ()
cancelMany as = do
  mapM_ cancel as
  mapM_ waitCatch as
