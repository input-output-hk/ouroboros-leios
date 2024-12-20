{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module LeiosProtocol.TaskMultiQueue where

import Control.Monad
import Control.Monad.Class.MonadFork (MonadFork (forkIO))
import Control.Tracer
import Data.Array
import qualified Data.Map.Strict as Map
import GHC.Natural
import LeiosProtocol.Common
import STMCompat

type IsLabel lbl = (Ix lbl, Bounded lbl)

newtype TaskMultiQueue lbl m = TaskMultiQueue (Array lbl (TBQueue m (CPUTask, m ())))

newTaskMultiQueue' :: (MonadSTM m, Ix l) => (l, l) -> Natural -> STM m (TaskMultiQueue l m)
newTaskMultiQueue' (a, b) n =
  TaskMultiQueue . listArray (a, b) <$> mapM (const $ newTBQueue n) (range (a, b))

newTaskMultiQueue :: (MonadSTM m, IsLabel l) => Natural -> STM m (TaskMultiQueue l m)
newTaskMultiQueue = newTaskMultiQueue' (minBound, maxBound)

writeTMQueue :: (MonadSTM m, IsLabel l) => TaskMultiQueue l m -> l -> (CPUTask, m ()) -> STM m ()
writeTMQueue (TaskMultiQueue mq) lbl = writeTBQueue (mq ! lbl)

readTMQueue :: forall m l. (MonadSTM m, IsLabel l) => TaskMultiQueue l m -> l -> STM m (CPUTask, m ())
readTMQueue (TaskMultiQueue mq) lbl = readTBQueue (mq ! lbl)

flushTMQueue :: forall m l. (MonadSTM m, IsLabel l) => TaskMultiQueue l m -> STM m [(l, [(CPUTask, m ())])]
flushTMQueue (TaskMultiQueue mq) = forM (assocs mq) (\(l, q) -> (l,) <$> flushTBQueue q)

runInfParallelBlocking ::
  forall m l.
  (MonadSTM m, MonadDelay m, IsLabel l, MonadMonotonicTimeNSec m, MonadFork m) =>
  Tracer m CPUTask ->
  TaskMultiQueue l m ->
  m ()
runInfParallelBlocking tracer mq = do
  xs <- atomically $ do
    xs <- concatMap snd <$> flushTMQueue mq
    when (null xs) retry
    return xs
  mapM_ (traceWith tracer . fst) xs
  now <- getMonotonicTime
  -- forking to do the waiting so we can go back to fetch more tasks.
  -- on the worst case this forks for each task, which might degrade sim performance.
  -- Andrea: a small experiment with short-leios-p2p-1 shows up to 16 tasks at once.
  --         OTOH only 14% of the time we had more than 1 task.
  void $ forkIO $ do
    let tasksByEnd = Map.fromListWith (<>) [(addTime cpuTaskDuration now, [m]) | (CPUTask{..}, m) <- xs]

    forM_ (Map.toAscList tasksByEnd) $ \(end, ms) -> do
      waitUntil end
      sequence_ ms
