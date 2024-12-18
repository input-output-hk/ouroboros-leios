{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module LeiosProtocol.TaskMultiQueue where

import Control.Monad (forM, forM_, when)
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
writeTMQueue (TaskMultiQueue mq) lbl task = writeTBQueue (mq ! lbl) task

readTMQueue :: forall m l. (MonadSTM m, IsLabel l) => TaskMultiQueue l m -> l -> STM m (CPUTask, m ())
readTMQueue (TaskMultiQueue mq) lbl = readTBQueue (mq ! lbl)

flushTMQueue :: forall m l. (MonadSTM m, IsLabel l) => TaskMultiQueue l m -> STM m [(l, [(CPUTask, m ())])]
flushTMQueue (TaskMultiQueue mq) = forM (assocs mq) (\(l, q) -> (l,) <$> flushTBQueue q)

runInfParallelBlocking ::
  forall m l.
  (MonadSTM m, MonadDelay m, IsLabel l, MonadMonotonicTime m) =>
  Tracer m CPUTask ->
  TaskMultiQueue l m ->
  m ()
runInfParallelBlocking tracer mq = do
  xs <- atomically $ do
    xs <- concat . map snd <$> flushTMQueue mq
    when (null xs) retry
    return xs
  mapM_ (traceWith tracer . fst) xs
  now <- getMonotonicTime

  let tasksByEnd = Map.fromListWith (<>) [(addTime cpuTaskDuration now, [m]) | (CPUTask{..}, m) <- xs]

  forM_ (Map.toAscList tasksByEnd) $ \(end, ms) -> do
    waitUntil end
    sequence_ ms
