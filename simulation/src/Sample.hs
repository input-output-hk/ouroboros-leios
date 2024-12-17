module Sample where

import Data.List (foldl')
import System.IO (hFlush, stdout)
import TimeCompat
import VizSim

data SampleModel event state = SampleModel
  { initState :: state
  , accumState :: Time -> event -> state -> state
  , renderState :: state -> IO ()
  }

runSampleModel ::
  SampleModel event state ->
  Time ->
  [(Time, event)] ->
  IO ()
runSampleModel (SampleModel s0 accum render) stop = go . flip SimVizModel s0 . takeWhile (\(t, _) -> t <= stop)
 where
  go m = case stepSimViz 10000 m of
    m'@(SimVizModel ((now, _) : _) _) -> do
      putStrLn $ "time reached: " ++ show now
      hFlush stdout
      go m'
    (SimVizModel [] s) -> do
      putStrLn "done."
      render s
  stepSimViz n (SimVizModel es s) = case splitAt n es of
    (before, after) -> SimVizModel after (foldl' (\x (t, e) -> accum t e x) s before)
